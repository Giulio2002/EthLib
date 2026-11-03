module

public import EthLib.EVM.Word.Exp
public import EthLib.EVM.Proofs.Word
public import EthLib.Execution.Proofs.Precompiles.Modexp.PowMod

/-!
# EXP result contracts

The reference is natural exponentiation followed by reduction.
The executable helper uses the separately verified modular algorithm.
-/

@[expose] public section

namespace EthLib.EVM.Proofs.Word

open EthLib.EVM
open EthLib.EVM.Word

/-- EXP agrees with the natural-number result for all word operands. -/
theorem toNat_exp (base exponent : Word) :
    (exp base exponent).toNat = base.toNat ^ exponent.toNat % modulus := by
  simp only [exp, BitVec.toNat_ofNat, EthLib.Execution.Precompiles.Modexp.powMod_eq, modulus, Nat.mod_mod]

namespace Reference

/-- The mathematical EXP result on bounded natural numbers. -/
def exp (base exponent : Value) : Value :=
  ⟨base.val ^ exponent.val % (2 ^ 256), Nat.mod_lt _ (by decide)⟩

end Reference

/-- The executable result refines the bounded natural reference. -/
theorem exp_refines (base exponent : Word) :
    decode (exp base exponent) = Reference.exp (decode base) (decode exponent) := by
  apply Subtype.ext
  exact toNat_exp base exponent

/-- EXP always returns a word in range. -/
theorem exp_lt (base exponent : Word) : (exp base exponent).toNat < modulus :=
  toNat_lt _

/-- Every base to exponent zero, including zero, gives one. -/
theorem exp_zero (base : Word) : exp base 0 = 1 := by
  apply BitVec.eq_of_toNat_eq
  simp [toNat_exp, modulus]

/-- Exponent one preserves the base. -/
theorem exp_one (base : Word) : exp base 1 = base := by
  apply BitVec.eq_of_toNat_eq
  simpa [toNat_exp] using Nat.mod_eq_of_lt (toNat_lt base)

/-- One to any exponent is one. -/
theorem one_exp (exponent : Word) : exp 1 exponent = 1 := by
  apply BitVec.eq_of_toNat_eq
  simp [toNat_exp, modulus]

/-- Zero to a nonzero exponent is zero. -/
theorem zero_exp (exponent : Word) (h : exponent ≠ 0) : exp 0 exponent = 0 := by
  apply BitVec.eq_of_toNat_eq
  have hn : exponent.toNat ≠ 0 := by
    intro he
    apply h
    apply BitVec.eq_of_toNat_eq
    simpa using he
  simp [toNat_exp, Nat.zero_pow (Nat.pos_of_ne_zero hn)]

/-- Adding exponents without word overflow multiplies the two results. -/
theorem exp_add (base a b : Word) (h : a.toNat + b.toNat < modulus) :
    (exp base (Word.add a b)).toNat =
      ((exp base a).toNat * (exp base b).toNat) % modulus := by
  rw [toNat_exp, add_no_wrap a b h, Nat.pow_add, toNat_exp, toNat_exp, Nat.mod_mul_mod]
  simp [Nat.mul_mod]

/-- The number of nonzero exponent calls in the modular algorithm. -/
def expSteps (e : Nat) : Nat :=
  if e = 0 then 0 else 1 + expSteps (e / 2)
termination_by e
decreasing_by omega

/-- An exponent below `2^bits` takes at most `bits` squaring steps. -/
theorem expSteps_le (bits e : Nat) (h : e < 2 ^ bits) : expSteps e ≤ bits := by
  induction bits generalizing e with
  | zero =>
    have : e = 0 := by simpa using h
    subst e
    simp [expSteps]
  | succ bits ih =>
    by_cases hz : e = 0
    · subst e
      simp [expSteps]
    · have hh : e / 2 < 2 ^ bits := by
        rw [Nat.pow_succ] at h
        omega
      rw [expSteps, ite_eq_right hz]
      have := ih (e / 2) hh
      omega

/-- A word exponent takes at most 256 squaring steps. -/
theorem expSteps_word (exponent : Word) : expSteps exponent.toNat ≤ 256 :=
  expSteps_le 256 exponent.toNat (toNat_lt exponent)

end EthLib.EVM.Proofs.Word
