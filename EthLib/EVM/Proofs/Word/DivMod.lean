module

public import EthLib.EVM.Word.DivMod
public import EthLib.EVM.Proofs.Word

/-! Unsigned DIV and MOD result contracts, independent of instruction execution. -/

@[expose] public section

namespace EthLib.EVM.Proofs.Word

open EthLib.EVM
open EthLib.EVM.Word

/-- The quotient equals the specified natural equation for every divisor. -/
theorem toNat_div (n d : Word) :
    (Word.div n d).toNat = if d.toNat = 0 then 0 else n.toNat / d.toNat := by
  by_cases h : d.toNat = 0
  · simp [Word.div, h]
  · simp only [Word.div, h, ite_false, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (toNat_lt n))

/-- The remainder equals the specified natural equation for every divisor. -/
theorem toNat_mod (n d : Word) :
    (Word.mod n d).toNat = if d.toNat = 0 then 0 else n.toNat % d.toNat := by
  by_cases h : d.toNat = 0
  · simp [Word.mod, h]
  · simp only [Word.mod, h, ite_false, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) (toNat_lt n))

namespace Reference

/-- The Yellow Paper quotient on bounded natural values. -/
def div (n d : Value) : Value :=
  if h : d.val = 0 then ⟨0, by decide⟩
  else ⟨n.val / d.val, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) n.property⟩

/-- The Yellow Paper remainder on bounded natural values. -/
def mod (n d : Value) : Value :=
  if h : d.val = 0 then ⟨0, by decide⟩
  else ⟨n.val % d.val, Nat.lt_of_le_of_lt (Nat.mod_le _ _) n.property⟩

end Reference

/-- Concrete quotient refines the bounded-natural model, including zero. -/
theorem div_refines (n d : Word) :
    decode (Word.div n d) = Reference.div (decode n) (decode d) := by
  apply Subtype.ext
  by_cases h : d.toNat = 0
  · simpa [Reference.div, decode, h] using toNat_div n d
  · simpa [Reference.div, decode, h] using toNat_div n d

/-- Concrete remainder refines the bounded-natural model, including zero. -/
theorem mod_refines (n d : Word) :
    decode (Word.mod n d) = Reference.mod (decode n) (decode d) := by
  apply Subtype.ext
  by_cases h : d.toNat = 0
  · simpa [Reference.mod, decode, h] using toNat_mod n d
  · simpa [Reference.mod, decode, h] using toNat_mod n d

/-- Quotients are in the word range. -/
theorem div_lt (n d : Word) : (Word.div n d).toNat < modulus := toNat_lt _

/-- Remainders are in the word range. -/
theorem mod_lt (n d : Word) : (Word.mod n d).toNat < modulus := toNat_lt _

/-- A nonzero divisor strictly bounds the remainder. -/
theorem mod_lt_divisor (n d : Word) (h : d.toNat ≠ 0) :
    (Word.mod n d).toNat < d.toNat := by
  rw [toNat_mod, ite_eq_right h]
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

/-- For a nonzero divisor, quotient and remainder reconstruct the numerator. -/
theorem div_mod_decomposition (n d : Word) (h : d.toNat ≠ 0) :
    (Word.div n d).toNat * d.toNat + (Word.mod n d).toNat = n.toNat := by
  rw [toNat_div, toNat_mod, ite_eq_right h, ite_eq_right h]
  simpa [Nat.mul_comm] using Nat.div_add_mod n.toNat d.toNat

/-- Division by zero returns zero. -/
theorem div_zero (n : Word) : Word.div n 0 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [toNat_div]

/-- Remainder by zero returns zero. -/
theorem mod_zero (n : Word) : Word.mod n 0 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [toNat_mod]

/-- Division by one leaves the numerator unchanged. -/
theorem div_one (n : Word) : Word.div n 1 = n := by
  apply BitVec.eq_of_toNat_eq
  simp [toNat_div]

/-- Remainder by one is zero. -/
theorem mod_one (n : Word) : Word.mod n 1 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [toNat_mod, Nat.mod_one]

/-- A numerator smaller than a nonzero divisor has zero quotient. -/
theorem div_eq_zero_of_lt (n d : Word) (h : n.toNat < d.toNat) :
    Word.div n d = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_div, ite_eq_right (Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le _) h))]
  simp [Nat.div_eq_of_lt h]

/-- A numerator smaller than a nonzero divisor is its own remainder. -/
theorem mod_eq_self_of_lt (n d : Word) (h : n.toNat < d.toNat) :
    Word.mod n d = n := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_mod, ite_eq_right (Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le _) h))]
  exact Nat.mod_eq_of_lt h

end EthLib.EVM.Proofs.Word
