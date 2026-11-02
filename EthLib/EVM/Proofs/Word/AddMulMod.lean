module

public import EthLib.EVM.Word.AddMulMod
public import EthLib.EVM.Proofs.Word

/-! Kernel-checked arithmetic contracts for ADDMOD and MULMOD results. -/

@[expose] public section

namespace EthLib.EVM.Proofs.Word.AddMulMod

open EthLib.EVM
open EthLib.EVM.Word

namespace Reference

/-- The source equation on natural numbers, independent of word representation. -/
def addmod (a b m : Nat) : Nat := if m = 0 then 0 else (a + b) % m

/-- The source equation on natural numbers, independent of word representation. -/
def mulmod (a b m : Nat) : Nat := if m = 0 then 0 else (a * b) % m

end Reference

/-- The full sum is reduced by the third operand before word representation. -/
theorem toNat_addmod (a b m : Word) :
    (addmod a b m).toNat = Reference.addmod a.toNat b.toNat m.toNat := by
  by_cases h : m.toNat = 0
  · simp [addmod, Reference.addmod, h]
  · simp only [addmod, Reference.addmod, h, ite_false, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero h)) m.isLt)

/-- The full product is reduced by the third operand before word representation. -/
theorem toNat_mulmod (a b m : Word) :
    (mulmod a b m).toNat = Reference.mulmod a.toNat b.toNat m.toNat := by
  by_cases h : m.toNat = 0
  · simp [mulmod, Reference.mulmod, h]
  · simp only [mulmod, Reference.mulmod, h, ite_false, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero h)) m.isLt)

/-- Zero modulus produces zero. -/
theorem addmod_zero_modulus (a b : Word) : addmod a b 0 = 0 := by
  simp [addmod]

/-- Zero modulus produces zero. -/
theorem mulmod_zero_modulus (a b : Word) : mulmod a b 0 = 0 := by
  simp [mulmod]

/-- A nonzero modulus bounds the result strictly. -/
theorem addmod_lt (a b m : Word) (h : m.toNat ≠ 0) :
    (addmod a b m).toNat < m.toNat := by
  rw [toNat_addmod]
  simp only [Reference.addmod, h, ite_false]
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

/-- A nonzero modulus bounds the result strictly. -/
theorem mulmod_lt (a b m : Word) (h : m.toNat ≠ 0) :
    (mulmod a b m).toNat < m.toNat := by
  rw [toNat_mulmod]
  simp only [Reference.mulmod, h, ite_false]
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

/-- The decoded word agrees with the independent natural-number model. -/
theorem addmod_refines (a b m : Word) :
    (decode (addmod a b m)).val = Reference.addmod a.toNat b.toNat m.toNat :=
  toNat_addmod a b m

/-- The decoded word agrees with the independent natural-number model. -/
theorem mulmod_refines (a b m : Word) :
    (decode (mulmod a b m)).val = Reference.mulmod a.toNat b.toNat m.toNat :=
  toNat_mulmod a b m

/-- Addition is commutative before reduction. -/
theorem addmod_comm (a b m : Word) : addmod a b m = addmod b a m := by
  apply BitVec.eq_of_toNat_eq
  simp [toNat_addmod, Reference.addmod, Nat.add_comm]

/-- Multiplication is commutative before reduction. -/
theorem mulmod_comm (a b m : Word) : mulmod a b m = mulmod b a m := by
  apply BitVec.eq_of_toNat_eq
  simp [toNat_mulmod, Reference.mulmod, Nat.mul_comm]

/-- Adding zero gives the operand reduced by the modulus. -/
theorem addmod_zero (a m : Word) :
    (addmod a 0 m).toNat = if m.toNat = 0 then 0 else a.toNat % m.toNat := by
  simp [toNat_addmod, Reference.addmod]

/-- Multiplication by zero gives zero. -/
theorem mulmod_zero (a m : Word) : mulmod a 0 m = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [toNat_mulmod, Reference.mulmod]

/-- Multiplication by one gives the operand reduced by the modulus. -/
theorem mulmod_one (a m : Word) :
    (mulmod a 1 m).toNat = if m.toNat = 0 then 0 else a.toNat % m.toNat := by
  simp [toNat_mulmod, Reference.mulmod]

/-- Reducing both summands first preserves the full-precision result. -/
theorem addmod_reduce (a b m : Word) (h : m.toNat ≠ 0) :
    (addmod a b m).toNat = (a.toNat % m.toNat + b.toNat % m.toNat) % m.toNat := by
  rw [toNat_addmod]
  simp only [Reference.addmod, h, ite_false]
  exact Nat.add_mod _ _ _

/-- Reducing both factors first preserves the full-precision result. -/
theorem mulmod_reduce (a b m : Word) (h : m.toNat ≠ 0) :
    (mulmod a b m).toNat = (a.toNat % m.toNat * (b.toNat % m.toNat)) % m.toNat := by
  rw [toNat_mulmod]
  simp only [Reference.mulmod, h, ite_false]
  exact Nat.mul_mod _ _ _

/-- The largest word plus one retains the carry before reduction. -/
theorem addmod_overflow :
    addmod (BitVec.ofNatLT (modulus - 1) (by decide)) 1
      (BitVec.ofNatLT (modulus - 1) (by decide)) = 1 := by decide

/-- Doubling the largest word keeps the high bit before reduction. -/
theorem mulmod_overflow :
    mulmod (BitVec.ofNatLT (modulus - 1) (by decide)) 2
      (BitVec.ofNatLT (modulus - 1) (by decide)) = 0 ∧
    ((modulus - 1) * 2 % modulus) % (modulus - 1) ≠ 0 := by decide

/-- Modulus one always gives zero. -/
theorem addmod_one_modulus (a b : Word) : addmod a b 1 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [toNat_addmod, Reference.addmod, Nat.mod_one]

/-- Modulus one always gives zero. -/
theorem mulmod_one_modulus (a b : Word) : mulmod a b 1 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [toNat_mulmod, Reference.mulmod, Nat.mod_one]

/-- The largest operands reduce to zero under the largest modulus. -/
theorem max_operands_max_modulus :
    addmod (BitVec.ofNatLT (modulus - 1) (by decide))
      (BitVec.ofNatLT (modulus - 1) (by decide))
      (BitVec.ofNatLT (modulus - 1) (by decide)) = 0 ∧
    mulmod (BitVec.ofNatLT (modulus - 1) (by decide))
      (BitVec.ofNatLT (modulus - 1) (by decide))
      (BitVec.ofNatLT (modulus - 1) (by decide)) = 0 := by decide

end EthLib.EVM.Proofs.Word.AddMulMod
