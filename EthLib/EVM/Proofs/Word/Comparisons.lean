module

public import EthLib.EVM.Word.Comparisons

/-!
# Comparison result contracts

The equations refine each word result to a natural or integer predicate.
Correspondence with the cited sources is an interpretation.
-/

@[expose] public section

namespace EthLib.EVM.Proofs.Word.Comparisons

open EthLib.EVM

/-- The exact LT result for every pair of operands. -/
theorem lt_equation (a b : Word) : Word.ltResult a b =
    (if a.toNat < b.toNat then 1 else 0) := rfl

/-- LT returns exactly zero or one. -/
theorem lt_range (a b : Word) : Word.ltResult a b = 0 ∨ Word.ltResult a b = 1 := by
  unfold Word.ltResult
  split <;> simp

/-- LT returns one exactly when its predicate holds. -/
theorem lt_one_iff (a b : Word) : Word.ltResult a b = 1 ↔ a.toNat < b.toNat := by
  simp [Word.ltResult]

/-- LT returns zero exactly when its predicate fails. -/
theorem lt_zero_iff (a b : Word) : Word.ltResult a b = 0 ↔ ¬ (a.toNat < b.toNat) := by
  simp [Word.ltResult]

/-- The exact GT result for every pair of operands. -/
theorem gt_equation (a b : Word) : Word.gtResult a b =
    (if b.toNat < a.toNat then 1 else 0) := rfl

/-- GT returns exactly zero or one. -/
theorem gt_range (a b : Word) : Word.gtResult a b = 0 ∨ Word.gtResult a b = 1 := by
  unfold Word.gtResult
  split <;> simp

/-- GT returns one exactly when its predicate holds. -/
theorem gt_one_iff (a b : Word) : Word.gtResult a b = 1 ↔ b.toNat < a.toNat := by
  simp [Word.gtResult]

/-- GT returns zero exactly when its predicate fails. -/
theorem gt_zero_iff (a b : Word) : Word.gtResult a b = 0 ↔ ¬ (b.toNat < a.toNat) := by
  simp [Word.gtResult]

/-- The exact SLT result for every pair of operands. -/
theorem slt_equation (a b : Word) : Word.sltResult a b =
    (if Word.signed a < Word.signed b then 1 else 0) := rfl

/-- SLT returns exactly zero or one. -/
theorem slt_range (a b : Word) : Word.sltResult a b = 0 ∨ Word.sltResult a b = 1 := by
  unfold Word.sltResult
  split <;> simp

/-- SLT returns one exactly when its predicate holds. -/
theorem slt_one_iff (a b : Word) : Word.sltResult a b = 1 ↔ Word.signed a < Word.signed b := by
  simp [Word.sltResult]

/-- SLT returns zero exactly when its predicate fails. -/
theorem slt_zero_iff (a b : Word) : Word.sltResult a b = 0 ↔ ¬ (Word.signed a < Word.signed b) := by
  simp [Word.sltResult]

/-- The exact SGT result for every pair of operands. -/
theorem sgt_equation (a b : Word) : Word.sgtResult a b =
    (if Word.signed b < Word.signed a then 1 else 0) := rfl

/-- SGT returns exactly zero or one. -/
theorem sgt_range (a b : Word) : Word.sgtResult a b = 0 ∨ Word.sgtResult a b = 1 := by
  unfold Word.sgtResult
  split <;> simp

/-- SGT returns one exactly when its predicate holds. -/
theorem sgt_one_iff (a b : Word) : Word.sgtResult a b = 1 ↔ Word.signed b < Word.signed a := by
  simp [Word.sgtResult]

/-- SGT returns zero exactly when its predicate fails. -/
theorem sgt_zero_iff (a b : Word) : Word.sgtResult a b = 0 ↔ ¬ (Word.signed b < Word.signed a) := by
  simp [Word.sgtResult]

/-- The exact EQ result for every pair of operands. -/
theorem eq_equation (a b : Word) : Word.eqResult a b =
    (if a = b then 1 else 0) := rfl

/-- EQ returns exactly zero or one. -/
theorem eq_range (a b : Word) : Word.eqResult a b = 0 ∨ Word.eqResult a b = 1 := by
  unfold Word.eqResult
  split <;> simp

/-- EQ returns one exactly when its predicate holds. -/
theorem eq_one_iff (a b : Word) : Word.eqResult a b = 1 ↔ a = b := by
  simp [Word.eqResult]

/-- EQ returns zero exactly when its predicate fails. -/
theorem eq_zero_iff (a b : Word) : Word.eqResult a b = 0 ↔ ¬ (a = b) := by
  simp [Word.eqResult]

/-- The exact ISZERO result for every operand. -/
theorem iszero_equation (a : Word) : Word.iszeroResult a =
    (if a = 0 then 1 else 0) := rfl

/-- ISZERO returns exactly zero or one. -/
theorem iszero_range (a : Word) : Word.iszeroResult a = 0 ∨ Word.iszeroResult a = 1 := by
  unfold Word.iszeroResult
  split <;> simp

/-- ISZERO returns one exactly for zero. -/
theorem iszero_one_iff (a : Word) : Word.iszeroResult a = 1 ↔ a = 0 := by
  simp [Word.iszeroResult]

/-- ISZERO returns zero exactly for a nonzero word. -/
theorem iszero_zero_iff (a : Word) : Word.iszeroResult a = 0 ↔ a ≠ 0 := by
  simp [Word.iszeroResult]

/-- Reversing operands exchanges unsigned LT and GT. -/
theorem gt_reverse (a b : Word) : Word.gtResult a b = Word.ltResult b a := rfl

/-- Reversing operands exchanges signed LT and GT. -/
theorem sgt_reverse (a b : Word) : Word.sgtResult a b = Word.sltResult b a := rfl

/-- Equality is symmetric. -/
theorem eq_symmetric (a b : Word) : Word.eqResult a b = Word.eqResult b a := by
  simp [Word.eqResult, eq_comm]

/-- ISZERO is equality with zero. -/
theorem iszero_eq (a : Word) : Word.iszeroResult a = Word.eqResult a 0 := rfl

/-- Negating LT gives the mathematical non-strict opposite comparison. -/
theorem not_lt (a b : Word) : Word.iszeroResult (Word.ltResult a b) =
    (if b.toNat ≤ a.toNat then 1 else 0) := by
  simp [Word.iszeroResult, Word.ltResult, Nat.not_lt]

/-- Negating signed LT gives the mathematical non-strict opposite comparison. -/
theorem not_slt (a b : Word) : Word.iszeroResult (Word.sltResult a b) =
    (if Word.signed b ≤ Word.signed a then 1 else 0) := by
  simp [Word.iszeroResult, Word.sltResult, Int.not_lt]

/-- Equality agrees with equality of unsigned observations. -/
theorem eq_nat_iff (a b : Word) : Word.eqResult a b = 1 ↔ a.toNat = b.toNat := by
  rw [eq_one_iff]
  exact ⟨fun h => congrArg BitVec.toNat h, BitVec.eq_of_toNat_eq⟩

/-- Zero testing agrees with the unsigned observation. -/
theorem iszero_nat_iff (a : Word) : Word.iszeroResult a = 1 ↔ a.toNat = 0 := by
  rw [iszero_one_iff]
  constructor
  · intro h; subst a; rfl
  · intro h; apply BitVec.eq_of_toNat_eq; simpa using h

/-- Equal operands compare equal. -/
theorem example_equal : Word.eqResult 7 7 = 1 := by decide

/-- Operand order affects unsigned comparison. -/
theorem example_order : Word.ltResult 1 2 = 1 ∧ Word.ltResult 2 1 = 0 := by decide

/-- The signed minimum is below the signed maximum. -/
theorem example_signed_extremes :
    Word.sltResult (BitVec.intMin 256) (BitVec.intMax 256) = 1 := by decide

/-- The sign boundary reverses unsigned order. -/
theorem example_sign_boundary :
    Word.sltResult (BitVec.intMin 256) 0 = 1 ∧ Word.ltResult (BitVec.intMin 256) 0 = 0 := by decide

end EthLib.EVM.Proofs.Word.Comparisons
