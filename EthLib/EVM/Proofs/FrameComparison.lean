module

public import EthLib.EVM.Proofs.Frame
public import EthLib.EVM.Proofs.Word.Comparisons
public import EthLib.EVM.Proofs.Word.Bitwise

/-! # Comparison and bitwise frame refinements

The first popped word is the left operand.
These theorems compose the frame transition with the word contracts.
-/

@[expose] public section
namespace EthLib.EVM.Frame

/-- The LT transition and its Boolean result. -/
theorem step_lt_boolean (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .lt)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.ltResult x y :: xs)) :
    step s = .continue t ∧ (Word.ltResult x y = 1 ↔ x.toNat < y.toNat) :=
  ⟨step_lt s t x y xs at_ items gas fields, Proofs.Word.Comparisons.lt_one_iff x y⟩

/-- The GT transition and its Boolean result. -/
theorem step_gt_boolean (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .gt)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.gtResult x y :: xs)) :
    step s = .continue t ∧ (Word.gtResult x y = 1 ↔ y.toNat < x.toNat) :=
  ⟨step_gt s t x y xs at_ items gas fields, Proofs.Word.Comparisons.gt_one_iff x y⟩

/-- The SLT transition and its Boolean result. -/
theorem step_slt_boolean (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .slt)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.sltResult x y :: xs)) :
    step s = .continue t ∧ (Word.sltResult x y = 1 ↔ Word.signed x < Word.signed y) :=
  ⟨step_slt s t x y xs at_ items gas fields, Proofs.Word.Comparisons.slt_one_iff x y⟩

/-- The SGT transition and its Boolean result. -/
theorem step_sgt_boolean (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .sgt)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.sgtResult x y :: xs)) :
    step s = .continue t ∧ (Word.sgtResult x y = 1 ↔ Word.signed y < Word.signed x) :=
  ⟨step_sgt s t x y xs at_ items gas fields, Proofs.Word.Comparisons.sgt_one_iff x y⟩

/-- The EQ transition and its Boolean result. -/
theorem step_eq_boolean (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .eq)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.eqResult x y :: xs)) :
    step s = .continue t ∧ (Word.eqResult x y = 1 ↔ x = y) :=
  ⟨step_eq s t x y xs at_ items gas fields, Proofs.Word.Comparisons.eq_one_iff x y⟩

/-- The ISZERO transition and its Boolean result. -/
theorem step_iszero_boolean (s t : State) (x : Word) (xs : List Word)
    (at_ : At s (some .iszero)) (items : s.stack.val = x :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.iszeroResult x :: xs)) :
    step s = .continue t ∧ (Word.iszeroResult x = 1 ↔ x = 0) :=
  ⟨step_iszero s t x xs at_ items gas fields, Proofs.Word.Comparisons.iszero_one_iff x⟩

/-- The AND transition and its natural-number bitwise result. -/
theorem step_and_numeric (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .and)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.bitwiseAnd x y :: xs)) :
    step s = .continue t ∧ (Word.bitwiseAnd x y).toNat = x.toNat &&& y.toNat :=
  ⟨step_and s t x y xs at_ items gas fields, Proofs.Word.Bitwise.and_nat x y⟩

/-- The OR transition and its natural-number bitwise result. -/
theorem step_or_numeric (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .or)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.bitwiseOr x y :: xs)) :
    step s = .continue t ∧ (Word.bitwiseOr x y).toNat = x.toNat ||| y.toNat :=
  ⟨step_or s t x y xs at_ items gas fields, Proofs.Word.Bitwise.or_nat x y⟩

/-- The XOR transition and its natural-number bitwise result. -/
theorem step_xor_numeric (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .xor)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.bitwiseXor x y :: xs)) :
    step s = .continue t ∧ (Word.bitwiseXor x y).toNat = x.toNat ^^^ y.toNat :=
  ⟨step_xor s t x y xs at_ items gas fields, Proofs.Word.Bitwise.xor_nat x y⟩

/-- The NOT transition and its full-width numeric complement. -/
theorem step_not_numeric (s t : State) (x : Word) (xs : List Word)
    (at_ : At s (some .not)) (items : s.stack.val = x :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.bitwiseNot x :: xs)) :
    step s = .continue t ∧ (Word.bitwiseNot x).toNat = Word.modulus - 1 - x.toNat :=
  ⟨step_not s t x xs at_ items gas fields, Proofs.Word.Bitwise.not_nat x⟩

end EthLib.EVM.Frame
