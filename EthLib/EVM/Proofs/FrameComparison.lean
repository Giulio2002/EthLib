module

public import EthLib.EVM.Proofs.Frame
public import EthLib.EVM.Proofs.Word.Comparisons
public import EthLib.EVM.Proofs.Word.Bitwise
public import EthLib.EVM.Proofs.Word.Shifts
public import EthLib.EVM.Proofs.Word.ByteSignExtend

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

/-- The SHL transition and its numeric result. -/
theorem step_shl_numeric (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .shl)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.shl x y :: xs)) :
    step s = .continue t ∧ ((Word.shl x y).toNat =
      if x.toNat < 256 then (y.toNat * 2 ^ x.toNat) % (2 ^ 256) else 0) :=
  ⟨step_shl s t x y xs at_ items gas fields, Proofs.Word.Shifts.shl_refines x y⟩

/-- The SHR transition and its numeric result. -/
theorem step_shr_numeric (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .shr)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.shr x y :: xs)) :
    step s = .continue t ∧ ((Word.shr x y).toNat =
      if x.toNat < 256 then y.toNat / 2 ^ x.toNat else 0) :=
  ⟨step_shr s t x y xs at_ items gas fields, Proofs.Word.Shifts.shr_refines x y⟩

/-- The SAR transition and its numeric result. -/
theorem step_sar_numeric (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .sar)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.sar x y :: xs)) :
    step s = .continue t ∧ (Word.signed (Word.sar x y) =
      if x.toNat < 256 then Word.signed y / (2 ^ x.toNat : Int)
      else if Word.signed y < 0 then -1 else 0) :=
  ⟨step_sar s t x y xs at_ items gas fields, Proofs.Word.Shifts.sar_refines x y⟩

/-- The BYTE transition and its numeric result. -/
theorem step_byte_numeric (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .byte)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.byte x y :: xs)) :
    step s = .continue t ∧ ((Word.byte x y).toNat = Proofs.Word.ByteSignExtend.Reference.byte x.toNat y.toNat) :=
  ⟨step_byte s t x y xs at_ items gas fields, Proofs.Word.ByteSignExtend.byte_refines x y⟩

/-- The SIGNEXTEND transition and its numeric result. -/
theorem step_signextend_numeric (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .signextend)) (items : s.stack.val = x :: y :: xs) (gas : 5 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 5) (Word.signextend x y :: xs)) :
    step s = .continue t ∧ ((Word.signextend x y).toNat = Proofs.Word.ByteSignExtend.Reference.signextend x.toNat y.toNat) :=
  ⟨step_signextend s t x y xs at_ items gas fields, Proofs.Word.ByteSignExtend.signextend_refines x y⟩

/-- BYTE produces one big-endian byte, or zero beyond the word. -/
theorem step_byte_bounds (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .byte)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.byte x y :: xs)) :
    step s = .continue t ∧ (Word.byte x y).toNat < 256 ∧
      (32 ≤ x.toNat → Word.byte x y = 0) :=
  ⟨step_byte s t x y xs at_ items gas fields, Proofs.Word.ByteSignExtend.byte_lt x y,
    Proofs.Word.ByteSignExtend.byte_out_of_range x y⟩

/-- SIGNEXTEND copies the selected sign bit to every upper bit. -/
theorem step_signextend_bits (s t : State) (x y : Word) (xs : List Word) (k : Nat)
    (at_ : At s (some .signextend)) (items : s.stack.val = x :: y :: xs) (gas : 5 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 5) (Word.signextend x y :: xs))
    (h : x.toNat < 32) (hk : 8 * (x.toNat + 1) ≤ k) (hk256 : k < 256) :
    step s = .continue t ∧
      (Word.signextend x y).getLsbD k = y.getLsbD (8 * (x.toNat + 1) - 1) :=
  ⟨step_signextend s t x y xs at_ items gas fields,
    Proofs.Word.ByteSignExtend.signextend_upper_bit x y h k hk hk256⟩

/-- Large SIGNEXTEND indices leave the input word unchanged. -/
theorem step_signextend_large (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .signextend)) (items : s.stack.val = x :: y :: xs) (gas : 5 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 5) (Word.signextend x y :: xs))
    (h : 32 ≤ x.toNat) : step s = .continue t ∧ Word.signextend x y = y :=
  ⟨step_signextend s t x y xs at_ items gas fields,
    Proofs.Word.ByteSignExtend.signextend_out_of_range x y h⟩

/-- Selecting all bytes leaves the input word unchanged. -/
theorem step_signextend_31 (s t : State) (y : Word) (xs : List Word)
    (at_ : At s (some .signextend)) (items : s.stack.val = 31 :: y :: xs) (gas : 5 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 5) (Word.signextend 31 y :: xs)) :
    step s = .continue t ∧ Word.signextend 31 y = y :=
  ⟨step_signextend s t 31 y xs at_ items gas fields,
    Proofs.Word.ByteSignExtend.signextend_31 y⟩

end EthLib.EVM.Frame
