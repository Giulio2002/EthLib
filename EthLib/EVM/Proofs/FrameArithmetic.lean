module

public import EthLib.EVM.Proofs.Frame
public import EthLib.EVM.Proofs.Word.DivMod
public import EthLib.EVM.Proofs.Word.SignedDivMod

/-!
# Arithmetic frame refinements

The transition rules use first-popped operands first.
The numeric equations compose those rules with the word contracts.
-/

@[expose] public section
namespace EthLib.EVM.Frame

/-- The MUL transition and its numeric result. -/
theorem step_mul_numeric (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .mul)) (items : s.stack.val = x :: y :: xs) (gas : 5 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 5) (Word.mul x y :: xs)) :
    step s = .continue t ∧ (Word.mul x y).toNat = (x.toNat * y.toNat) % Word.modulus :=
  ⟨step_mul s t x y xs at_ items gas fields, Proofs.Word.toNat_mul x y⟩

/-- The SUB transition and its numeric result. -/
theorem step_sub_numeric (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .sub)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.sub x y :: xs)) :
    step s = .continue t ∧ ((Word.sub x y).toNat : Int) = ((x.toNat : Int) - (y.toNat : Int)) % (Word.modulus : Int) :=
  ⟨step_sub s t x y xs at_ items gas fields, Proofs.Word.toNat_sub_int x y⟩

/-- The DIV transition and its numeric result. -/
theorem step_div_numeric (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .div)) (items : s.stack.val = x :: y :: xs) (gas : 5 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 5) (Word.div x y :: xs)) :
    step s = .continue t ∧ (Word.div x y).toNat = if y.toNat = 0 then 0 else x.toNat / y.toNat :=
  ⟨step_div s t x y xs at_ items gas fields, Proofs.Word.toNat_div x y⟩

/-- The MOD transition and its numeric result. -/
theorem step_mod_numeric (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .mod)) (items : s.stack.val = x :: y :: xs) (gas : 5 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 5) (Word.mod x y :: xs)) :
    step s = .continue t ∧ (Word.mod x y).toNat = if y.toNat = 0 then 0 else x.toNat % y.toNat :=
  ⟨step_mod s t x y xs at_ items gas fields, Proofs.Word.toNat_mod x y⟩

/-- The SDIV transition and its numeric result. -/
theorem step_sdiv_numeric (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .sdiv)) (items : s.stack.val = x :: y :: xs) (gas : 5 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 5) (Word.sdiv x y :: xs)) :
    step s = .continue t ∧ Word.signed (Word.sdiv x y) = (Proofs.Word.SignedDivMod.Reference.quotient (Word.signed x) (Word.signed y)).bmod (2 ^ 256) :=
  ⟨step_sdiv s t x y xs at_ items gas fields, Proofs.Word.SignedDivMod.sdiv_refines x y⟩

/-- The SMOD transition and its numeric result. -/
theorem step_smod_numeric (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .smod)) (items : s.stack.val = x :: y :: xs) (gas : 5 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 5) (Word.smod x y :: xs)) :
    step s = .continue t ∧ Word.signed (Word.smod x y) = Proofs.Word.SignedDivMod.Reference.remainder (Word.signed x) (Word.signed y) :=
  ⟨step_smod s t x y xs at_ items gas fields, Proofs.Word.SignedDivMod.smod_refines x y⟩

end EthLib.EVM.Frame
