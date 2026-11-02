module

public import EthLib.EVM.Proofs.Frame
public import EthLib.EVM.Proofs.Opcode
public import EthLib.EVM.Proofs.PushImmediate
public import EthLib.EVM.Proofs.Word

/-!
# Frame and primitive reference contracts

These lemmas compose the frame rules with the independent opcode table and
numeric contracts already proved for PUSH data and word addition.
-/

@[expose] public section
namespace EthLib.EVM.Frame

/-- Instruction lookup agrees with the independently listed opcode table. -/
theorem at_reference (s : State) (op : Option Opcode) : At s op ↔
    ∃ h : s.pc < s.code.size, Proofs.Opcode.reference.lookup s.code[s.pc] = op := by
  simp only [At, Proofs.Opcode.decode_reference]

/-- A successful PUSH also has the proved big-endian numeric value. -/
theorem push_numeric (s t : State) (n : Fin 33) (h : At s (some (.push n)))
    (gas : (if n.val = 0 then 2 else 3) ≤ s.gas) (room : s.stack.val.length < 1024)
    (fields : Advances s t (PushImmediate.nextPC s.pc n)
      (s.gas - (if n.val = 0 then 2 else 3))
      (PushImmediate.value s.code s.pc n :: s.stack.val)) :
    step s = .continue t ∧
      (PushImmediate.value s.code s.pc n).toNat =
        (PushImmediate.bytes s.code s.pc n).foldl (fun k b => 256 * k + b.toNat) 0 :=
  ⟨step_push s t n h gas room fields, Proofs.PushImmediate.value_numeric _ _ _⟩

/-- A successful ADD also has the proved modular arithmetic result. -/
theorem add_numeric (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .add)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.add x y :: xs)) :
    step s = .continue t ∧
      (Word.add x y).toNat = (x.toNat + y.toNat) % Word.modulus :=
  ⟨step_add s t x y xs h items gas fields, Proofs.Word.toNat_add _ _⟩

end EthLib.EVM.Frame
