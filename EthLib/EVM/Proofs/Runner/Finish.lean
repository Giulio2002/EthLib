module

public import EthLib.EVM.Proofs.Runner
public import EthLib.EVM.Proofs.Frame.Finish

@[expose] public section
namespace EthLib.EVM.Runner.FinishProgram

/-- PC followed by RETURN or REVERT. -/
def program : Frame.FinishKind → ByteArray
  | .return_ => ⟨#[0x58, 0xf3]⟩
  | .revert_ => ⟨#[0x58, 0xfd]⟩

/-- The actual runner executes PC and then returns the selected memory bytes. -/
theorem run (s : Frame.State) (kind : Frame.FinishKind) (length : Word) (xs : List Word)
    (room : xs.length ≤ 1022) (extraGas : Nat) :
    let cost := Gas.rangeCost s.memory.words 0 length.toNat
    let initial : Frame.State := { s with code := program kind, pc := 0, gas := 2 + cost + extraGas, stack := ⟨length :: xs, by simp; omega⟩ }
    let output : ByteArray := ⟨(Memory.readRange s.memory.store 0 length.toNat).toArray⟩
    ∃ t, (match kind with
      | .return_ => Runner.run 2 initial = .returned t output
      | .revert_ => Runner.run 2 initial = .reverted t extraGas output) ∧
      t.gas = extraGas ∧ t.pc = 1 ∧ t.stack.val = xs ∧ t.logs = s.logs ∧
      Frame.FinishBytes s 0 length output := by
  let cost := Gas.rangeCost s.memory.words 0 length.toNat
  let initial : Frame.State := { s with code := program kind, pc := 0, gas := 2 + cost + extraGas, stack := ⟨length :: xs, by simp; omega⟩ }
  let stack : Stack := ⟨0 :: length :: xs, by simp; omega⟩
  let tail : Stack := ⟨xs, by omega⟩
  let mid : Frame.State := { initial with pc := 1, gas := cost + extraGas, stack }
  let terminal : Frame.State := { mid with gas := extraGas, stack := tail, memory := Memory.Allocation.expand s.memory 0 length.toNat, memoryValid := Memory.Allocation.expand_valid_for_frame _ _ _ s.memoryValid }
  let output : ByteArray := ⟨(Memory.readRange s.memory.store 0 length.toNat).toArray⟩
  have first : Frame.Rule initial (.continue mid) := by
    apply Frame.Rule.observation initial mid .pc
    · cases kind <;> simp [Frame.At, Frame.Observation.opcode, initial, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [initial, cost] <;> omega
    · simp [initial]; omega
    · simp [Frame.Advances, Frame.Observation.value, mid, initial, stack, cost]; omega
  have last : match kind with
      | .return_ => Frame.Rule mid (.returned terminal output)
      | .revert_ => Frame.Rule mid (.revert terminal extraGas output) := by
    cases kind with
    | return_ =>
      apply Frame.Rule.finishReturn mid terminal (⟨length :: xs, by simp; omega⟩) tail 0 length
      · simp [Frame.At, mid, initial, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
      · rfl
      · rfl
      · simp [mid, initial, cost]
      · simp [Frame.AdvancesMemory, terminal, mid, initial, tail, cost]
    | revert_ =>
      apply Frame.Rule.finishRevert mid terminal (⟨length :: xs, by simp; omega⟩) tail 0 length
      · simp [Frame.At, mid, initial, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
      · rfl
      · rfl
      · simp [mid, initial, cost]
      · simp [Frame.AdvancesMemory, terminal, mid, initial, tail, cost]
  refine ⟨terminal, ?_, rfl, rfl, rfl, rfl, Frame.finish_bytes s 0 length⟩
  cases kind with
  | return_ =>
    have trace : Runner.Terminates initial 2 (.returned terminal output) := .next first (.returned last)
    simpa [initial] using Runner.run_of_terminates trace 0
  | revert_ =>
    have trace : Runner.Terminates initial 2 (.reverted terminal extraGas output) := .next first (.reverted last)
    simpa [initial] using Runner.run_of_terminates trace 0

end EthLib.EVM.Runner.FinishProgram
