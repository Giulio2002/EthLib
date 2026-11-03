module

public import EthLib.EVM.Proofs.Runner
public import EthLib.EVM.Proofs.Frame.Environment

/-! SLOTNUM and NUMBER observe independently supplied block metadata. -/

@[expose] public section
namespace EthLib.EVM.Runner.SlotNumber

/-- SLOTNUM, NUMBER, and STOP. -/
def program : ByteArray := ⟨#[0x4b, 0x43, 0x00]⟩

/-- The observations preserve the entire supplied frame context. -/
theorem run (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State) (warmAddresses : List World.Address) (warmSlots : List (World.Address × Word)) (static : Bool) (stateGas : Frame.StateGas) (xs : List Word)
    (room : xs.length ≤ 1022) (g : Nat) (mem : Memory.Allocation.State)
    (valid : Memory.Allocation.Valid mem) :
    ∃ t, Runner.run 3 ⟨program, 0, ⟨xs, by omega⟩, 4 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots, static, stateGas⟩ = .stopped t ∧
      t.pc = 3 ∧ t.gas = g ∧ t.code = program ∧ t.memory = mem ∧
      t.context = context ∧ t.returnData = returnData ∧
      t.stack.val = context.environment.number :: BitVec.ofNat 256 context.environment.slotNumber.val :: xs := by
  let s : Frame.State := ⟨program, 0, ⟨xs, by omega⟩, 4 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots, static, stateGas⟩
  let s1 : Frame.State := { s with pc := 1, gas := 2 + g, stack := ⟨BitVec.ofNat 256 context.environment.slotNumber.val :: xs, by simp; omega⟩ }
  let s2 : Frame.State := { s with pc := 2, gas := g, stack := ⟨context.environment.number :: BitVec.ofNat 256 context.environment.slotNumber.val :: xs, by simp; omega⟩ }
  let s3 : Frame.State := { s2 with pc := 3 }
  have h1 : Frame.Rule s (.continue s1) := by
    apply Frame.Rule.observation s s1 .slotnum
    · simp [Frame.At, Frame.Observation.opcode, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s]; omega
    · simp [s]; omega
    · simp [Frame.Advances, Frame.Observation.value, s, s1]; omega
  have h2 : Frame.Rule s1 (.continue s2) := by
    apply Frame.Rule.observation s1 s2 .number
    · simp [Frame.At, Frame.Observation.opcode, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s1]
    · simp [s1]; omega
    · simp [Frame.Advances, Frame.Observation.value, s1, s2, s]
  have h3 : Frame.Rule s2 (.stop s3) := by
    apply Frame.Rule.stop
    simp [Frame.At, s2, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
  have trace : Runner.Terminates s 3 (.stopped s3) := .next h1 (.next h2 (.stop h3))
  have result := Runner.run_of_terminates trace 0
  refine ⟨s3, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simpa [s] using result

end EthLib.EVM.Runner.SlotNumber
