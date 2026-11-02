module

public import EthLib.EVM.Proofs.Runner
public import EthLib.EVM.Proofs.Frame.Environment

/-! A bounded program reads all five immutable message fields. -/

@[expose] public section
namespace EthLib.EVM.Runner.EnvironmentProgram

/-- ADDRESS, ORIGIN, CALLER, CALLVALUE, GASPRICE, STOP. -/
def program : ByteArray := ⟨#[0x30, 0x32, 0x33, 0x34, 0x3a, 0x00]⟩

/-- The program reads arbitrary metadata and leaves the residual frame intact. -/
theorem run (context : CallData.Context) (returnData : ByteArray) (xs : List Word)
    (room : xs.length ≤ 1019) (g : Nat) (mem : Memory.Allocation.State)
    (valid : Memory.Allocation.Valid mem) :
    ∃ t, Runner.run 6 ⟨program, 0, ⟨xs, by omega⟩, 10 + g, mem, valid, context, returnData⟩ = .stopped t ∧
      t.pc = 6 ∧ t.gas = g ∧ t.code = program ∧ t.memory = mem ∧
      t.context = context ∧ t.returnData = returnData ∧
      t.stack.val = context.environment.gasPrice :: context.environment.value ::
        Environment.addressWord context.environment.caller ::
        Environment.addressWord context.environment.origin ::
        Environment.addressWord context.environment.currentTarget :: xs := by
  let s : Frame.State := ⟨program, 0, ⟨xs, by omega⟩, 10 + g, mem, valid, context, returnData⟩
  let s1 : Frame.State := { s with pc := 1, gas := 8 + g, stack := ⟨Environment.addressWord context.environment.currentTarget :: xs, by simp; omega⟩ }
  let s2 : Frame.State := { s with pc := 2, gas := 6 + g, stack := ⟨Environment.addressWord context.environment.origin :: Environment.addressWord context.environment.currentTarget :: xs, by simp; omega⟩ }
  let s3 : Frame.State := { s with pc := 3, gas := 4 + g, stack := ⟨Environment.addressWord context.environment.caller :: Environment.addressWord context.environment.origin :: Environment.addressWord context.environment.currentTarget :: xs, by simp; omega⟩ }
  let s4 : Frame.State := { s with pc := 4, gas := 2 + g, stack := ⟨context.environment.value :: Environment.addressWord context.environment.caller :: Environment.addressWord context.environment.origin :: Environment.addressWord context.environment.currentTarget :: xs, by simp; omega⟩ }
  let s5 : Frame.State := { s with pc := 5, gas := g, stack := ⟨context.environment.gasPrice :: context.environment.value :: Environment.addressWord context.environment.caller :: Environment.addressWord context.environment.origin :: Environment.addressWord context.environment.currentTarget :: xs, by simp; omega⟩ }
  let s6 : Frame.State := { s5 with pc := 6 }
  have h1 : Frame.Rule s (.continue s1) := by
    apply Frame.Rule.observation s s1 .address
    · simp [Frame.At, Frame.Observation.opcode, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s]; omega
    · simp [s]; omega
    · simp [Frame.Advances, Frame.Observation.value, Environment.addressWord, s, s1]; omega
  have h2 : Frame.Rule s1 (.continue s2) := by
    apply Frame.Rule.observation s1 s2 .origin
    · simp [Frame.At, Frame.Observation.opcode, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s1]; omega
    · simp [s1]; omega
    · simp [Frame.Advances, Frame.Observation.value, Environment.addressWord, s1, s2, s]; omega
  have h3 : Frame.Rule s2 (.continue s3) := by
    apply Frame.Rule.observation s2 s3 .caller
    · simp [Frame.At, Frame.Observation.opcode, s2, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s2]; omega
    · simp [s2]; omega
    · simp [Frame.Advances, Frame.Observation.value, Environment.addressWord, s2, s3, s]; omega
  have h4 : Frame.Rule s3 (.continue s4) := by
    apply Frame.Rule.observation s3 s4 .callvalue
    · simp [Frame.At, Frame.Observation.opcode, s3, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s3]; omega
    · simp [s3]; omega
    · simp [Frame.Advances, Frame.Observation.value, Environment.addressWord, s3, s4, s]; omega
  have h5 : Frame.Rule s4 (.continue s5) := by
    apply Frame.Rule.observation s4 s5 .gasprice
    · simp [Frame.At, Frame.Observation.opcode, s4, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s4]
    · simp [s4]; omega
    · simp [Frame.Advances, Frame.Observation.value, Environment.addressWord, s4, s5, s]
  have h6 : Frame.Rule s5 (.stop s6) := by
    apply Frame.Rule.stop
    simp [Frame.At, s5, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
  have trace : Runner.Terminates s 6 (.stopped s6) :=
    .next h1 (.next h2 (.next h3 (.next h4 (.next h5 (.stop h6)))))
  have result := Runner.run_of_terminates trace 0
  refine ⟨s6, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simpa [s] using result

end EthLib.EVM.Runner.EnvironmentProgram
