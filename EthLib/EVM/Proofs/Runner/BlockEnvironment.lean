module

public import EthLib.EVM.Proofs.Runner
public import EthLib.EVM.Proofs.Frame.Environment

/-! A program observes the supplied block and chain metadata. -/

@[expose] public section
namespace EthLib.EVM.Runner.BlockEnvironmentProgram

/-- The seven block observations followed by STOP. -/
def program : ByteArray := ⟨#[0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x48, 0x00]⟩

/-- The program observes arbitrary accepted metadata and preserves the frame. -/
theorem run (context : CallData.Context) (returnData : ByteArray) (xs : List Word)
    (room : xs.length ≤ 1017) (g : Nat) (mem : Memory.Allocation.State)
    (valid : Memory.Allocation.Valid mem) :
    ∃ t, Runner.run 8 ⟨program, 0, ⟨xs, by omega⟩, 14 + g, mem, valid, context, returnData⟩ = .stopped t ∧
      t.pc = 8 ∧ t.gas = g ∧ t.code = program ∧ t.memory = mem ∧
      t.context = context ∧ t.returnData = returnData ∧
      t.stack.val = context.environment.baseFee :: BitVec.ofNat 256 context.environment.chainId.val :: context.environment.gasLimit :: context.environment.prevRandao :: context.environment.number :: context.environment.timestamp :: Environment.addressWord context.environment.coinbase :: xs := by
  let s : Frame.State := ⟨program, 0, ⟨xs, by omega⟩, 14 + g, mem, valid, context, returnData⟩
  let s1 : Frame.State := { s with pc := 1, gas := 12 + g, stack := ⟨Environment.addressWord context.environment.coinbase :: xs, by simp; omega⟩ }
  let s2 : Frame.State := { s with pc := 2, gas := 10 + g, stack := ⟨context.environment.timestamp :: Environment.addressWord context.environment.coinbase :: xs, by simp; omega⟩ }
  let s3 : Frame.State := { s with pc := 3, gas := 8 + g, stack := ⟨context.environment.number :: context.environment.timestamp :: Environment.addressWord context.environment.coinbase :: xs, by simp; omega⟩ }
  let s4 : Frame.State := { s with pc := 4, gas := 6 + g, stack := ⟨context.environment.prevRandao :: context.environment.number :: context.environment.timestamp :: Environment.addressWord context.environment.coinbase :: xs, by simp; omega⟩ }
  let s5 : Frame.State := { s with pc := 5, gas := 4 + g, stack := ⟨context.environment.gasLimit :: context.environment.prevRandao :: context.environment.number :: context.environment.timestamp :: Environment.addressWord context.environment.coinbase :: xs, by simp; omega⟩ }
  let s6 : Frame.State := { s with pc := 6, gas := 2 + g, stack := ⟨BitVec.ofNat 256 context.environment.chainId.val :: context.environment.gasLimit :: context.environment.prevRandao :: context.environment.number :: context.environment.timestamp :: Environment.addressWord context.environment.coinbase :: xs, by simp; omega⟩ }
  let s7 : Frame.State := { s with pc := 7, gas := g, stack := ⟨context.environment.baseFee :: BitVec.ofNat 256 context.environment.chainId.val :: context.environment.gasLimit :: context.environment.prevRandao :: context.environment.number :: context.environment.timestamp :: Environment.addressWord context.environment.coinbase :: xs, by simp; omega⟩ }
  let s8 : Frame.State := { s7 with pc := 8 }
  have h1 : Frame.Rule s (.continue s1) := by
    apply Frame.Rule.observation s s1 .coinbase
    · simp [Frame.At, Frame.Observation.opcode, s, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s]; omega
    · simp [s]; omega
    · simp [Frame.Advances, Frame.Observation.value, Environment.addressWord, s, s1, s]; omega
  have h2 : Frame.Rule s1 (.continue s2) := by
    apply Frame.Rule.observation s1 s2 .timestamp
    · simp [Frame.At, Frame.Observation.opcode, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s1]; omega
    · simp [s1]; omega
    · simp [Frame.Advances, Frame.Observation.value, Environment.addressWord, s1, s2, s]; omega
  have h3 : Frame.Rule s2 (.continue s3) := by
    apply Frame.Rule.observation s2 s3 .number
    · simp [Frame.At, Frame.Observation.opcode, s2, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s2]; omega
    · simp [s2]; omega
    · simp [Frame.Advances, Frame.Observation.value, Environment.addressWord, s2, s3, s]; omega
  have h4 : Frame.Rule s3 (.continue s4) := by
    apply Frame.Rule.observation s3 s4 .prevrandao
    · simp [Frame.At, Frame.Observation.opcode, s3, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s3]; omega
    · simp [s3]; omega
    · simp [Frame.Advances, Frame.Observation.value, Environment.addressWord, s3, s4, s]; omega
  have h5 : Frame.Rule s4 (.continue s5) := by
    apply Frame.Rule.observation s4 s5 .gaslimit
    · simp [Frame.At, Frame.Observation.opcode, s4, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s4]; omega
    · simp [s4]; omega
    · simp [Frame.Advances, Frame.Observation.value, Environment.addressWord, s4, s5, s]; omega
  have h6 : Frame.Rule s5 (.continue s6) := by
    apply Frame.Rule.observation s5 s6 .chainid
    · simp [Frame.At, Frame.Observation.opcode, s5, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s5]; omega
    · simp [s5]; omega
    · simp [Frame.Advances, Frame.Observation.value, Environment.addressWord, s5, s6, s]; omega
  have h7 : Frame.Rule s6 (.continue s7) := by
    apply Frame.Rule.observation s6 s7 .basefee
    · simp [Frame.At, Frame.Observation.opcode, s6, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s6]
    · simp [s6]; omega
    · simp [Frame.Advances, Frame.Observation.value, Environment.addressWord, s6, s7, s]
  have h8 : Frame.Rule s7 (.stop s8) := by
    apply Frame.Rule.stop
    simp [Frame.At, s7, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
  have trace : Runner.Terminates s 8 (.stopped s8) :=
    .next h1 (.next h2 (.next h3 (.next h4 (.next h5 (.next h6 (.next h7 (.stop h8)))))))
  have result := Runner.run_of_terminates trace 0
  refine ⟨s8, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simpa [s] using result

end EthLib.EVM.Runner.BlockEnvironmentProgram
