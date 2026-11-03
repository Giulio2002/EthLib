module

public import EthLib.EVM.Proofs.Runner.BlobHash
public import EthLib.EVM.Proofs.Frame.BlobFee

/-! A bounded program observes a blob hash and the blob base fee. -/

@[expose] public section
namespace EthLib.EVM.Runner.BlobFeeProgram

/-- BLOBHASH followed by BLOBBASEFEE. -/
def program : ByteArray := ⟨#[0x49, 0x4a]⟩

/-- The actual bounded run preserves arbitrary context and memory. -/
theorem run (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State) (warmAddresses : List World.Address) (warmSlots : List (World.Address × Word)) (static : Bool) (stateGas : Frame.StateGas) (x : Word)
    (xs : List Word) (room : xs.length ≤ 1022) (g : Nat)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem) :
    ∃ t, Runner.run 2 ⟨program, 0, ⟨x :: xs, by simp; omega⟩,
        5 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots, static, stateGas⟩ = .exhausted t ∧
      t.stack.val = Frame.observationWord (BlobFee.calculateWith context.environment.blobFeeSchedule context.environment.excessBlobGas) ::
        Environment.blobHash context.environment x :: xs ∧
      t.context = context ∧ t.memory = mem ∧ t.returnData = returnData ∧
      t.gas = g ∧ t.pc = 2 := by
  let a := Environment.blobHash context.environment x
  let b := Frame.observationWord (BlobFee.calculateWith context.environment.blobFeeSchedule context.environment.excessBlobGas)
  let s : Frame.State := ⟨program, 0, ⟨x :: xs, by simp; omega⟩, 5 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots, static, stateGas⟩
  let s1 : Frame.State := { s with pc := 1, gas := 2 + g, stack := ⟨a :: xs, by simp; omega⟩ }
  let s2 : Frame.State := { s1 with pc := 2, gas := g, stack := ⟨b :: a :: xs, by simp; omega⟩ }
  have h1 : Frame.Rule s (.continue s1) := by
    apply Frame.Rule.blobhash s s1 x xs
    · simp [Frame.At, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s]; omega
    · simp [Frame.Advances, s, s1, a]; omega
  have h2 : Frame.Rule s1 (.continue s2) := by
    apply Frame.Rule.observation s1 s2 .blobbasefee
    · simp [Frame.At, Frame.Observation.opcode, s1, s, program, ByteArray.size,
        -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s1]
    · simp [s1]; omega
    · simp [Frame.Advances, Frame.Observation.value, Frame.observationWord, s1, s2, s, b]
  have trace : Runner.Continues s 2 s2 := .next h1 (.next h2 (.nil s2))
  have result := (Runner.run_exhausted_iff 2 s s2).mpr trace
  exact ⟨s2, by simpa [s] using result, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every bounded outcome preserves the full context and return data. -/
theorem run_preserves (fuel : Nat) (s : Frame.State) :
    (Runner.run fuel s).frame.context = s.context ∧
      (Runner.run fuel s).frame.returnData = s.returnData :=
  ⟨Runner.run_context_unchanged fuel s, Runner.run_returnData_unchanged fuel s⟩

set_option maxHeartbeats 2000000 in
/-- Every instruction in this program preserves memory. -/
theorem program_pure (s : Frame.State) (code : s.code = program) :
    Frame.PureMemoryStep s := by
  unfold Frame.PureMemoryStep
  have possible : s.pc = 0 ∨ s.pc = 1 ∨ 2 ≤ s.pc := by omega
  rcases possible with pc | pc | pc <;>
    simp [Frame.At, code, program, pc, ByteArray.size,
      -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]

/-- Every bounded outcome of this program preserves memory. -/
theorem program_memory (fuel : Nat) (s : Frame.State) (code : s.code = program) :
    (Runner.run fuel s).frame.memory = s.memory := by
  apply Runner.run_memory_unchanged_of_pure
  induction fuel generalizing s with
  | zero => trivial
  | succ fuel ih =>
    refine ⟨program_pure s code, ?_⟩
    cases h : Frame.step s with
    | «continue» t => exact ih t ((Frame.continue_code_unchanged h).trans code)
    | stop t => trivial
    | revert input gas output => trivial
    | exception input e => trivial
    | unsupported input op => trivial

end EthLib.EVM.Runner.BlobFeeProgram
