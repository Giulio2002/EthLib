module

public import EthLib.EVM.Proofs.Runner

/-! A two-instruction call-data observation program. -/

@[expose] public section
namespace EthLib.EVM.Runner.CallDataProgram

/-- Load a word, then observe the input size. -/
def program : ByteArray := ⟨#[0x35, 0x36]⟩

/-- The program observes arbitrary message bytes and an arbitrary full-width offset. -/
theorem load_size (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State) (warmAddresses : List World.Address) (warmSlots : List (World.Address × Word)) (static : Bool) (stateGas : Frame.StateGas) (logs : List Frame.LogEntry) (x : Word) (xs : List Word)
    (room : xs.length ≤ 1022) (g : Nat) (mem : Memory.Allocation.State)
    (valid : Memory.Allocation.Valid mem) :
    ∃ t, run 2 ⟨program, 0, ⟨x :: xs, by simp; omega⟩, 5 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots, static, stateGas, logs⟩ =
      .exhausted t ∧ t.stack.val =
        Frame.observationWord context.data.size :: CallData.load context x :: xs ∧
      t.context = context ∧ t.memory = mem ∧ t.gas = g := by
  let s : Frame.State := ⟨program, 0, ⟨x :: xs, by simp; omega⟩, 5 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots, static, stateGas, logs⟩
  let s1 : Frame.State := { s with pc := 1, gas := 2 + g, stack := ⟨CallData.load context x :: xs, by simp; omega⟩ }
  let s2 : Frame.State := { s1 with pc := 2, gas := g, stack := ⟨Frame.observationWord context.data.size :: CallData.load context x :: xs, by simp; omega⟩ }
  have h1 : Frame.Rule s (.continue s1) := by
    apply Frame.Rule.calldataload s s1 x xs
    · simp [Frame.At, s, program, ByteArray.size, -ByteArray.size_data,
        ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s]; omega
    · simp [Frame.Advances, s, s1]; omega
  have h2 : Frame.Rule s1 (.continue s2) := by
    apply Frame.Rule.observation s1 s2 .calldatasize
    · simp [Frame.At, Frame.Observation.opcode, s1, s, program, ByteArray.size,
        -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s1]
    · simp [s1]; omega
    · simp [Frame.Advances, Frame.Observation.value, Frame.observationWord, s1, s2, s]
  have trace : Runner.Continues s 2 s2 := .next h1 (.next h2 (.nil s2))
  have run := (Runner.run_exhausted_iff 2 s s2).mpr trace
  exact ⟨s2, by simpa [s] using run, rfl, rfl, rfl, rfl⟩

end EthLib.EVM.Runner.CallDataProgram
