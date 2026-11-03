module

public import EthLib.EVM.Proofs.Frame.TransientInitial
public import EthLib.EVM.Proofs.Runner

/-! A constructed transient write, read, deletion and stop program. -/

@[expose] public section
namespace EthLib.EVM.Runner.TransientProgram

/-- Write, read, discard the read, delete, then stop. -/
def program : ByteArray := ⟨#[0x5d, 0x5c, 0x50, 0x5d, 0x00]⟩

/-- The actual runner executes all five instructions for arbitrary tracker inputs. -/
theorem run (xs : List Word) (room : xs.length ≤ 1019) (key value : Word) (g : Nat)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem)
    (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State)
    (warmAddresses : List World.Address) (warmSlots : List (World.Address × Word))
    (stateGas : Frame.StateGas) :
    let s : Frame.State := ⟨program, 0, ⟨key :: value :: key :: key :: 0 :: xs, by simp; omega⟩,
      302 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots, false, stateGas⟩
    ∃ t, Runner.run 5 s = .stopped t ∧ t.pc = 5 ∧ t.gas = g ∧ t.stack.val = xs ∧
      t.tracker = TransactionTracker.setTransientStorage
        (TransactionTracker.setTransientStorage tracker context.environment.currentTarget key value)
        context.environment.currentTarget key 0 := by
  let s : Frame.State := ⟨program, 0, ⟨key :: value :: key :: key :: 0 :: xs, by simp; omega⟩,
    302 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots, false, stateGas⟩
  let tx1 := TransactionTracker.setTransientStorage tracker context.environment.currentTarget key value
  let tx2 := TransactionTracker.setTransientStorage tx1 context.environment.currentTarget key 0
  let s1 : Frame.State := { s with tracker := tx1, pc := 1, gas := 202 + g, stack := ⟨key :: key :: 0 :: xs, by simp; omega⟩ }
  let s2 : Frame.State := { s1 with pc := 2, gas := 102 + g, stack := ⟨Frame.TransientValueRule s1 key :: key :: 0 :: xs, by simp; omega⟩ }
  let s3 : Frame.State := { s2 with pc := 3, gas := 100 + g, stack := ⟨key :: 0 :: xs, by simp; omega⟩ }
  let s4 : Frame.State := { s3 with tracker := tx2, pc := 4, gas := g, stack := ⟨xs, by omega⟩ }
  let s5 : Frame.State := { s4 with pc := 5 }
  have r1 : Frame.Rule s (.continue s1) := by
    apply Frame.Rule.tstore s s1 ⟨value :: key :: key :: 0 :: xs, by simp; omega⟩
      ⟨key :: key :: 0 :: xs, by simp; omega⟩ key value tx1
    · simp [Frame.At, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · rfl
    · rfl
    · simp [s]; omega
    · exact Frame.transient_write_fields _ _ _ _
    · simp [Frame.Advances, s, s1]; omega
  have r2 : Frame.Rule s1 (.continue s2) := by
    apply Frame.Rule.tload s1 s2 ⟨key :: 0 :: xs, by simp; omega⟩ key
    · simp [Frame.At, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s1]; omega
    · simp [Frame.Advances, s1, s2]; omega
  have r3 : Frame.Rule s2 (.continue s3) := by
    apply Frame.Rule.pop s2 s3 (Frame.TransientValueRule s1 key) (key :: 0 :: xs)
    · simp [Frame.At, s2, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s2]; omega
    · simp [Frame.Advances, s2, s3]; omega
  have r4 : Frame.Rule s3 (.continue s4) := by
    apply Frame.Rule.tstore s3 s4 ⟨0 :: xs, by simp; omega⟩ ⟨xs, by omega⟩ key 0 tx2
    · simp [Frame.At, s3, s2, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · rfl
    · rfl
    · simp [s3]
    · exact Frame.transient_write_fields _ _ _ _
    · simp [Frame.Advances, s3, s4]
  have r5 : Frame.Rule s4 (.stop s5) := by
    apply Frame.Rule.stop
    simp [Frame.At, s4, s3, s2, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
  have trace : Runner.Terminates s 5 (.stopped s5) := .next r1 (.next r2 (.next r3 (.next r4 (.stop r5))))
  have result := Runner.run_of_terminates trace 0
  exact ⟨s5, by simpa [s] using result, rfl, rfl, rfl, rfl⟩

/-- The constructed program's final transient map has deleted the selected key. -/
theorem run_deleted (xs : List Word) (room : xs.length ≤ 1019) (key value : Word) (g : Nat)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem)
    (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State)
    (warmAddresses : List World.Address) (warmSlots : List (World.Address × Word))
    (stateGas : Frame.StateGas) :
    let s : Frame.State := ⟨program, 0, ⟨key :: value :: key :: key :: 0 :: xs, by simp; omega⟩,
      302 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots, false, stateGas⟩
    ∃ t, Runner.run 5 s = .stopped t ∧
      (TransactionState.Reference.observe t.tracker).writes.transient
        (context.environment.currentTarget, key) = none := by
  obtain ⟨t, run, _, _, _, trackerEq⟩ :=
    run xs room key value g mem valid context returnData tracker warmAddresses warmSlots stateGas
  refine ⟨t, run, ?_⟩
  rw [trackerEq]
  have spec := (TransactionTracker.setTransientStorage_spec
    (TransactionTracker.setTransientStorage tracker context.environment.currentTarget key value)
    context.environment.currentTarget key 0).2.1 (context.environment.currentTarget, key)
  simpa using spec

end EthLib.EVM.Runner.TransientProgram
