module

public import EthLib.EVM.Proofs.Runner

/-!
# Mixed bounded program

The rules follow Cancun execution-specs revision
`fd9298410ec7218838c8348f69c1eb633f1797dc`,
`vm/instructions/arithmetic.py`, `comparison.py`, and `control_flow.py`.
-/

@[expose] public section
namespace EthLib.EVM.Runner.Mixed

/-- ADD, ISZERO, PC, GAS and STOP. -/
def program : ByteArray := ⟨#[0x01, 0x15, 0x58, 0x5a, 0x00]⟩

/-- The mixed program runs for every input stack, gas reserve and valid memory.

The GAS word is reduced modulo `2^256`, as required by the frame's total extension.
-/
theorem add_iszero_pc_gas (x y : Word) (xs : List Word) (room : xs.length ≤ 1021)
    (g : Nat) (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem) (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State) (warmAddresses : List World.Address) (warmSlots : List (World.Address × Word)) (static : Bool) (stateGas : Frame.StateGas) (logs : List Frame.LogEntry) :
    ∃ t, Runner.run 5 ⟨program, 0, ⟨x :: y :: xs, by simp; omega⟩,
      10 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots, static, stateGas, logs⟩ = .stopped t ∧
      t.pc = 5 ∧ t.gas = g ∧ t.code = program ∧ t.memory = mem ∧
      t.stack.val = BitVec.ofNat 256 g :: 2 :: Word.iszeroResult (Word.add x y) :: xs := by
  -- Name each intermediate frame to state its exact stack and gas.
  let z := Word.iszeroResult (Word.add x y)
  let s : Frame.State := ⟨program, 0, ⟨x :: y :: xs, by simp; omega⟩, 10 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots, static, stateGas, logs⟩
  let s1 : Frame.State := { s with pc := 1, gas := 7 + g, stack := ⟨Word.add x y :: xs, by simp; omega⟩ }
  let s2 : Frame.State := { s with pc := 2, gas := 4 + g, stack := ⟨z :: xs, by simp; omega⟩ }
  let s3 : Frame.State := { s with pc := 3, gas := 2 + g, stack := ⟨2 :: z :: xs, by simp; omega⟩ }
  let s4 : Frame.State := { s with pc := 4, gas := g, stack := ⟨BitVec.ofNat 256 g :: 2 :: z :: xs, by simp; omega⟩ }
  let s5 : Frame.State := { s4 with pc := 5 }
  have h1 : Frame.Rule s (.continue s1) := by
    apply Frame.Rule.add s s1 x y xs
    · simp [Frame.At, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s]; omega
    · simp [Frame.Advances, s, s1]; omega
  have h2 : Frame.Rule s1 (.continue s2) := by
    apply Frame.Rule.iszero s1 s2 (Word.add x y) xs
    · simp [Frame.At, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s1]; omega
    · simp [Frame.Advances, s1, s2, z]; omega
  have h3 : Frame.Rule s2 (.continue s3) := by
    apply Frame.Rule.observation s2 s3 .pc
    · simp [Frame.At, Frame.Observation.opcode, s2, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s2]; omega
    · simp [s2]; omega
    · simp [Frame.Advances, Frame.Observation.value, s2, s3]; omega
  have h4 : Frame.Rule s3 (.continue s4) := by
    apply Frame.Rule.observation s3 s4 .gas
    · simp [Frame.At, Frame.Observation.opcode, s3, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s3]
    · simp [s3]; omega
    · simp [Frame.Advances, Frame.Observation.value, s3, s4]
  have h5 : Frame.Rule s4 (.stop s5) := by
    apply Frame.Rule.stop
    simp [Frame.At, s4, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
  -- Compose the independent instruction rules into a bounded terminal trace.
  have trace : Runner.Terminates s 5 (.stopped s5) :=
    .next h1 (.next h2 (.next h3 (.next h4 (.stop h5))))
  have run := Runner.run_of_terminates trace 0
  refine ⟨s5, ?_, rfl, rfl, rfl, rfl, rfl⟩
  simpa [s] using run

end EthLib.EVM.Runner.Mixed
