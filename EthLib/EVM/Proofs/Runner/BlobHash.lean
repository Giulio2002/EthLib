module

public import EthLib.EVM.Proofs.Runner
public import EthLib.EVM.Proofs.Environment

/-! Two transaction hash lookups in a bounded program. -/

@[expose] public section
namespace EthLib.EVM.Runner.BlobHashProgram

/-- Look up two indices and keep both results. -/
def program : ByteArray := ⟨#[0x49, 0x90, 0x49]⟩

/-- The bounded result selects both hashes for arbitrary context and indices. -/
theorem run (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State) (warmAddresses : List World.Address) (warmSlots : List (World.Address × Word)) (static : Bool) (stateGas : Frame.StateGas) (x y : Word)
    (xs : List Word) (room : xs.length ≤ 1022) (g : Nat)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem) :
    ∃ t, Runner.run 3 ⟨program, 0, ⟨x :: y :: xs, by simp; omega⟩,
        9 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots, static, stateGas⟩ = .exhausted t ∧
      t.stack.val = Environment.blobHash context.environment y ::
        Environment.blobHash context.environment x :: xs ∧
      t.context = context ∧ t.memory = mem ∧ t.returnData = returnData ∧
      t.gas = g ∧ t.pc = 3 := by
  let a := Environment.blobHash context.environment x
  let b := Environment.blobHash context.environment y
  let s : Frame.State := ⟨program, 0, ⟨x :: y :: xs, by simp; omega⟩, 9 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots, static, stateGas⟩
  let s1 : Frame.State := { s with pc := 1, gas := 6 + g, stack := ⟨a :: y :: xs, by simp; omega⟩ }
  let s2 : Frame.State := { s1 with pc := 2, gas := 3 + g, stack := ⟨y :: a :: xs, by simp; omega⟩ }
  let s3 : Frame.State := { s2 with pc := 3, gas := g, stack := ⟨b :: a :: xs, by simp; omega⟩ }
  have h1 : Frame.Rule s (.continue s1) := by
    apply Frame.Rule.blobhash s s1 x (y :: xs)
    · simp [Frame.At, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s]; omega
    · simp [Frame.Advances, s, s1, a]; omega
  have h2 : Frame.Rule s1 (.continue s2) := by
    apply Frame.Rule.swap s1 s2 ⟨0, by decide⟩ (by simp [s1])
    · simp [Frame.At, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s1]; omega
    · simp [Frame.Advances, s1, s2]; omega
  have h3 : Frame.Rule s2 (.continue s3) := by
    apply Frame.Rule.blobhash s2 s3 y (a :: xs)
    · simp [Frame.At, s2, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s2]
    · simp [Frame.Advances, s2, s3, s1, s, b]
  have trace : Runner.Continues s 3 s3 := .next h1 (.next h2 (.next h3 (.nil s3)))
  have result := (Runner.run_exhausted_iff 3 s s3).mpr trace
  exact ⟨s3, by simpa [s] using result, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The same actual runner result contains an in-range hash and an out-of-range zero. -/
theorem run_in_out (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State) (warmAddresses : List World.Address) (warmSlots : List (World.Address × Word)) (static : Bool) (stateGas : Frame.StateGas) (x y : Word)
    (xs : List Word) (room : xs.length ≤ 1022) (g : Nat)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem)
    (inside : x.toNat < context.environment.blobVersionedHashes.length)
    (outside : context.environment.blobVersionedHashes.length ≤ y.toNat) :
    ∃ t, Runner.run 3 ⟨program, 0, ⟨x :: y :: xs, by simp; omega⟩,
        9 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots, static, stateGas⟩ = .exhausted t ∧
      t.stack.val = 0 :: context.environment.blobVersionedHashes[x.toNat] :: xs ∧
      t.context = context ∧ t.memory = mem ∧ t.returnData = returnData ∧
      t.gas = g ∧ t.pc = 3 := by
  obtain ⟨t, result, stack, contextEq, memoryEq, retEq, gasEq, pcEq⟩ :=
    run context returnData tracker warmAddresses warmSlots static stateGas x y xs room g mem valid
  refine ⟨t, result, ?_, contextEq, memoryEq, retEq, gasEq, pcEq⟩
  simpa [Environment.blobHash_in_range context.environment x inside,
    Environment.blobHash_out_of_range context.environment y outside] using stack

/-- Every bounded outcome preserves context and return data. -/
theorem run_preserves (fuel : Nat) (s : Frame.State) :
    (Runner.run fuel s).frame.context = s.context ∧
      (Runner.run fuel s).frame.returnData = s.returnData :=
  ⟨Runner.run_context_unchanged fuel s, Runner.run_returnData_unchanged fuel s⟩

/-- Every bounded outcome of a memory-pure trace preserves memory. -/
theorem run_preserves_memory (fuel : Nat) (s : Frame.State)
    (pure : Runner.PureMemoryRun fuel s) :
    (Runner.run fuel s).frame.memory = s.memory :=
  Runner.run_memory_unchanged_of_pure fuel s pure

set_option maxHeartbeats 2000000 in
/-- Every program counter in this program is free of memory instructions. -/
theorem program_pure (s : Frame.State) (code : s.code = program) :
    Frame.PureMemoryStep s := by
  unfold Frame.PureMemoryStep
  have possible : s.pc = 0 ∨ s.pc = 1 ∨ s.pc = 2 ∨ 3 ≤ s.pc := by omega
  rcases possible with pc | pc | pc | pc <;>
    simp [Frame.At, code, program, pc, ByteArray.size,
      -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]

/-- All bounded outcomes of this program preserve memory. -/
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

end EthLib.EVM.Runner.BlobHashProgram
