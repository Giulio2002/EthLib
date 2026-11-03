module

public import EthLib.EVM.Proofs.Runner.BlockHash
public import EthLib.EVM.Proofs.Runner.BlobFee

/-! A historical block and blob observation program. -/

@[expose] public section
namespace EthLib.EVM.Runner.BlockBlobIntegration

/-- Look up a block hash, observe the block number, and look up a blob hash and fee. -/
def program : ByteArray := ⟨#[0x40, 0x90, 0x49, 0x43, 0x4a]⟩

/-- The bounded run computes each observation for arbitrary accepted context and state. -/
theorem run (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State) (warmAddresses : List World.Address) (warmSlots : List (World.Address × Word)) (static : Bool) (stateGas : Frame.StateGas) (logs : List Frame.LogEntry) (x y : Word)
    (xs : List Word) (room : xs.length ≤ 1020) (g : Nat)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem) :
    ∃ t, Runner.run 5 ⟨program, 0, ⟨x :: y :: xs, by simp; omega⟩,
        30 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots, static, stateGas, logs⟩ = .exhausted t ∧
      t.stack.val = Frame.observationWord (BlobFee.calculateWith context.environment.blobFeeSchedule context.environment.excessBlobGas) ::
        context.environment.number :: Environment.blobHash context.environment y ::
        Environment.blockHash context.environment.blockHashes context.environment.number x :: xs ∧
      t.code = program ∧ t.context = context ∧ t.memory = mem ∧ t.returnData = returnData ∧
      t.gas = g ∧ t.pc = 5 := by
  let a := Environment.blockHash context.environment.blockHashes context.environment.number x
  let b := Environment.blobHash context.environment y
  let c := context.environment.number
  let d := Frame.observationWord (BlobFee.calculateWith context.environment.blobFeeSchedule context.environment.excessBlobGas)
  let s : Frame.State := ⟨program, 0, ⟨x :: y :: xs, by simp; omega⟩, 30 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots, static, stateGas, logs⟩
  let s1 : Frame.State := { s with pc := 1, gas := 10 + g, stack := ⟨a :: y :: xs, by simp; omega⟩ }
  let s2 : Frame.State := { s with pc := 2, gas := 7 + g, stack := ⟨y :: a :: xs, by simp; omega⟩ }
  let s3 : Frame.State := { s with pc := 3, gas := 4 + g, stack := ⟨b :: a :: xs, by simp; omega⟩ }
  let s4 : Frame.State := { s with pc := 4, gas := 2 + g, stack := ⟨c :: b :: a :: xs, by simp; omega⟩ }
  let s5 : Frame.State := { s with pc := 5, gas := g, stack := ⟨d :: c :: b :: a :: xs, by simp; omega⟩ }
  have h1 : Frame.Rule s (.continue s1) := by
    apply Frame.Rule.blockhash s s1 x (y :: xs) a
    · simp [Frame.At, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s]; omega
    · exact (Frame.blockHashValue_iff _ _ _ _).mpr rfl
    · simp [Frame.Advances, s, s1, a]; omega
  have h2 : Frame.Rule s1 (.continue s2) := by
    apply Frame.Rule.swap s1 s2 ⟨0, by decide⟩ (by simp [s1])
    · simp [Frame.At, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s1]; omega
    · simp [Frame.Advances, s1, s2]; omega
  have h3 : Frame.Rule s2 (.continue s3) := by
    apply Frame.Rule.blobhash s2 s3 y (a :: xs)
    · simp [Frame.At, s2, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s2]; omega
    · simp [Frame.Advances, s2, s3, s, b]; omega
  have h4 : Frame.Rule s3 (.continue s4) := by
    apply Frame.Rule.observation s3 s4 .number
    · simp [Frame.At, Frame.Observation.opcode, s3, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s3]; omega
    · simp [s3]; omega
    · simp [Frame.Advances, Frame.Observation.value, s3, s4, s, c]; omega
  have h5 : Frame.Rule s4 (.continue s5) := by
    apply Frame.Rule.observation s4 s5 .blobbasefee
    · simp [Frame.At, Frame.Observation.opcode, s4, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s4]
    · simp [s4]; omega
    · simp [Frame.Advances, Frame.Observation.value, Frame.observationWord, s4, s5, s, d]
  have trace : Runner.Continues s 5 s5 := .next h1 (.next h2 (.next h3 (.next h4 (.next h5 (.nil s5)))))
  have result := (Runner.run_exhausted_iff 5 s s5).mpr trace
  exact ⟨s5, by simpa [s] using result, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A source-valid in-window history and a representable fee give exact source values.

The chain maps block numbers to decoded 32-byte hashes.
The list in the context contains the transaction's decoded versioned hashes.
The premises do not validate headers, transactions, or chain ancestry.
The fee uses the supplied schedule and is exact when it fits a word. -/
theorem run_source_in_window (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State) (warmAddresses : List World.Address) (warmSlots : List (World.Address × Word)) (static : Bool) (stateGas : Frame.StateGas) (logs : List Frame.LogEntry)
    (x y : Word) (xs : List Word) (room : xs.length ≤ 1020) (g : Nat)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem)
    (chain : Nat → Word)
    (history : Environment.HistoryMatches context.environment.blockHashes
      context.environment.number chain)
    (window : x.toNat < context.environment.number.toNat ∧
      context.environment.number.toNat ≤ x.toNat + 256)
    (feeBound : BlobFee.calculateWith context.environment.blobFeeSchedule context.environment.excessBlobGas < Word.modulus) :
    ∃ t fee, Runner.run 5 ⟨program, 0, ⟨x :: y :: xs, by simp; omega⟩,
        30 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots, static, stateGas, logs⟩ = .exhausted t ∧
      Word.ofNat (BlobFee.calculateWith context.environment.blobFeeSchedule context.environment.excessBlobGas) = .ok fee ∧
      fee.toNat = BlobFee.calculateWith context.environment.blobFeeSchedule context.environment.excessBlobGas ∧
      t.stack.val = fee :: context.environment.number ::
        (context.environment.blobVersionedHashes[y.toNat]?).getD 0 :: chain x.toNat :: xs ∧
      t.code = program ∧ t.context = context ∧ t.memory = mem ∧ t.returnData = returnData ∧
      t.gas = g ∧ t.pc = 5 := by
  obtain ⟨t, result, stack, code, ctx, memory, data, gas, pc⟩ :=
    run context returnData tracker warmAddresses warmSlots static stateGas logs x y xs room g mem valid
  refine ⟨t, Frame.observationWord (BlobFee.calculateWith context.environment.blobFeeSchedule context.environment.excessBlobGas),
    result, Frame.observationWord_checked _ feeBound, Frame.observationWord_exact _ feeBound, ?_,
    code, ctx, memory, data, gas, pc⟩
  simpa [Environment.blobHash,
    Environment.blockHash_source_agreement _ _ _ chain history window] using stack

end EthLib.EVM.Runner.BlockBlobIntegration
