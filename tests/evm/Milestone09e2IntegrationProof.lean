import EthLib.EVM.Proofs.Runner.BlockBlobIntegration

open EthLib.EVM

example (context : CallData.Context) (data : ByteArray) (x y : Word)
    (xs : List Word) (room : xs.length ≤ 1020) (g : Nat)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem) :
    ∃ t, Runner.run 5 ⟨Runner.BlockBlobIntegration.program, 0,
        ⟨x :: y :: xs, by simp; omega⟩, 30 + g, mem, valid, context, data⟩ = .exhausted t ∧
      t.stack.val = Frame.observationWord (BlobFee.calculateBlobGasPrice context.environment.excessBlobGas) ::
        context.environment.number :: Environment.blobHash context.environment y ::
        Environment.blockHash context.environment.blockHashes context.environment.number x :: xs ∧
      t.code = Runner.BlockBlobIntegration.program ∧ t.context = context ∧ t.memory = mem ∧
      t.returnData = data ∧ t.gas = g ∧ t.pc = 5 :=
  Runner.BlockBlobIntegration.run context data x y xs room g mem valid

#print axioms Runner.BlockBlobIntegration.run

-- The exact contract derives the output from history and fee premises.
example (context : CallData.Context) (data : ByteArray) (x y : Word)
    (xs : List Word) (room : xs.length ≤ 1020) (g : Nat)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem)
    (chain : Nat → Word)
    (history : Environment.HistoryMatches context.environment.blockHashes context.environment.number chain)
    (window : x.toNat < context.environment.number.toNat ∧
      context.environment.number.toNat ≤ x.toNat + 256)
    (feeBound : BlobFee.calculateBlobGasPrice context.environment.excessBlobGas < Word.modulus) :
    ∃ t fee, Runner.run 5 ⟨Runner.BlockBlobIntegration.program, 0,
        ⟨x :: y :: xs, by simp; omega⟩, 30 + g, mem, valid, context, data⟩ = .exhausted t ∧
      Word.ofNat (BlobFee.calculateBlobGasPrice context.environment.excessBlobGas) = .ok fee ∧
      fee.toNat = BlobFee.calculateBlobGasPrice context.environment.excessBlobGas ∧
      t.stack.val = fee :: context.environment.number ::
        (context.environment.blobVersionedHashes[y.toNat]?).getD 0 :: chain x.toNat :: xs ∧
      t.code = Runner.BlockBlobIntegration.program ∧ t.context = context ∧ t.memory = mem ∧
      t.returnData = data ∧ t.gas = g ∧ t.pc = 5 :=
  Runner.BlockBlobIntegration.run_source_in_window context data x y xs room g mem valid chain history window feeBound

#print axioms Runner.BlockBlobIntegration.run_source_in_window
