import EthLib.EVM.Proofs

open EthLib.EVM

example (s : Frame.State) (empty : s.stack.val = []) :
    Frame.blobHash s = .exception s .stackUnderflow :=
  Frame.blobHash_empty s empty

example (s : Frame.State) (x : Word) (xs : List Word)
    (items : s.stack.val = x :: xs) (gas : s.gas < 3) :
    Frame.blobHash s = .exception s .outOfGas :=
  Frame.blobHash_gas s x xs items gas

example (s t : Frame.State) (x : Word) (xs : List Word)
    (items : s.stack.val = x :: xs) (gas : 3 ≤ s.gas)
    (fields : Frame.Advances s t (s.pc + 1) (s.gas - 3)
      (Environment.blobHash s.context.environment x :: xs)) :
    Frame.blobHash s = .continue t :=
  Frame.blobHash_success s t x xs items gas fields

example (s t : Frame.State) (h : Frame.blobHash s = .continue t) :
    ∃ x xs, s.stack.val = x :: xs ∧ 3 ≤ s.gas ∧
      Frame.Advances s t (s.pc + 1) (s.gas - 3)
        (Environment.blobHash s.context.environment x :: xs) :=
  Frame.blobHash_actual s t h

example (c : Environment.Context) (x : Word)
    (h : x.toNat < c.blobVersionedHashes.length) :
    Environment.blobHash c x = c.blobVersionedHashes[x.toNat] :=
  Environment.blobHash_in_range c x h

example (c : Environment.Context) (x : Word)
    (h : c.blobVersionedHashes.length ≤ x.toNat) :
    Environment.blobHash c x = 0 :=
  Environment.blobHash_out_of_range c x h

example (fuel : Nat) (s : Frame.State) :
    (Runner.run fuel s).frame.context = s.context ∧
      (Runner.run fuel s).frame.returnData = s.returnData :=
  ⟨Runner.run_context_unchanged fuel s, Runner.run_returnData_unchanged fuel s⟩

example (context : CallData.Context) (ret : ByteArray) (tracker : TransactionState.State) (warmAddresses : List World.Address) (warmSlots : List (World.Address × Word)) (x y : Word) (xs : List Word)
    (room : xs.length ≤ 1022) (g : Nat) (mem : Memory.Allocation.State)
    (valid : Memory.Allocation.Valid mem)
    (inside : x.toNat < context.environment.blobVersionedHashes.length)
    (outside : context.environment.blobVersionedHashes.length ≤ y.toNat) :
    ∃ t, Runner.run 3 ⟨Runner.BlobHashProgram.program, 0,
        ⟨x :: y :: xs, by simp; omega⟩, 9 + g, mem, valid, context, ret, tracker, warmAddresses, warmSlots⟩ = .exhausted t ∧
      t.stack.val = 0 :: context.environment.blobVersionedHashes[x.toNat] :: xs ∧
      t.context = context ∧ t.memory = mem ∧ t.returnData = ret ∧ t.gas = g ∧ t.pc = 3 :=
  Runner.BlobHashProgram.run_in_out context ret tracker warmAddresses warmSlots x y xs room g mem valid inside outside

example (fuel : Nat) (s : Frame.State) (code : s.code = Runner.BlobHashProgram.program) :
    (Runner.run fuel s).frame.memory = s.memory :=
  Runner.BlobHashProgram.program_memory fuel s code
