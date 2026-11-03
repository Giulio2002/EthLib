import EthLib.EVM.Proofs.Runner.MixedCopy

open EthLib.EVM

-- A downstream proof consumes the concrete bounded run and its source-word facts.
example (ctx : CallData.Context) (ret : ByteArray) (tracker : TransactionState.State) (warmAddresses : List World.Address) (warmSlots : List (World.Address × Word)) (co ro : Word) (xs : List Word)
    (room : xs.length ≤ 1016) (mem : Memory.Allocation.State)
    (valid : Memory.Allocation.Valid mem) (bounds : ro.toNat + 32 ≤ ret.size) (g : Nat) :
    let a := CallData.readRange ctx.data co.toNat 32
    let b := (ret.data.toList.drop ro.toNat).take 32
    let m1 := Memory.Allocation.write mem 0 a
    let m2 := Memory.Allocation.write m1 32 b
    let m3 := (Memory.Allocation.loadWord m2 0).2
    let c1 := Gas.inputCopyCost mem.words 0 32
    let c2 := Gas.inputCopyCost m1.words 32 32
    let c3 := 3 + Gas.rangeCost m2.words 0 32
    let c4 := 3 + Gas.rangeCost m3.words 32 32
    ∃ t, Runner.run 5 ⟨Runner.MixedCopy.program, 0,
        ⟨[0, co, 32, 32, ro, 32, 0, 32] ++ xs, by simp; omega⟩,
        c1 + c2 + c3 + 3 + c4 + g, mem, valid, ctx, ret, tracker, warmAddresses, warmSlots⟩ = .exhausted t ∧
      t.pc = 5 ∧ t.gas = g ∧ t.context = ctx ∧ t.returnData = ret ∧
      Memory.readRange t.memory.store 0 32 = a ∧ Memory.readRange t.memory.store 32 32 = b := by
  obtain ⟨t, run, _, pc, gas, _, _, _, context, returnData, _, _, a, b, _⟩ :=
    Runner.MixedCopy.run_mixed ctx ret tracker warmAddresses warmSlots co ro xs room mem valid bounds g
  exact ⟨t, run, pc, gas, context, returnData, a, b⟩
