import EthLib.EVM.Proofs

open EthLib.EVM

-- A successful observation exposes the actual head for all source-sized values.
example (s t : Frame.State) (o : Frame.Observation)
    (atOpcode : Frame.At s (some o.opcode)) (run : Frame.step s = .continue t)
    (bound : o.value s < Word.modulus) :
    ∃ w, t.stack.val = w :: s.stack.val ∧ w.toNat = o.value s :=
  Frame.step_observation_stack_exact s t o atOpcode run bound

-- The result also has a specified meaning outside the source U256 domain.
example (s t : Frame.State) (o : Frame.Observation)
    (atOpcode : Frame.At s (some o.opcode)) (run : Frame.step s = .continue t) :
    ∃ w, t.stack.val = w :: s.stack.val ∧ w.toNat = o.value s % Word.modulus :=
  Frame.step_observation_stack_mod s t o atOpcode run

-- The runner proof is quantified over both bytes, the old stack, gas and memory.
example (a b : UInt8) (xs : List Word) (room : xs.length ≤ 1022)
    (g : Nat) (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem) (context : CallData.Context) (returnData : ByteArray) :
    ∃ t, Runner.run 4 ⟨Runner.StraightLine.program a b, 0, ⟨xs, by omega⟩,
      9 + g, mem, valid, context, returnData⟩ = .stopped t ∧ t.pc = 6 ∧ t.gas = g ∧
      t.stack.val = Word.add (BitVec.ofNat 256 b.toNat) (BitVec.ofNat 256 a.toNat) :: xs :=
  Runner.StraightLine.push_push_add_stop a b xs room g mem valid context returnData

#print axioms Frame.step_observation_stack
#print axioms Frame.step_observation_stack_mod
#print axioms Frame.step_observation_stack_exact
#print axioms Frame.step_iff_rule
#print axioms Runner.StraightLine.push_push_add_stop

example (x y : Word) (xs : List Word) (room : xs.length ≤ 1021)
    (g : Nat) (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem) (context : CallData.Context) (returnData : ByteArray) :
    ∃ t, Runner.run 5 ⟨Runner.Mixed.program, 0, ⟨x :: y :: xs, by simp; omega⟩,
      10 + g, mem, valid, context, returnData⟩ = .stopped t ∧
      t.pc = 5 ∧ t.gas = g ∧ t.code = Runner.Mixed.program ∧ t.memory = mem ∧
      t.stack.val = BitVec.ofNat 256 g :: 2 :: Word.iszeroResult (Word.add x y) :: xs :=
  Runner.Mixed.add_iszero_pc_gas x y xs room g mem valid context returnData

#print axioms Runner.Mixed.add_iszero_pc_gas
