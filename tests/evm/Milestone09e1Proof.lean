import EthLib.EVM.Proofs

open EthLib.EVM

example (address : Environment.Address) :
    (Environment.addressWord address).toNat = address.val := Environment.addressWord_toNat address

example (s t : Frame.State) (o : Frame.Observation) (at_ : Frame.At s (some o.opcode))
    (run : Frame.step s = .continue t) :
    2 ≤ s.gas ∧ s.stack.val.length < 1024 ∧
      Frame.Advances s t (s.pc + 1) (s.gas - 2)
        (Frame.observationWord (o.value s) :: s.stack.val) :=
  Frame.step_observation_actual s t o at_ run

-- No opcode or program-counter premise is needed for the direct helper.
example (s t : Frame.State) (value : Nat → Nat)
    (run : Frame.observe s value = .continue t) :
    2 ≤ s.gas ∧ s.stack.val.length < 1024 ∧
    t.code = s.code ∧ t.memory = s.memory ∧ t.pc = s.pc + 1 ∧
    t.gas = s.gas - 2 ∧
    t.stack.val = Frame.observationWord (value (s.gas - 2)) :: s.stack.val ∧
    t.context = s.context ∧ t.returnData = s.returnData ∧ t.tracker = s.tracker ∧
    t.warmAddresses = s.warmAddresses ∧ t.warmSlots = s.warmSlots := by
  simpa [Frame.Advances] using Frame.observe_actual s t value run

example (s t : Frame.State) (value : Nat → Nat) (gas : 2 ≤ s.gas)
    (room : s.stack.val.length < 1024)
    (fields : Frame.Advances s t (s.pc + 1) (s.gas - 2)
      (Frame.observationWord (value (s.gas - 2)) :: s.stack.val)) :
    Frame.observe s value = .continue t :=
  Frame.observe_success s t value gas room fields

example (s : Frame.State) (value : Nat → Nat) (gas : s.gas < 2) :
    Frame.observe s value = .exception s .outOfGas := Frame.observe_gas s value gas

example (s : Frame.State) (value : Nat → Nat) (gas : 2 ≤ s.gas)
    (full : s.stack.val.length = 1024) :
    Frame.observe s value = .exception s .stackOverflow := Frame.observe_full s value gas full

example (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State) (warmAddresses : List World.Address) (warmSlots : List (World.Address × Word)) (xs : List Word)
    (room : xs.length ≤ 1019) (g : Nat) (mem : Memory.Allocation.State)
    (valid : Memory.Allocation.Valid mem) :
    ∃ t, Runner.run 6 ⟨Runner.EnvironmentProgram.program, 0, ⟨xs, by omega⟩,
      10 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots⟩ = .stopped t ∧
      t.pc = 6 ∧ t.gas = g ∧ t.code = Runner.EnvironmentProgram.program ∧
      t.memory = mem ∧ t.context = context ∧ t.returnData = returnData ∧
      t.stack.val = context.environment.gasPrice :: context.environment.value ::
        Environment.addressWord context.environment.caller ::
        Environment.addressWord context.environment.origin ::
        Environment.addressWord context.environment.currentTarget :: xs :=
  Runner.EnvironmentProgram.run context returnData tracker warmAddresses warmSlots xs room g mem valid
