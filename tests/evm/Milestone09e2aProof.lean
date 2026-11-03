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
    t.warmAddresses = s.warmAddresses ∧ t.warmSlots = s.warmSlots ∧
    t.isStatic = s.isStatic ∧ t.stateGas = s.stateGas ∧ t.logs = s.logs := by
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

example (s t : Frame.State) (o : Frame.Observation)
    (at_ : Frame.At s (some o.opcode)) (run : Frame.step s = .continue t) :
    t.stack.val = Frame.observationWord (o.value s) :: s.stack.val ∧ t.context = s.context :=
  Frame.block_observation_actual s t o at_ run

example (id : Fin (2^64)) : (BitVec.ofNat 256 id.val).toNat = id.val :=
  Frame.chainId_word_toNat id

example (bytes : ByteArray) (s : Frame.State)
    (h : Word.ofBytesBE bytes = .ok s.context.environment.prevRandao) :
    s.context.environment.prevRandao.toBytesBE = bytes := Frame.prevRandao_codec bytes s h

example (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State) (warmAddresses : List World.Address) (warmSlots : List (World.Address × Word)) (static : Bool) (stateGas : Frame.StateGas) (logs : List Frame.LogEntry) (xs : List Word)
    (room : xs.length ≤ 1017) (g : Nat) (mem : Memory.Allocation.State)
    (valid : Memory.Allocation.Valid mem) :
    ∃ t, Runner.run 8 ⟨Runner.BlockEnvironmentProgram.program, 0, ⟨xs, by omega⟩,
      14 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots, static, stateGas, logs⟩ = .stopped t ∧
      t.pc = 8 ∧ t.gas = g ∧ t.code = Runner.BlockEnvironmentProgram.program ∧
      t.memory = mem ∧ t.context = context ∧ t.returnData = returnData ∧
      t.stack.val = context.environment.baseFee :: BitVec.ofNat 256 context.environment.chainId.val ::
        context.environment.gasLimit :: context.environment.prevRandao :: context.environment.number ::
        context.environment.timestamp :: Environment.addressWord context.environment.coinbase :: xs :=
  Runner.BlockEnvironmentProgram.run context returnData tracker warmAddresses warmSlots static stateGas logs xs room g mem valid

example (s : Frame.State) :
    Frame.observationWord (Frame.Observation.coinbase.value s) =
        Environment.addressWord s.context.environment.coinbase ∧
    Frame.observationWord (Frame.Observation.timestamp.value s) = s.context.environment.timestamp ∧
    Frame.observationWord (Frame.Observation.number.value s) = s.context.environment.number ∧
    Frame.observationWord (Frame.Observation.prevrandao.value s) = s.context.environment.prevRandao ∧
    Frame.observationWord (Frame.Observation.gaslimit.value s) = s.context.environment.gasLimit ∧
    Frame.observationWord (Frame.Observation.chainid.value s) = BitVec.ofNat 256 s.context.environment.chainId.val ∧
    Frame.observationWord (Frame.Observation.basefee.value s) = s.context.environment.baseFee :=
  Frame.block_observation_values s
