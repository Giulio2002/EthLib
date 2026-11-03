import EthLib.EVM.Proofs.Runner.Sload

open EthLib.EVM

example (s t : Frame.State) (run : Frame.sload s = .continue t) :
    ∃ (rest : Stack) (key : Word), s.stack.val = key :: rest.val ∧
      Frame.SloadCost s key ≤ s.gas ∧
      Frame.Advances { s with warmSlots := Frame.SloadWarm s key, tracker := Frame.SloadRead s key }
        t (s.pc + 1) (s.gas - Frame.SloadCost s key) (Frame.SloadValue s key :: rest.val) :=
  (Frame.sload_success_iff s t).mp run

example (s t : Frame.State) (rest : Stack) (key : Word)
    (items : s.stack.val = key :: rest.val) (gas : Frame.SloadCost s key ≤ s.gas)
    (fields : Frame.Advances { s with warmSlots := Frame.SloadWarm s key, tracker := Frame.SloadRead s key }
      t (s.pc + 1) (s.gas - Frame.SloadCost s key) (Frame.SloadValue s key :: rest.val)) :
    Frame.sload s = .continue t :=
  (Frame.sload_success_iff s t).mpr ⟨rest, key, items, gas, fields⟩

example (s input : Frame.State) (reason : Frame.Exception)
    (run : Frame.sload s = .exception input reason) :
    (s.stack.val = [] ∧ input = s ∧ reason = .stackUnderflow) ∨
      (∃ (rest : Stack) (key : Word), s.stack.val = key :: rest.val ∧
        s.gas < Frame.SloadCost s key ∧
        input = { s with stack := rest, warmSlots := Frame.SloadWarm s key } ∧
        reason = .outOfGas) :=
  (Frame.sload_exception_iff s input reason).mp run

example (s : Frame.State) (empty : s.stack.val = []) :
    Frame.sload s = .exception s .stackUnderflow :=
  (Frame.sload_exception_iff s s .stackUnderflow).mpr (Or.inl ⟨empty, rfl, rfl⟩)

example (s : Frame.State) (rest : Stack) (key : Word)
    (items : s.stack.val = key :: rest.val) (low : s.gas < Frame.SloadCost s key) :
    Frame.sload s = .exception { s with stack := rest, warmSlots := Frame.SloadWarm s key } .outOfGas :=
  (Frame.sload_exception_iff s _ _).mpr (Or.inr ⟨rest, key, items, low, rfl, rfl⟩)

example (s : Frame.State) (key : Word) :
    TransactionTracker.StorageValue (TransactionState.Reference.observe s.tracker)
      s.context.environment.currentTarget key (Frame.SloadValue s key) :=
  Frame.sload_storage_value s key

example (s : Frame.State) (key : Word) (slot : World.Address × Word) :
    slot ∈ Frame.SloadWarm s key ↔ slot = (s.context.environment.currentTarget, key) ∨ slot ∈ s.warmSlots :=
  Frame.sload_warm_membership s key slot

example (s : Frame.State) (key : Word) :
    ((s.context.environment.currentTarget, key) ∈ s.warmSlots → Frame.SloadCost s key = 100) ∧
    ((s.context.environment.currentTarget, key) ∉ s.warmSlots → Frame.SloadCost s key = 2100) :=
  Frame.sload_cost_cases s key

example (s : Frame.State) (out : Frame.Outcome)
    (notSload : ¬ Frame.At s (some .sload)) (notSstore : ¬ Frame.At s (some .sstore)) (rule : Frame.Rule s out) :
    out.frame.warmSlots = s.warmSlots :=
  Frame.outcome_slots_unchanged_of_not_sload notSload notSstore rule

example (key : Word) (xs : List Word) (room : xs.length ≤ 1022) (g : Nat)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem)
    (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State)
    (warm : List World.Address) (slots : List (World.Address × Word)) (static : Bool) (stateGas : Frame.StateGas)
    (cold : (context.environment.currentTarget, key) ∉ slots) :
    let s : Frame.State := ⟨Runner.SloadProgram.program, 0, ⟨key :: key :: xs, by simp; omega⟩,
      2203 + g, mem, valid, context, returnData, tracker, warm, slots, static, stateGas⟩
    ∃ t, Runner.run 4 s = .stopped t ∧ t.pc = 4 ∧ t.gas = g ∧
      t.stack.val = Frame.SloadValue s key :: Frame.SloadValue s key :: xs ∧
      t.warmSlots = (context.environment.currentTarget, key) :: slots ∧ t.warmAddresses = warm ∧
      t.tracker = { tracker with storageReads := (context.environment.currentTarget, key) :: (context.environment.currentTarget, key) :: tracker.storageReads } ∧
      t.code = Runner.SloadProgram.program ∧ t.memory = mem ∧ t.context = context ∧ t.returnData = returnData :=
  Runner.SloadProgram.run key xs room g mem valid context returnData tracker warm slots static stateGas cold

example (fuel : Nat) (s : Frame.State) (slot : World.Address × Word) (warm : slot ∈ s.warmSlots) :
    slot ∈ (Runner.run fuel s).frame.warmSlots :=
  Runner.SloadProgram.run_slots_monotone fuel s slot warm

example (s t : Frame.State) (run : Frame.sload s = .continue t) :
    ∃ (rest : Stack) (key : Word), s.stack.val = key :: rest.val ∧
      Frame.SloadCost s key ≤ s.gas ∧ t.pc = s.pc + 1 ∧
      t.gas = s.gas - Frame.SloadCost s key ∧ t.stack.val = Frame.SloadValue s key :: rest.val ∧
      t.code = s.code ∧ t.memory = s.memory ∧ t.context = s.context ∧ t.returnData = s.returnData ∧
      t.warmAddresses = s.warmAddresses ∧ t.warmSlots = Frame.SloadWarm s key ∧
      t.tracker.parent = s.tracker.parent ∧ t.tracker.writes = s.tracker.writes ∧
      t.tracker.accountReads = s.tracker.accountReads ∧
      t.tracker.storageReads = (s.context.environment.currentTarget, key) :: s.tracker.storageReads ∧
      t.tracker.createdAccounts = s.tracker.createdAccounts ∧ t.tracker.snapshots = s.tracker.snapshots := by
  obtain ⟨rest, key, items, gas, code, mem, pc, left, stack, context, ret, tracker, warm, slots, static, stateGas⟩ :=
    (Frame.sload_success_iff s t).mp run
  refine ⟨rest, key, items, gas, pc, left, stack, code, mem, context, ret, warm, slots, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [tracker]; rfl
