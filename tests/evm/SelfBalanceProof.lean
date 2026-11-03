import EthLib.EVM.Proofs.Runner.SelfBalance

open EthLib.EVM

example (s t : Frame.State) :
    Frame.selfBalance s = .continue t ↔
      5 ≤ s.gas ∧ s.stack.val.length < 1024 ∧
      Frame.Advances { s with tracker := Frame.SelfBalanceRead s } t (s.pc + 1) (s.gas - 5)
        ((Frame.SelfBalanceAccount s).balance :: s.stack.val) :=
  Frame.selfBalance_success_iff s t

example (s input : Frame.State) (reason : Frame.Exception) :
    Frame.selfBalance s = .exception input reason ↔
      (s.gas < 5 ∧ input = s ∧ reason = .outOfGas) ∨
      (5 ≤ s.gas ∧ s.stack.val.length = 1024 ∧
        input = { s with tracker := Frame.SelfBalanceRead s } ∧ reason = .stackOverflow) :=
  Frame.selfBalance_exception_iff s input reason

example (s : Frame.State) (at_ : Frame.At s (some .selfbalance)) :
    Frame.step s = Frame.selfBalance s := Frame.step_selfBalance s at_

example (xs : List Word) (room : xs.length ≤ 1022) (g : Nat)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem)
    (context : CallData.Context) (data : ByteArray) (tracker : TransactionState.State) (warmAddresses : List World.Address) (warmSlots : List (World.Address × Word)) (static : Bool) (stateGas : Frame.StateGas) :
    let s : Frame.State := ⟨Runner.SelfBalanceProgram.program, 0, ⟨xs, by omega⟩,
      7 + g, mem, valid, context, data, tracker, warmAddresses, warmSlots, static, stateGas⟩
    ∃ t, Runner.run 3 s = .stopped t ∧ t.pc = 3 ∧ t.gas = g ∧
      t.stack.val = 1 :: (Frame.SelfBalanceAccount s).balance :: xs ∧
      t.tracker = Frame.SelfBalanceRead s ∧ t.memory = mem ∧ t.context = context ∧
      t.returnData = data ∧ t.code = Runner.SelfBalanceProgram.program :=
  Runner.SelfBalanceProgram.run xs room g mem valid context data tracker warmAddresses warmSlots static stateGas

example (s : Frame.State) :
    (∀ x, (TransactionState.Reference.observe s.tracker).writes.accounts
      s.context.environment.currentTarget = some x →
      Frame.SelfBalanceAccount s = x.getD World.emptyAccount) ∧
    ((TransactionState.Reference.observe s.tracker).writes.accounts
      s.context.environment.currentTarget = none →
      Frame.SelfBalanceAccount s = ((TransactionState.Reference.observe s.tracker).parentAccounts
        s.context.environment.currentTarget).getD World.emptyAccount) :=
  Frame.selfBalance_account_value s

example (s : Frame.State) (out : Frame.Outcome)
    (notSelf : ¬ Frame.At s (some .selfbalance)) (notBalance : ¬ Frame.At s (some .balance)) (notSload : ¬ Frame.At s (some .sload)) (notSstore : ¬ Frame.At s (some .sstore)) (rule : Frame.Rule s out) :
    out.frame.tracker = s.tracker :=
  Frame.outcome_tracker_unchanged_of_not_selfBalance notSelf notBalance notSload notSstore rule

example (fuel : Nat) (s : Frame.State) (trace : Runner.NoSstoreRun fuel s) :
    (Runner.run fuel s).frame.tracker.parent = s.tracker.parent ∧
    (Runner.run fuel s).frame.tracker.writes = s.tracker.writes ∧
    (Runner.run fuel s).frame.tracker.createdAccounts = s.tracker.createdAccounts ∧
    (Runner.run fuel s).frame.tracker.snapshots = s.tracker.snapshots :=
  Runner.SelfBalanceProgram.run_tracker_retained fuel s trace

example (s t : Frame.State) (run : Frame.selfBalance s = .continue t) :
    5 ≤ s.gas ∧ t.pc = s.pc + 1 ∧ t.gas = s.gas - 5 ∧
    t.stack.val = (Frame.SelfBalanceAccount s).balance :: s.stack.val ∧
    t.code = s.code ∧ t.memory = s.memory ∧ t.context = s.context ∧
    t.returnData = s.returnData ∧ t.tracker.parent = s.tracker.parent ∧
    t.tracker.writes = s.tracker.writes ∧
    t.tracker.accountReads = s.context.environment.currentTarget :: s.tracker.accountReads ∧
    t.tracker.storageReads = s.tracker.storageReads ∧
    t.tracker.createdAccounts = s.tracker.createdAccounts ∧
    t.tracker.snapshots = s.tracker.snapshots := by
  obtain ⟨gas, _, code, memory, pc, left, stack, context, ret, tracker, warmAddresses, warmSlots, static, stateGas⟩ :=
    (Frame.selfBalance_success_iff s t).mp run
  rw [tracker]
  exact ⟨gas, pc, left, stack, code, memory, context, ret, rfl, rfl, rfl, rfl, rfl, rfl⟩
