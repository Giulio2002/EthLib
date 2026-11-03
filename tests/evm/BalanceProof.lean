import EthLib.EVM.Proofs.Runner.Balance

open EthLib.EVM

example (s t : Frame.State) (run : Frame.balance s = .continue t) :
    ∃ (rest : Stack) (x : Word), s.stack.val = x :: rest.val ∧
      Frame.BalanceCost s (Frame.BalanceAddress x) ≤ s.gas ∧
      Frame.Advances { s with warmAddresses := Frame.BalanceWarm s (Frame.BalanceAddress x), tracker := Frame.BalanceRead s (Frame.BalanceAddress x) }
        t (s.pc + 1) (s.gas - Frame.BalanceCost s (Frame.BalanceAddress x))
        ((Frame.BalanceAccount s (Frame.BalanceAddress x)).balance :: rest.val) :=
  (Frame.balance_success_iff s t).mp run

example (s input : Frame.State) (reason : Frame.Exception)
    (run : Frame.balance s = .exception input reason) :
    (s.stack.val = [] ∧ input = s ∧ reason = .stackUnderflow) ∨
      (∃ (rest : Stack) (x : Word), s.stack.val = x :: rest.val ∧
        s.gas < Frame.BalanceCost s (Frame.BalanceAddress x) ∧
        input = { s with stack := rest, warmAddresses := Frame.BalanceWarm s (Frame.BalanceAddress x) } ∧
        reason = .outOfGas) :=
  (Frame.balance_exception_iff s input reason).mp run

example (s : Frame.State) (a b : World.Address) :
    b ∈ Frame.BalanceWarm s a ↔ b = a ∨ b ∈ s.warmAddresses :=
  Frame.balance_warm_membership s a b

example (s : Frame.State) (a : World.Address) :
    (a ∈ s.warmAddresses → Frame.BalanceCost s a = 100) ∧
    (a ∉ s.warmAddresses → Frame.BalanceCost s a = 3000) :=
  Frame.balance_cost_cases s a

example (s : Frame.State) (out : Frame.Outcome)
    (notBalance : ¬ Frame.At s (some .balance)) (rule : Frame.Rule s out) :
    out.frame.warmAddresses = s.warmAddresses :=
  Frame.outcome_warm_unchanged_of_not_balance notBalance rule

example (x : Word) (xs : List Word) (room : xs.length ≤ 1022) (g : Nat)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem)
    (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State)
    (warm : List World.Address) (warmSlots : List (World.Address × Word)) (cold : Frame.BalanceAddress x ∉ warm) :
    let s : Frame.State := ⟨Runner.BalanceProgram.program, 0, ⟨x :: x :: xs, by simp; omega⟩,
      3103 + g, mem, valid, context, returnData, tracker, warm, warmSlots⟩
    ∃ t, Runner.run 4 s = .stopped t ∧ t.pc = 4 ∧ t.gas = g ∧
      t.stack.val = (Frame.BalanceAccount s (Frame.BalanceAddress x)).balance ::
        (Frame.BalanceAccount s (Frame.BalanceAddress x)).balance :: xs ∧
      t.warmAddresses = Frame.BalanceAddress x :: warm ∧
      t.tracker = { tracker with accountReads := Frame.BalanceAddress x :: Frame.BalanceAddress x :: tracker.accountReads } ∧
      t.code = Runner.BalanceProgram.program ∧ t.memory = mem ∧ t.context = context ∧ t.returnData = returnData :=
  Runner.BalanceProgram.run x xs room g mem valid context returnData tracker warm warmSlots cold

example (fuel : Nat) (s : Frame.State) (a : World.Address) (warm : a ∈ s.warmAddresses) :
    a ∈ (Runner.run fuel s).frame.warmAddresses :=
  Runner.BalanceProgram.run_warm_monotone fuel s a warm

example (s : Frame.State) (empty : s.stack.val = []) :
    Frame.balance s = .exception s .stackUnderflow :=
  (Frame.balance_exception_iff s s .stackUnderflow).mpr (Or.inl ⟨empty, rfl, rfl⟩)

example (s : Frame.State) (rest : Stack) (x : Word)
    (items : s.stack.val = x :: rest.val)
    (low : s.gas < Frame.BalanceCost s (Frame.BalanceAddress x)) :
    Frame.balance s = .exception { s with stack := rest, warmAddresses := Frame.BalanceWarm s (Frame.BalanceAddress x) } .outOfGas :=
  (Frame.balance_exception_iff s _ _).mpr (Or.inr ⟨rest, x, items, low, rfl, rfl⟩)

example (s t : Frame.State) (rest : Stack) (x : Word)
    (items : s.stack.val = x :: rest.val)
    (gas : Frame.BalanceCost s (Frame.BalanceAddress x) ≤ s.gas)
    (fields : Frame.Advances { s with warmAddresses := Frame.BalanceWarm s (Frame.BalanceAddress x), tracker := Frame.BalanceRead s (Frame.BalanceAddress x) }
      t (s.pc + 1) (s.gas - Frame.BalanceCost s (Frame.BalanceAddress x))
      ((Frame.BalanceAccount s (Frame.BalanceAddress x)).balance :: rest.val)) :
    Frame.balance s = .continue t :=
  (Frame.balance_success_iff s t).mpr ⟨rest, x, items, gas, fields⟩

example (s : Frame.State) (a : World.Address) :
    (∀ x, (TransactionState.Reference.observe s.tracker).writes.accounts a = some x →
      Frame.BalanceAccount s a = x.getD World.emptyAccount) ∧
    ((TransactionState.Reference.observe s.tracker).writes.accounts a = none →
      Frame.BalanceAccount s a = ((TransactionState.Reference.observe s.tracker).parentAccounts a).getD World.emptyAccount) :=
  Frame.balance_account_value s a
