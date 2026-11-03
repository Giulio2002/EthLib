import EthLib.EVM.Proofs.NestedRunner
import EthLib.EVM.Proofs.CallPreparation

open EthLib.EVM

-- Downstream consumers can construct and eliminate the finite machine trace.
theorem nested_trace_forward (fuel : Nat) (m : NestedRunner.Machine) :
    NestedRunner.Trace fuel m (NestedRunner.run fuel m) :=
  NestedRunner.run_trace fuel m

theorem nested_trace_converse (fuel : Nat) (m : NestedRunner.Machine) (r : NestedRunner.Result)
    (h : NestedRunner.Trace fuel m r) : NestedRunner.run fuel m = r :=
  (NestedRunner.run_iff_trace fuel m r).mpr h

-- The constructed child receives the grant and preserves the checkpoint and static mode.
theorem nested_child_grant (p : CallPreparation.Prepared) :
    (NestedRunner.childFrame p).gas = p.childGas ∧
    (NestedRunner.childFrame p).stateGas.reservoir = p.stateGrant ∧
    (NestedRunner.childFrame p).tracker = TransactionState.snapshot p.parent.tracker ∧
    (NestedRunner.childFrame p).isStatic = p.parent.isStatic := by
  have h := NestedRunner.child_frame_fields p
  exact ⟨h.1, h.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

-- Exhausted child execution retains its callers and can resume with more fuel.
theorem nested_resume_after_exhaustion (fuel extra : Nat) (m next : NestedRunner.Machine)
    (h : NestedRunner.run fuel m = .exhausted next) :
    NestedRunner.run (fuel + extra) m = NestedRunner.run extra next := by
  rw [NestedRunner.run_add, h]

-- A successful value entry satisfies the independent checked-balance bound.
theorem nested_value_entry_balance_bound (p : CallPreparation.Prepared) (child : Frame.State)
    (hv : p.request.value ≠ 0) (h : NestedRunner.enterChild p = .ok child) :
    p.request.value.toNat ≤
      (TransactionAccount.selectedAccount
        (TransactionState.Reference.observe (TransactionState.snapshot p.parent.tracker))
        p.parent.context.environment.currentTarget).balance.toNat := by
  exact (NestedRunner.enterChild_transfer_refines p child hv h).1

-- An observed unchanged gas diagnostic determines the failed initial check.
theorem nested_initial_gas_converse (s : Frame.State) (r : Frame.CallRequest)
    (h : CallPreparation.prepare s r = .outOfGas s) :
    s.gas < (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
      (if r.value == 0 then 0 else 11300) +
      Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat :=
  (CallPreparation.initial_failure_iff s r).mp h

-- The same arithmetic condition constructs the actual diagnostic outcome.
theorem nested_initial_gas_forward (s : Frame.State) (r : Frame.CallRequest)
    (h : s.gas < (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
      (if r.value == 0 then 0 else 11300) +
      Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat) :
    CallPreparation.prepare s r = .outOfGas s :=
  (CallPreparation.initial_failure_iff s r).mpr h

-- A failed transfer exposes the insufficient balance and the retained read effect.
theorem nested_value_insufficient_observed (p : CallPreparation.Prepared) (child : Frame.State)
    (hv : p.request.value ≠ 0)
    (h : NestedRunner.enterChild p = .error (.insufficientBalance, child)) :
    (TransactionAccount.selectedAccount
      (TransactionState.Reference.observe (TransactionState.snapshot p.parent.tracker))
      p.parent.context.environment.currentTarget).balance.toNat < p.request.value.toNat ∧
    TransactionTracker.AccountReadEffect
      (TransactionState.Reference.observe (TransactionState.snapshot p.parent.tracker))
      (TransactionState.Reference.observe child.tracker)
      p.parent.context.environment.currentTarget :=
  NestedRunner.enterChild_insufficient_refines p child hv h

-- Observing a new-account refund recovers the meter relation and retained fields.
theorem nested_refund_observed (parent out : Frame.State)
    (h : NestedRunner.refundNewAccount parent true = out) :
    out.tracker = parent.tracker ∧ out.logs = parent.logs ∧
    out.memory = parent.memory ∧ out.warmAddresses = parent.warmAddresses ∧
    Gas.StateMeter.CreditEffect (Frame.stateMeter parent) (Frame.stateMeter out) 183600 := by
  have effect := (NestedRunner.refundNewAccount_iff parent out).mp h
  exact ⟨effect.2.2.2.2.2.2.1, effect.2.2.2.2.2.2.2.2.2.2.1,
    effect.2.2.2.1, effect.2.2.2.2.2.2.2.1, effect.2.2.2.2.2.2.2.2.2.2.2⟩

-- Independent field equations and the credit relation determine the result.
theorem nested_refund_constructed (parent out : Frame.State)
    (hcode : out.code = parent.code) (hpc : out.pc = parent.pc)
    (hstack : out.stack = parent.stack) (hmem : out.memory = parent.memory)
    (hctx : out.context = parent.context) (hdata : out.returnData = parent.returnData)
    (htracker : out.tracker = parent.tracker) (hwa : out.warmAddresses = parent.warmAddresses)
    (hws : out.warmSlots = parent.warmSlots) (hstatic : out.isStatic = parent.isStatic)
    (hlogs : out.logs = parent.logs)
    (hmeter : Gas.StateMeter.CreditEffect (Frame.stateMeter parent) (Frame.stateMeter out) 183600) :
    NestedRunner.refundNewAccount parent true = out :=
  (NestedRunner.refundNewAccount_iff parent out).mpr
    ⟨hcode, hpc, hstack, hmem, hctx, hdata, htracker, hwa, hws, hstatic, hlogs, hmeter⟩

-- Observed recipient overflow follows a sufficient sender balance and a checked addition failure.
theorem nested_value_overflow_observed (p : CallPreparation.Prepared) (child : Frame.State)
    (hv : p.request.value ≠ 0)
    (h : NestedRunner.enterChild p = .error (.recipientOverflow, child)) :
    p.request.value.toNat ≤
      (TransactionAccount.selectedAccount
        (TransactionState.Reference.observe (TransactionState.snapshot p.parent.tracker))
        p.parent.context.environment.currentTarget).balance.toNat ∧
    ∃ debit : TransactionState.Reference.View,
      Word.modulus ≤ (TransactionAccount.selectedAccount debit p.address).balance.toNat + p.request.value.toNat ∧
      TransactionTracker.AccountReadEffect debit (TransactionState.Reference.observe child.tracker) p.address :=
  by
    have effect := NestedRunner.enterChild_overflow_refines p child hv h
    obtain ⟨bound, debit, _, overflow, read⟩ := effect
    exact ⟨bound, debit, overflow, read⟩

-- Independent account and code maps construct the first missing-code diagnostic.
theorem nested_first_missing_constructed (s : Frame.State) (r : Frame.CallRequest)
    (hgas : (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
      (if r.value == 0 then 0 else 11300) +
      Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat ≤ s.gas)
    (hhash : (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
      (Frame.balanceAddress r.address)).codeHash ≠ World.emptyCodeHash)
    (hwrite : (TransactionState.Reference.observe s.tracker).writes.code
      (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
      (Frame.balanceAddress r.address)).codeHash = none)
    (hparent : (TransactionState.Reference.observe s.tracker).parentCode
      (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
      (Frame.balanceAddress r.address)).codeHash = none) :
    CallPreparation.prepare s r = .tooling { s with
      warmAddresses := if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses
        else Frame.balanceAddress r.address :: s.warmAddresses,
      tracker := { s.tracker with accountReads := Frame.balanceAddress r.address :: s.tracker.accountReads } } .missingCode :=
  CallPreparation.first_missing_forward s r hgas hhash hwrite hparent

-- A missing-code outcome recovers the original gas, hash, stores and diagnostic.
theorem preparation_missing_observed (s d : Frame.State) (r : Frame.CallRequest)
    (h : CallPreparation.prepare s r = .tooling d .missingCode) :
    (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
      (if r.value == 0 then 0 else 11300) +
      Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat ≤ s.gas ∧
    (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
      (Frame.balanceAddress r.address)).codeHash ≠ World.emptyCodeHash ∧
    (TransactionState.Reference.observe s.tracker).writes.code
      (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
      (Frame.balanceAddress r.address)).codeHash = none ∧
    (TransactionState.Reference.observe s.tracker).parentCode
      (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
      (Frame.balanceAddress r.address)).codeHash = none ∧
    d = { s with warmAddresses := if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses
      else Frame.balanceAddress r.address :: s.warmAddresses, tracker :=
        { s.tracker with accountReads := Frame.balanceAddress r.address :: s.tracker.accountReads } } :=
  (CallPreparation.missingCode_iff s d r).mp h

-- The delegation outcome recovers the selected code, its bytes and full diagnostic.
theorem preparation_delegation_observed (s d : Frame.State) (r : Frame.CallRequest)
    (h : CallPreparation.prepare s r = .tooling d .delegation) :
    ((if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
      (if r.value == 0 then 0 else 11300) +
      Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat ≤ s.gas) ∧
    ∃ code, CallPreparation.SelectedCode s r code ∧ code.size = 23 ∧
      code.data.toList.take 3 = [0xef, 0x01, 0x00] ∧
      d = { s with warmAddresses := if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses
        else Frame.balanceAddress r.address :: s.warmAddresses, tracker :=
          { s.tracker with accountReads := Frame.balanceAddress r.address :: s.tracker.accountReads } } := by
  obtain ⟨hg, code, hc, hd, hframe⟩ := (CallPreparation.delegation_iff s d r).mp h
  exact ⟨hg, code, hc, hd.1, hd.2, hframe⟩

-- Independent code and byte conditions construct the delegation diagnostic.
theorem preparation_delegation_constructed (s d : Frame.State) (r : Frame.CallRequest)
    (hg : (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
      (if r.value == 0 then 0 else 11300) +
      Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat ≤ s.gas)
    (code : ByteArray) (hc : CallPreparation.SelectedCode s r code)
    (hlen : code.size = 23) (hprefix : code.data.toList.take 3 = [0xef, 0x01, 0x00])
    (hframe : d = { s with warmAddresses := if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses
      else Frame.balanceAddress r.address :: s.warmAddresses, tracker :=
        { s.tracker with accountReads := Frame.balanceAddress r.address :: s.tracker.accountReads } }) :
    CallPreparation.prepare s r = .tooling d .delegation :=
  (CallPreparation.delegation_iff s d r).mpr ⟨hg, code, hc, ⟨hlen, hprefix⟩, hframe⟩

-- A later failure recovers non-delegated code, account creation and shortage.
theorem preparation_later_gas_observed (s d : Frame.State) (r : Frame.CallRequest)
    (hg : CallPreparation.Cost s r ≤ s.gas)
    (h : CallPreparation.prepare s r = .outOfGas d) :
    ∃ code, CallPreparation.SelectedCode s r code ∧ ¬ CallPreparation.Designator code ∧
      CallPreparation.NewAccount s r ∧
      s.stateGas.reservoir + (s.gas - CallPreparation.Cost s r) < 183600 ∧
      d = { s with gas := s.gas - CallPreparation.Cost s r, warmAddresses := if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses else Frame.balanceAddress r.address :: s.warmAddresses, tracker := { s.tracker with accountReads := Frame.balanceAddress r.address :: Frame.balanceAddress r.address :: Frame.balanceAddress r.address :: s.tracker.accountReads } } :=
  (CallPreparation.later_failure_iff s d r hg).mp h

-- Independent shortage conditions construct exactly that diagnostic.
theorem preparation_later_gas_constructed (s d : Frame.State) (r : Frame.CallRequest)
    (hg : CallPreparation.Cost s r ≤ s.gas) (code : ByteArray)
    (hc : CallPreparation.SelectedCode s r code) (hd : ¬ CallPreparation.Designator code)
    (hn : CallPreparation.NewAccount s r)
    (hf : s.stateGas.reservoir + (s.gas - CallPreparation.Cost s r) < 183600)
    (hframe : d = { s with gas := s.gas - CallPreparation.Cost s r, warmAddresses := if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses else Frame.balanceAddress r.address :: s.warmAddresses, tracker := { s.tracker with accountReads := Frame.balanceAddress r.address :: Frame.balanceAddress r.address :: Frame.balanceAddress r.address :: s.tracker.accountReads } }) :
    CallPreparation.prepare s r = .outOfGas d :=
  (CallPreparation.later_failure_iff s d r hg).mpr ⟨code, hc, hd, hn, hf, hframe⟩

-- Observed ready preparation selects affordable nondelegated code and preserves metadata.
theorem preparation_ready_observed (s : Frame.State) (r : Frame.CallRequest) (p : CallPreparation.Prepared)
    (h : CallPreparation.prepare s r = .ready p) :
    CallPreparation.Cost s r ≤ s.gas ∧ CallPreparation.SelectedCode s r p.code ∧
    ¬ CallPreparation.Designator p.code ∧ p.parent.tracker.parent = s.tracker.parent ∧
    p.parent.tracker.writes = s.tracker.writes ∧ p.parent.tracker.snapshots = s.tracker.snapshots := by
  obtain ⟨hg, hc, hd⟩ := CallPreparation.ready_conditions s r p h
  have fields := CallPreparation.ready_retained s r p h
  exact ⟨hg, hc, hd, fields.2.2.2.2.2.2.2.1, fields.2.2.2.2.2.2.2.2.1,
    fields.2.2.2.2.2.2.2.2.2.2.2.1⟩

-- The compatibility-only value-transfer tooling result has no preparation witness.
theorem preparation_no_value_tooling (s d : Frame.State) (r : Frame.CallRequest) :
    CallPreparation.prepare s r ≠ .tooling d .valueTransfer :=
  CallPreparation.valueTransfer_unreachable s d r


-- Eliminate the actual ready result into the independent complete field equations.
theorem preparation_ready_allfields (s : Frame.State) (r : Frame.CallRequest) (p : CallPreparation.Prepared)
    (h : CallPreparation.prepare s r = .ready p) :
  ∃ code : ByteArray, ∃ meter : Gas.StateMeter.Meter, ∃ forwarded : Nat,
    CallPreparation.Cost s r ≤ s.gas ∧ CallPreparation.SelectedCode s r code ∧ ¬ CallPreparation.Designator code ∧
    ((CallPreparation.NewAccount s r ∧ Gas.StateMeter.ChargeEffect (CallPreparation.InitialMeter s r) meter 183600) ∨
      (¬ CallPreparation.NewAccount s r ∧ meter = CallPreparation.InitialMeter s r)) ∧
    forwarded = min r.gas.toNat (meter.executionGas - meter.executionGas / 64) ∧
    p.request = r ∧ p.address = Frame.balanceAddress r.address ∧ p.code = code ∧
    p.childGas = forwarded + (if r.value.toNat = 0 then 0 else 2300) ∧
    p.stateGrant = meter.stateGas ∧ (p.newAccountCharged = true ↔ CallPreparation.NewAccount s r) ∧
    (p.insufficientBalance = true ↔
      (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
        s.context.environment.currentTarget).balance.toNat < r.value.toNat) ∧
    p.parent.code = s.code ∧ p.parent.pc = s.pc ∧ p.parent.stack = s.stack ∧
    p.parent.gas = meter.executionGas - forwarded ∧
    p.parent.memory.store = s.memory.store ∧
    p.parent.memory.words = max (max s.memory.words (Memory.Allocation.requiredWords r.inputOffset.toNat r.inputSize.toNat))
      (Memory.Allocation.requiredWords r.outputOffset.toNat r.outputSize.toNat) ∧
    p.parent.context = s.context ∧ p.parent.returnData = ByteArray.empty ∧
    p.parent.tracker = { s.tracker with accountReads := s.context.environment.currentTarget ::
      (if r.value = 0 then [Frame.balanceAddress r.address, Frame.balanceAddress r.address] ++ s.tracker.accountReads
      else [Frame.balanceAddress r.address, Frame.balanceAddress r.address, Frame.balanceAddress r.address] ++ s.tracker.accountReads) } ∧
    p.parent.warmAddresses = (if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses
      else Frame.balanceAddress r.address :: s.warmAddresses) ∧
    p.parent.warmSlots = s.warmSlots ∧ p.parent.isStatic = s.isStatic ∧
    p.parent.stateGas = ⟨0, meter.baseline, meter.refundCounter, meter.spilled, meter.committedSpill⟩ ∧
    p.parent.logs = s.logs := by
  have effect := (CallPreparation.prepare_iff s r (.ready p)).mp h
  change CallPreparation.ReadySpec s r p at effect
  obtain ⟨code, meter, forwarded, hgas, hcode, hdesign, hmeter, hforward, hrequest,
    haddress, hbytes, hchild, hgrant, hnew, hbalance, hframecode, hpc, hstack, hframegas,
    hstore, hwords, hcontext, hdata, htracker, hwarm, hslots, hstatic, hstate, hlogs⟩ := effect
  exact ⟨code, meter, forwarded, hgas, hcode, hdesign, hmeter, hforward, hrequest,
    haddress, hbytes, hchild, hgrant, hnew, hbalance, hframecode, hpc, hstack, hframegas,
    hstore, hwords, hcontext, hdata, htracker, hwarm, hslots, hstatic, hstate, hlogs⟩

-- Independent field equations construct an actual ready result through the global iff.
theorem preparation_ready_constructed (s : Frame.State) (r : Frame.CallRequest) (p : CallPreparation.Prepared)
    (fields :
  ∃ code : ByteArray, ∃ meter : Gas.StateMeter.Meter, ∃ forwarded : Nat,
    CallPreparation.Cost s r ≤ s.gas ∧ CallPreparation.SelectedCode s r code ∧ ¬ CallPreparation.Designator code ∧
    ((CallPreparation.NewAccount s r ∧ Gas.StateMeter.ChargeEffect (CallPreparation.InitialMeter s r) meter 183600) ∨
      (¬ CallPreparation.NewAccount s r ∧ meter = CallPreparation.InitialMeter s r)) ∧
    forwarded = min r.gas.toNat (meter.executionGas - meter.executionGas / 64) ∧
    p.request = r ∧ p.address = Frame.balanceAddress r.address ∧ p.code = code ∧
    p.childGas = forwarded + (if r.value.toNat = 0 then 0 else 2300) ∧
    p.stateGrant = meter.stateGas ∧ (p.newAccountCharged = true ↔ CallPreparation.NewAccount s r) ∧
    (p.insufficientBalance = true ↔
      (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
        s.context.environment.currentTarget).balance.toNat < r.value.toNat) ∧
    p.parent.code = s.code ∧ p.parent.pc = s.pc ∧ p.parent.stack = s.stack ∧
    p.parent.gas = meter.executionGas - forwarded ∧
    p.parent.memory.store = s.memory.store ∧
    p.parent.memory.words = max (max s.memory.words (Memory.Allocation.requiredWords r.inputOffset.toNat r.inputSize.toNat))
      (Memory.Allocation.requiredWords r.outputOffset.toNat r.outputSize.toNat) ∧
    p.parent.context = s.context ∧ p.parent.returnData = ByteArray.empty ∧
    p.parent.tracker = { s.tracker with accountReads := s.context.environment.currentTarget ::
      (if r.value = 0 then [Frame.balanceAddress r.address, Frame.balanceAddress r.address] ++ s.tracker.accountReads
      else [Frame.balanceAddress r.address, Frame.balanceAddress r.address, Frame.balanceAddress r.address] ++ s.tracker.accountReads) } ∧
    p.parent.warmAddresses = (if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses
      else Frame.balanceAddress r.address :: s.warmAddresses) ∧
    p.parent.warmSlots = s.warmSlots ∧ p.parent.isStatic = s.isStatic ∧
    p.parent.stateGas = ⟨0, meter.baseline, meter.refundCounter, meter.spilled, meter.committedSpill⟩ ∧
    p.parent.logs = s.logs) : CallPreparation.prepare s r = .ready p := by
  apply (CallPreparation.prepare_iff s r (.ready p)).mpr
  change CallPreparation.ReadySpec s r p
  obtain ⟨code, meter, forwarded, hgas, hcode, hdesign, hmeter, hforward, hrequest,
    haddress, hbytes, hchild, hgrant, hnew, hbalance, hframecode, hpc, hstack, hframegas,
    hstore, hwords, hcontext, hdata, htracker, hwarm, hslots, hstatic, hstate, hlogs⟩ := fields
  exact ⟨code, meter, forwarded, hgas, hcode, hdesign, hmeter, hforward, hrequest,
    haddress, hbytes, hchild, hgrant, hnew, hbalance, hframecode, hpc, hstack, hframegas,
    hstore, hwords, hcontext, hdata, htracker, hwarm, hslots, hstatic, hstate, hlogs⟩

-- An observed zero-value entry exposes the exact snapshot and operand-bound input bytes.
theorem nested_zero_entry_observed (p : CallPreparation.Prepared) (out : Frame.State)
    (hv : p.request.value = 0) (h : NestedRunner.enterChild p = .ok out) :
    Frame.FinishBytes p.parent p.request.inputOffset p.request.inputSize out.context.data ∧
    out.tracker.writes = p.parent.tracker.writes ∧
    out.tracker.snapshots = p.parent.tracker.writes :: p.parent.tracker.snapshots ∧
    out.logs = [] ∧ out.stateGas.reservoir = p.stateGrant ∧ out.stateGas.baseline = p.stateGrant := by
  have effect := (NestedRunner.zeroEntry_iff p out hv).mp h
  obtain ⟨_, _, _, _, _, _, _, _, hbytes, _, hwrites, _, _, _, hsnap, _, _, _, hstate, hlogs⟩ := effect
  exact ⟨hbytes, hwrites, hsnap, hlogs, congrArg Frame.StateGas.reservoir hstate,
    congrArg Frame.StateGas.baseline hstate⟩

-- Independent complete child fields reconstruct the zero-value result.
theorem nested_zero_entry_constructed (p : CallPreparation.Prepared) (out : Frame.State)
    (hv : p.request.value = 0)
    (hc : out.code = p.code) (hpc : out.pc = 0) (hstack : out.stack = Stack.empty)
    (hgas : out.gas = p.childGas) (hmem : out.memory = Memory.Allocation.empty)
    (hreturn : out.returnData = ByteArray.empty)
    (henv : out.context.environment = { p.parent.context.environment with currentTarget := p.address, caller := p.parent.context.environment.currentTarget, value := p.request.value })
    (hbytes : Frame.FinishBytes p.parent p.request.inputOffset p.request.inputSize out.context.data)
    (hparent : out.tracker.parent = p.parent.tracker.parent) (hwrites : out.tracker.writes = p.parent.tracker.writes)
    (hareads : out.tracker.accountReads = p.parent.tracker.accountReads)
    (hsreads : out.tracker.storageReads = p.parent.tracker.storageReads)
    (hcreated : out.tracker.createdAccounts = p.parent.tracker.createdAccounts)
    (hsnap : out.tracker.snapshots = p.parent.tracker.writes :: p.parent.tracker.snapshots)
    (hwarm : out.warmAddresses = p.parent.warmAddresses) (hslots : out.warmSlots = p.parent.warmSlots)
    (hstatic : out.isStatic = p.parent.isStatic)
    (hmeter : out.stateGas = ⟨p.stateGrant, p.stateGrant, 0, 0, 0⟩) (hlogs : out.logs = []) :
    NestedRunner.enterChild p = .ok out :=
  (NestedRunner.zeroEntry_iff p out hv).mpr ⟨hv, hc, hpc, hstack, hgas, hmem, hreturn, henv,
    hbytes, hparent, hwrites, hareads, hsreads, hcreated, hsnap, hwarm, hslots, hstatic, hmeter, hlogs⟩

-- With stack room, a continuation error recovers precisely the failing checkpoint conditions.
theorem nested_resume_invalid_observed (c : NestedRunner.Continuation) (child : Frame.State)
    (success : Bool) (gas : Nat) (output : ByteArray) (rest : List NestedRunner.Continuation)
    (hroom : c.parent.stack.val.length < 1024)
    (h : NestedRunner.resume c child success gas output rest = .done (.tooling child .invalidContinuation)) :
    child.stateGas.committedSpill ≠ 0 ∨ child.tracker.snapshots = [] :=
  (NestedRunner.resume_invalid_checkpoint_iff c child success gas output rest hroom).mp h

-- A failed checkpoint constructs the corresponding continuation diagnostic.
theorem nested_resume_invalid_constructed (c : NestedRunner.Continuation) (child : Frame.State)
    (success : Bool) (gas : Nat) (output : ByteArray) (rest : List NestedRunner.Continuation)
    (hroom : c.parent.stack.val.length < 1024)
    (h : child.stateGas.committedSpill ≠ 0 ∨ child.tracker.snapshots = []) :
    NestedRunner.resume c child success gas output rest = .done (.tooling child .invalidContinuation) :=
  (NestedRunner.resume_invalid_checkpoint_iff c child success gas output rest hroom).mpr h


-- Recover every independent continuation field from the actual machine transition.
theorem nested_resume_allfields (c : NestedRunner.Continuation) (child : Frame.State) (success : Bool)
    (gas : Nat) (output : ByteArray) (rest : List NestedRunner.Continuation) (out : NestedRunner.Machine)
    (h : NestedRunner.resume c child success gas output rest = .next out) :
  ∃ incorporated credited : Frame.State,
    ChildSettlement.Effect c.parent child incorporated success gas output ∧
    NestedRunner.RefundSpec success c.newAccountCharged incorporated credited ∧
    credited.stack.val.length < 1024 ∧
    out.depth = c.depth ∧ out.callers = rest ∧
    out.frame.code = credited.code ∧ out.frame.pc = credited.pc + 1 ∧
    out.frame.stack.val = (if success then 1 else 0) :: credited.stack.val ∧
    out.frame.gas = credited.gas ∧
    out.frame.memory.store = List.zip
      (List.range' c.request.outputOffset.toNat (output.data.toList.take c.request.outputSize.toNat).length)
      (output.data.toList.take c.request.outputSize.toNat) ++ credited.memory.store ∧
    out.frame.memory.words = max credited.memory.words
      (Memory.Allocation.requiredWords c.request.outputOffset.toNat (output.data.toList.take c.request.outputSize.toNat).length) ∧
    out.frame.context = credited.context ∧ out.frame.returnData = credited.returnData ∧
    out.frame.tracker = credited.tracker ∧ out.frame.warmAddresses = credited.warmAddresses ∧
    out.frame.warmSlots = credited.warmSlots ∧ out.frame.isStatic = credited.isStatic ∧
    out.frame.stateGas = credited.stateGas ∧ out.frame.logs = credited.logs := by
  have effect := (NestedRunner.resume_success_iff c child success gas output rest out).mp h
  obtain ⟨incorporated, credited, hsettle, hcredit, hroom, hdepth, hcallers, hcode, hpc, hstack, hgas, hstore, hwords, hcontext, hdata, htracker, hwarm, hslots, hstatic, hstate, hlogs⟩ := effect
  exact ⟨incorporated, credited, hsettle, hcredit, hroom, hdepth, hcallers, hcode, hpc, hstack, hgas, hstore, hwords, hcontext, hdata, htracker, hwarm, hslots, hstatic, hstate, hlogs⟩

-- Independent incorporation, refund, stack, memory and field conditions construct the transition.
theorem nested_resume_constructed (c : NestedRunner.Continuation) (child : Frame.State) (success : Bool)
    (gas : Nat) (output : ByteArray) (rest : List NestedRunner.Continuation) (out : NestedRunner.Machine)
    (fields :
  ∃ incorporated credited : Frame.State,
    ChildSettlement.Effect c.parent child incorporated success gas output ∧
    NestedRunner.RefundSpec success c.newAccountCharged incorporated credited ∧
    credited.stack.val.length < 1024 ∧
    out.depth = c.depth ∧ out.callers = rest ∧
    out.frame.code = credited.code ∧ out.frame.pc = credited.pc + 1 ∧
    out.frame.stack.val = (if success then 1 else 0) :: credited.stack.val ∧
    out.frame.gas = credited.gas ∧
    out.frame.memory.store = List.zip
      (List.range' c.request.outputOffset.toNat (output.data.toList.take c.request.outputSize.toNat).length)
      (output.data.toList.take c.request.outputSize.toNat) ++ credited.memory.store ∧
    out.frame.memory.words = max credited.memory.words
      (Memory.Allocation.requiredWords c.request.outputOffset.toNat (output.data.toList.take c.request.outputSize.toNat).length) ∧
    out.frame.context = credited.context ∧ out.frame.returnData = credited.returnData ∧
    out.frame.tracker = credited.tracker ∧ out.frame.warmAddresses = credited.warmAddresses ∧
    out.frame.warmSlots = credited.warmSlots ∧ out.frame.isStatic = credited.isStatic ∧
    out.frame.stateGas = credited.stateGas ∧ out.frame.logs = credited.logs) : NestedRunner.resume c child success gas output rest = .next out := by
  apply (NestedRunner.resume_success_iff c child success gas output rest out).mpr
  obtain ⟨incorporated, credited, hsettle, hcredit, hroom, hdepth, hcallers, hcode, hpc, hstack, hgas, hstore, hwords, hcontext, hdata, htracker, hwarm, hslots, hstatic, hstate, hlogs⟩ := fields
  exact ⟨incorporated, credited, hsettle, hcredit, hroom, hdepth, hcallers, hcode, hpc, hstack, hgas, hstore, hwords, hcontext, hdata, htracker, hwarm, hslots, hstatic, hstate, hlogs⟩

-- An observed continuation diagnostic exposes checkpoint failure or a full credited stack.
theorem nested_resume_failure_observed (c : NestedRunner.Continuation) (child : Frame.State)
    (success : Bool) (gas : Nat) (output : ByteArray) (rest : List NestedRunner.Continuation)
    (diagnostic : Frame.State)
    (h : NestedRunner.resume c child success gas output rest = .done (.tooling diagnostic .invalidContinuation)) :
    (diagnostic = child ∧ (child.stateGas.committedSpill ≠ 0 ∨
      (child.stateGas.committedSpill = 0 ∧ child.tracker.snapshots = []))) ∨
    ∃ incorporated credited : Frame.State,
      ChildSettlement.Effect c.parent child incorporated success gas output ∧
      NestedRunner.RefundSpec success c.newAccountCharged incorporated credited ∧
      credited.stack.val.length = 1024 ∧ diagnostic = credited := by
  have effect := (NestedRunner.resume_failure_iff c child success gas output rest diagnostic).mp h
  rcases effect with ⟨hframe, hreason⟩ | ⟨incorporated, credited, hsettle, hrefund, hfull, hframe⟩
  · exact Or.inl ⟨hframe, hreason⟩
  · exact Or.inr ⟨incorporated, credited, hsettle, hrefund, hfull, hframe⟩

-- Independent checkpoint or full-stack conditions construct the diagnostic.
theorem nested_resume_failure_constructed (c : NestedRunner.Continuation) (child : Frame.State)
    (success : Bool) (gas : Nat) (output : ByteArray) (rest : List NestedRunner.Continuation)
    (diagnostic : Frame.State)
    (h : (diagnostic = child ∧ (child.stateGas.committedSpill ≠ 0 ∨
      (child.stateGas.committedSpill = 0 ∧ child.tracker.snapshots = []))) ∨
    ∃ incorporated credited : Frame.State,
      ChildSettlement.Effect c.parent child incorporated success gas output ∧
      NestedRunner.RefundSpec success c.newAccountCharged incorporated credited ∧
      credited.stack.val.length = 1024 ∧ diagnostic = credited) :
    NestedRunner.resume c child success gas output rest = .done (.tooling diagnostic .invalidContinuation) := by
  apply (NestedRunner.resume_failure_iff c child success gas output rest diagnostic).mpr
  rcases h with ⟨hframe, hreason⟩ | ⟨incorporated, credited, hsettle, hrefund, hfull, hframe⟩
  · exact Or.inl ⟨hframe, hreason⟩
  · exact Or.inr ⟨incorporated, credited, hsettle, hrefund, hfull, hframe⟩

-- A nonzero successful entry exposes both checked account modifications and event selection.
theorem nested_entry_value_observed (p : CallPreparation.Prepared) (child : Frame.State)
    (hv : p.request.value ≠ 0) (h : NestedRunner.enterChild p = .ok child) :
    ∃ checkpoint debit : TransactionState.State,
      NestedRunner.CheckpointExact p.parent.tracker checkpoint ∧ NestedRunner.EntryShape p child ∧
      p.request.value.toNat ≤ (TransactionAccount.selectedAccount (TransactionState.Reference.observe checkpoint)
        p.parent.context.environment.currentTarget).balance.toNat ∧
      NestedRunner.BalanceEffect checkpoint debit p.parent.context.environment.currentTarget (BitVec.ofNat 256
        ((TransactionAccount.selectedAccount (TransactionState.Reference.observe checkpoint)
          p.parent.context.environment.currentTarget).balance.toNat - p.request.value.toNat)) ∧
      (TransactionAccount.selectedAccount (TransactionState.Reference.observe debit) p.address).balance.toNat + p.request.value.toNat < Word.modulus ∧
      NestedRunner.BalanceEffect debit child.tracker p.address (BitVec.ofNat 256
        ((TransactionAccount.selectedAccount (TransactionState.Reference.observe debit) p.address).balance.toNat + p.request.value.toNat)) ∧
      child.logs = NestedRunner.EntryLog p := by
  have effect := (NestedRunner.entry_iff p (.ok child)).mp h
  change ∃ checkpoint, NestedRunner.CheckpointExact p.parent.tracker checkpoint ∧ NestedRunner.EntryShape p child ∧
    ((p.request.value = 0 ∧ child.tracker = checkpoint ∧ child.logs = []) ∨
      (p.request.value ≠ 0 ∧ NestedRunner.ExactTransfer checkpoint p.parent.context.environment.currentTarget p.address p.request.value (.ok child.tracker) ∧ child.logs = NestedRunner.EntryLog p)) at effect
  obtain ⟨checkpoint, hsave, hshape, branch⟩ := effect
  rcases branch with ⟨hz, _, _⟩ | ⟨_, hmove, hlogs⟩
  · exact False.elim (hv hz)
  · change _ ∧ ∃ _, _ at hmove
    obtain ⟨hbound, debit, hdebit, hcredit, hfinal⟩ := hmove
    exact ⟨checkpoint, debit, hsave, hshape, hbound, hdebit, hcredit, hfinal, hlogs⟩

-- Checked transfer failures expose the exact read history and preserve the child shape.
theorem nested_entry_insufficient_observed (p : CallPreparation.Prepared) (child : Frame.State)
    (h : NestedRunner.enterChild p = .error (.insufficientBalance, child)) :
    ∃ checkpoint, NestedRunner.CheckpointExact p.parent.tracker checkpoint ∧ NestedRunner.EntryShape p child ∧
      p.request.value ≠ 0 ∧
      (TransactionAccount.selectedAccount (TransactionState.Reference.observe checkpoint)
        p.parent.context.environment.currentTarget).balance.toNat < p.request.value.toNat ∧
      NestedRunner.ReadExact checkpoint child.tracker p.parent.context.environment.currentTarget ∧ child.logs = [] := by
  have effect := (NestedRunner.entry_iff p (.error (.insufficientBalance, child))).mp h
  change ∃ checkpoint, NestedRunner.CheckpointExact p.parent.tracker checkpoint ∧ NestedRunner.EntryShape p child ∧
    p.request.value ≠ 0 ∧
    ((TransactionAccount.selectedAccount (TransactionState.Reference.observe checkpoint)
      p.parent.context.environment.currentTarget).balance.toNat < p.request.value.toNat ∧
      NestedRunner.ReadExact checkpoint child.tracker p.parent.context.environment.currentTarget) ∧ child.logs = [] at effect
  obtain ⟨checkpoint, hsave, hshape, hv, ⟨hbalance, hread⟩, hlogs⟩ := effect
  exact ⟨checkpoint, hsave, hshape, hv, hbalance, hread, hlogs⟩

-- A diagnostic can be constructed from independent checkpoint and transfer conditions.
theorem nested_entry_error_constructed (p : CallPreparation.Prepared) (reason : TransactionTransfer.TransferError)
    (child : Frame.State) (checkpoint : TransactionState.State)
    (hsave : NestedRunner.CheckpointExact p.parent.tracker checkpoint) (hshape : NestedRunner.EntryShape p child)
    (hv : p.request.value ≠ 0)
    (htransfer : NestedRunner.ExactTransfer checkpoint p.parent.context.environment.currentTarget p.address p.request.value (.error (reason, child.tracker)))
    (hlogs : child.logs = []) : NestedRunner.enterChild p = .error (reason, child) := by
  apply (NestedRunner.entry_iff p (.error (reason, child))).mpr
  exact ⟨checkpoint, hsave, hshape, hv, htransfer, hlogs⟩

-- Independent nonzero transfer and event equations construct child entry.
theorem nested_entry_value_constructed (p : CallPreparation.Prepared) (child : Frame.State)
    (checkpoint : TransactionState.State) (hsave : NestedRunner.CheckpointExact p.parent.tracker checkpoint)
    (hshape : NestedRunner.EntryShape p child) (hv : p.request.value ≠ 0)
    (htransfer : NestedRunner.ExactTransfer checkpoint p.parent.context.environment.currentTarget p.address p.request.value (.ok child.tracker))
    (hlogs : child.logs = NestedRunner.EntryLog p) : NestedRunner.enterChild p = .ok child := by
  apply (NestedRunner.entry_iff p (.ok child)).mpr
  exact ⟨checkpoint, hsave, hshape, Or.inr ⟨hv, htransfer, hlogs⟩⟩

-- Observed overflow recovers the debit, checked recipient bound and exact read history.
theorem nested_entry_overflow_observed (p : CallPreparation.Prepared) (child : Frame.State)
    (h : NestedRunner.enterChild p = .error (.recipientOverflow, child)) :
    ∃ checkpoint debit : TransactionState.State,
      NestedRunner.CheckpointExact p.parent.tracker checkpoint ∧ NestedRunner.EntryShape p child ∧
      p.request.value ≠ 0 ∧
      p.request.value.toNat ≤ (TransactionAccount.selectedAccount (TransactionState.Reference.observe checkpoint)
        p.parent.context.environment.currentTarget).balance.toNat ∧
      NestedRunner.BalanceEffect checkpoint debit p.parent.context.environment.currentTarget (BitVec.ofNat 256
        ((TransactionAccount.selectedAccount (TransactionState.Reference.observe checkpoint)
          p.parent.context.environment.currentTarget).balance.toNat - p.request.value.toNat)) ∧
      Word.modulus ≤ (TransactionAccount.selectedAccount (TransactionState.Reference.observe debit) p.address).balance.toNat + p.request.value.toNat ∧
      NestedRunner.ReadExact debit child.tracker p.address ∧ child.logs = [] := by
  have effect := (NestedRunner.entry_iff p (.error (.recipientOverflow, child))).mp h
  change ∃ checkpoint, NestedRunner.CheckpointExact p.parent.tracker checkpoint ∧ NestedRunner.EntryShape p child ∧
    p.request.value ≠ 0 ∧
    (p.request.value.toNat ≤ (TransactionAccount.selectedAccount (TransactionState.Reference.observe checkpoint)
      p.parent.context.environment.currentTarget).balance.toNat ∧
      ∃ debit, NestedRunner.BalanceEffect checkpoint debit p.parent.context.environment.currentTarget (BitVec.ofNat 256
        ((TransactionAccount.selectedAccount (TransactionState.Reference.observe checkpoint)
          p.parent.context.environment.currentTarget).balance.toNat - p.request.value.toNat)) ∧
      Word.modulus ≤ (TransactionAccount.selectedAccount (TransactionState.Reference.observe debit) p.address).balance.toNat + p.request.value.toNat ∧
      NestedRunner.ReadExact debit child.tracker p.address) ∧ child.logs = [] at effect
  obtain ⟨checkpoint, hsave, hshape, hv, ⟨hbound, debit, hdebit, hover, hread⟩, hlogs⟩ := effect
  exact ⟨checkpoint, debit, hsave, hshape, hv, hbound, hdebit, hover, hread, hlogs⟩

-- An actual successful continuation exposes the committed tracker, logs, warmth and output.
theorem nested_resume_commit_observed (c : NestedRunner.Continuation) (child : Frame.State)
    (gas : Nat) (output : ByteArray) (rest : List NestedRunner.Continuation) (out : NestedRunner.Machine)
    (h : NestedRunner.resume c child true gas output rest = .next out) :
    ∃ saved tail, child.stateGas.committedSpill = 0 ∧ child.tracker.snapshots = saved :: tail ∧
      out.frame.tracker.parent = child.tracker.parent ∧ out.frame.tracker.writes = child.tracker.writes ∧
      out.frame.tracker.accountReads = child.tracker.accountReads ∧ out.frame.tracker.storageReads = child.tracker.storageReads ∧
      out.frame.tracker.createdAccounts = child.tracker.createdAccounts ∧ out.frame.tracker.snapshots = tail ∧
      out.frame.logs = c.parent.logs ++ child.logs ∧
      out.frame.warmAddresses = child.warmAddresses ++ c.parent.warmAddresses ∧
      out.frame.warmSlots = child.warmSlots ++ c.parent.warmSlots ∧ out.frame.returnData = output ∧
      out.frame.stack.val = 1 :: c.parent.stack.val ∧ out.frame.pc = c.parent.pc + 1 := by
  have effect := (NestedRunner.resume_success_iff c child true gas output rest out).mp h
  rcases effect with ⟨inc, credited, hsettle, hrefund, _, _, _, _, hpc, hstack, _, _, _, _, hdata, htracker, hwarm, hslots, _, _, hlogs⟩
  simp [NestedRunner.RefundSpec] at hrefund
  subst credited
  rcases hsettle with ⟨saved, tail, hspill, hsnap, hfields⟩
  simp only [↓reduceIte] at hfields
  rcases hfields with ⟨_, hincpc, hincstack, _, _, hincdata, _, hparent, hwrites, hareads,
    hsreads, hcreated, hsnaps, hinclogs, hincwarm, hincslots, _⟩
  refine ⟨saved, tail, hspill, hsnap, ?_⟩
  simp_all

-- A failed child continuation recovers saved writes and retains child read diagnostics.
theorem nested_resume_rollback_observed (c : NestedRunner.Continuation) (child : Frame.State)
    (gas : Nat) (output : ByteArray) (rest : List NestedRunner.Continuation) (out : NestedRunner.Machine)
    (h : NestedRunner.resume c child false gas output rest = .next out) :
    ∃ saved tail, child.stateGas.committedSpill = 0 ∧ child.tracker.snapshots = saved :: tail ∧
      out.frame.tracker.parent = child.tracker.parent ∧ out.frame.tracker.writes = saved ∧
      out.frame.tracker.accountReads = child.tracker.accountReads ∧ out.frame.tracker.storageReads = child.tracker.storageReads ∧
      out.frame.tracker.createdAccounts = child.tracker.createdAccounts ∧ out.frame.tracker.snapshots = tail ∧
      out.frame.logs = c.parent.logs ∧ out.frame.warmAddresses = c.parent.warmAddresses ∧
      out.frame.warmSlots = c.parent.warmSlots ∧ out.frame.returnData = output ∧
      out.frame.stack.val = 0 :: c.parent.stack.val ∧ out.frame.pc = c.parent.pc + 1 := by
  have effect := (NestedRunner.resume_success_iff c child false gas output rest out).mp h
  rcases effect with ⟨inc, credited, hsettle, hrefund, _, _, _, _, hpc, hstack, _, _, _, _, hdata, htracker, hwarm, hslots, _, _, hlogs⟩
  have hretain := NestedRunner.refund_spec_retained false c.newAccountCharged inc credited hrefund
  rcases hretain with ⟨_, hcreditpc, hcreditstack, _, _, hcreditdata, hcredittracker,
    hcreditwarm, hcreditslots, _, hcreditlogs⟩
  rcases hsettle with ⟨saved, tail, hspill, hsnap, hfields⟩
  simp only [Bool.false_eq_true, ↓reduceIte] at hfields
  rcases hfields with ⟨_, hincpc, hincstack, _, _, hincdata, _, hparent, hwrites, hareads,
    hsreads, hcreated, hsnaps, hinclogs, hincwarm, hincslots, _⟩
  refine ⟨saved, tail, hspill, hsnap, ?_⟩
  simp_all

-- An observed self-transfer emits no EIP-7708 event.
theorem nested_entry_self_log (p : CallPreparation.Prepared) (child : Frame.State)
    (hv : p.request.value ≠ 0) (hself : p.parent.context.environment.currentTarget = p.address)
    (h : NestedRunner.enterChild p = .ok child) : child.logs = [] := by
  obtain ⟨_, _, _, _, _, _, _, _, hlogs⟩ := nested_entry_value_observed p child hv h
  simpa [NestedRunner.EntryLog, hself] using hlogs

-- An observed distinct-address transfer emits the source event with all three topics.
theorem nested_entry_distinct_log (p : CallPreparation.Prepared) (child : Frame.State)
    (hv : p.request.value ≠ 0) (hdistinct : p.parent.context.environment.currentTarget ≠ p.address)
    (h : NestedRunner.enterChild p = .ok child) :
    child.logs = [⟨⟨2 ^ 160 - 2, by decide⟩,
      [Frame.logTopic (World.codeHash "Transfer(address,address,uint256)".toUTF8),
       Frame.logTopic (Environment.addressWord p.parent.context.environment.currentTarget),
       Frame.logTopic (Environment.addressWord p.address)], p.request.value.toBytesBE⟩] := by
  obtain ⟨_, _, _, _, _, _, _, _, hlogs⟩ := nested_entry_value_observed p child hv h
  simpa [NestedRunner.EntryLog, hdistinct] using hlogs

-- An actual exceptional child continuation rolls back and returns empty data.
theorem nested_exceptional_child_observed (c : NestedRunner.Continuation) (child : Frame.State)
    (reason : Frame.Exception) (rest : List NestedRunner.Continuation) (out : NestedRunner.Machine)
    (h : NestedRunner.exceptional child reason (c :: rest) = .next out) :
    ∃ saved tail, child.stateGas.committedSpill = 0 ∧ child.tracker.snapshots = saved :: tail ∧
      out.frame.tracker.writes = saved ∧ out.frame.tracker.accountReads = child.tracker.accountReads ∧
      out.frame.tracker.storageReads = child.tracker.storageReads ∧ out.frame.logs = c.parent.logs ∧
      out.frame.returnData = ByteArray.empty ∧ out.frame.stack.val = 0 :: c.parent.stack.val := by
  have hresume : NestedRunner.resume c child false 0 ByteArray.empty rest = .next out := by
    simpa [NestedRunner.exceptional] using h
  obtain ⟨saved, tail, hspill, hsnap, _, hwrites, hareads, hsreads, _, _, hlogs, _, _, hdata, hstack, _⟩ :=
    nested_resume_rollback_observed c child 0 ByteArray.empty rest out hresume
  exact ⟨saved, tail, hspill, hsnap, hwrites, hareads, hsreads, hlogs, hdata, hstack⟩

-- Arithmetic and both duplicate-preserving balance effects construct a nonzero entry.
theorem nested_entry_value_from_fields (p : CallPreparation.Prepared) (child : Frame.State)
    (checkpoint debit : TransactionState.State) (hsave : NestedRunner.CheckpointExact p.parent.tracker checkpoint)
    (hshape : NestedRunner.EntryShape p child) (hv : p.request.value ≠ 0)
    (hbound : p.request.value.toNat ≤ (TransactionAccount.selectedAccount (TransactionState.Reference.observe checkpoint)
      p.parent.context.environment.currentTarget).balance.toNat)
    (hdebit : NestedRunner.BalanceEffect checkpoint debit p.parent.context.environment.currentTarget (BitVec.ofNat 256
      ((TransactionAccount.selectedAccount (TransactionState.Reference.observe checkpoint)
        p.parent.context.environment.currentTarget).balance.toNat - p.request.value.toNat)))
    (hcredit : (TransactionAccount.selectedAccount (TransactionState.Reference.observe debit) p.address).balance.toNat + p.request.value.toNat < Word.modulus)
    (hfinal : NestedRunner.BalanceEffect debit child.tracker p.address (BitVec.ofNat 256
      ((TransactionAccount.selectedAccount (TransactionState.Reference.observe debit) p.address).balance.toNat + p.request.value.toNat)))
    (hlogs : child.logs = NestedRunner.EntryLog p) : NestedRunner.enterChild p = .ok child := by
  apply nested_entry_value_constructed p child checkpoint hsave hshape hv
  · exact ⟨hbound, debit, hdebit, hcredit, hfinal⟩
  · exact hlogs

-- An observed output copy overwrites only the requested prefix and leaves other bytes intact.
theorem nested_resume_byte_observed (c : NestedRunner.Continuation) (child : Frame.State)
    (success : Bool) (gas : Nat) (output : ByteArray) (rest : List NestedRunner.Continuation)
    (out : NestedRunner.Machine) (h : NestedRunner.resume c child success gas output rest = .next out) :
    ∃ incorporated credited : Frame.State,
      ChildSettlement.Effect c.parent child incorporated success gas output ∧
      NestedRunner.RefundSpec success c.newAccountCharged incorporated credited ∧
      ∀ q, Memory.readByte out.frame.memory.store q =
        if hq : c.request.outputOffset.toNat ≤ q ∧
          q < c.request.outputOffset.toNat + (output.data.toList.take c.request.outputSize.toNat).length then
          (output.data.toList.take c.request.outputSize.toNat)[q - c.request.outputOffset.toNat]'(by omega)
        else Memory.readByte credited.memory.store q := by
  obtain ⟨incorporated, credited, hsettle, hrefund, hbytes⟩ :=
    NestedRunner.resume_success_bytes c child success gas output rest out h
  exact ⟨incorporated, credited, hsettle, hrefund, hbytes⟩

-- Insufficient balance and the exact first read construct the entry error.
theorem nested_entry_insufficient_constructed (p : CallPreparation.Prepared) (child : Frame.State)
    (checkpoint : TransactionState.State) (hsave : NestedRunner.CheckpointExact p.parent.tracker checkpoint)
    (hshape : NestedRunner.EntryShape p child) (hv : p.request.value ≠ 0)
    (hbalance : (TransactionAccount.selectedAccount (TransactionState.Reference.observe checkpoint)
      p.parent.context.environment.currentTarget).balance.toNat < p.request.value.toNat)
    (hread : NestedRunner.ReadExact checkpoint child.tracker p.parent.context.environment.currentTarget)
    (hlogs : child.logs = []) : NestedRunner.enterChild p = .error (.insufficientBalance, child) :=
  nested_entry_error_constructed p .insufficientBalance child checkpoint hsave hshape hv ⟨hbalance, hread⟩ hlogs

-- Overflow after the debit and recipient read constructs the overflow diagnostic.
theorem nested_entry_overflow_constructed (p : CallPreparation.Prepared) (child : Frame.State)
    (checkpoint debit : TransactionState.State) (hsave : NestedRunner.CheckpointExact p.parent.tracker checkpoint)
    (hshape : NestedRunner.EntryShape p child) (hv : p.request.value ≠ 0)
    (hbound : p.request.value.toNat ≤ (TransactionAccount.selectedAccount (TransactionState.Reference.observe checkpoint)
      p.parent.context.environment.currentTarget).balance.toNat)
    (hdebit : NestedRunner.BalanceEffect checkpoint debit p.parent.context.environment.currentTarget (BitVec.ofNat 256
      ((TransactionAccount.selectedAccount (TransactionState.Reference.observe checkpoint)
        p.parent.context.environment.currentTarget).balance.toNat - p.request.value.toNat)))
    (hover : Word.modulus ≤ (TransactionAccount.selectedAccount (TransactionState.Reference.observe debit) p.address).balance.toNat + p.request.value.toNat)
    (hread : NestedRunner.ReadExact debit child.tracker p.address) (hlogs : child.logs = []) :
    NestedRunner.enterChild p = .error (.recipientOverflow, child) :=
  nested_entry_error_constructed p .recipientOverflow child checkpoint hsave hshape hv
    ⟨hbound, debit, hdebit, hover, hread⟩ hlogs


-- Eliminate an observed successful entry into every child-frame field.
theorem nested_entry_success_frame_fields (p : CallPreparation.Prepared) (out : Frame.State)
    (h : NestedRunner.enterChild p = .ok out) :
  out.code = p.code ∧ out.pc = 0 ∧ out.stack = Stack.empty ∧ out.gas = p.childGas ∧
  out.memory = Memory.Allocation.empty ∧ out.returnData = ByteArray.empty ∧
  out.context.environment = { p.parent.context.environment with currentTarget := p.address, caller := p.parent.context.environment.currentTarget, value := p.request.value } ∧
  Frame.FinishBytes p.parent p.request.inputOffset p.request.inputSize out.context.data ∧
  out.warmAddresses = p.parent.warmAddresses ∧ out.warmSlots = p.parent.warmSlots ∧
  out.isStatic = p.parent.isStatic ∧ out.stateGas = ⟨p.stateGrant, p.stateGrant, 0, 0, 0⟩ := by
  have effect := (NestedRunner.entry_iff p (.ok out)).mp h
  obtain ⟨_, _, shape, _⟩ := effect
  obtain ⟨hcode, hpc, hstack, hgas, hmem, hreturn, hcontext, hdata, hwarm, hslots, hstatic, hstate⟩ := shape
  exact ⟨hcode, hpc, hstack, hgas, hmem, hreturn, hcontext, hdata, hwarm, hslots, hstatic, hstate⟩

-- The same field equations hold for either observed transfer diagnostic.
theorem nested_entry_error_frame_fields (p : CallPreparation.Prepared) (out : Frame.State)
    (reason : TransactionTransfer.TransferError) (h : NestedRunner.enterChild p = .error (reason, out)) :
  out.code = p.code ∧ out.pc = 0 ∧ out.stack = Stack.empty ∧ out.gas = p.childGas ∧
  out.memory = Memory.Allocation.empty ∧ out.returnData = ByteArray.empty ∧
  out.context.environment = { p.parent.context.environment with currentTarget := p.address, caller := p.parent.context.environment.currentTarget, value := p.request.value } ∧
  Frame.FinishBytes p.parent p.request.inputOffset p.request.inputSize out.context.data ∧
  out.warmAddresses = p.parent.warmAddresses ∧ out.warmSlots = p.parent.warmSlots ∧
  out.isStatic = p.parent.isStatic ∧ out.stateGas = ⟨p.stateGrant, p.stateGrant, 0, 0, 0⟩ := by
  have effect := (NestedRunner.entry_iff p (.error (reason, out))).mp h
  obtain ⟨_, _, shape, _⟩ := effect
  obtain ⟨hcode, hpc, hstack, hgas, hmem, hreturn, hcontext, hdata, hwarm, hslots, hstatic, hstate⟩ := shape
  exact ⟨hcode, hpc, hstack, hgas, hmem, hreturn, hcontext, hdata, hwarm, hslots, hstatic, hstate⟩
