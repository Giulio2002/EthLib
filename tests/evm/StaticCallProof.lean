import EthLib.EVM.Proofs

open EthLib.EVM

/-!
Proof consumers of the STATICCALL frame rule, preparation, lifecycle and nested step.
-/

namespace StaticCallConsumer

-- Six operands suspend in any context, with value zero and the remaining stack.
theorem suspend_any_context (s : Frame.State) (stack : Stack)
    (gas address inputOffset inputSize outputOffset outputSize : Word)
    (at_ : Frame.At s (some .staticcall))
    (items : s.stack.val = gas :: address :: inputOffset :: inputSize :: outputOffset :: outputSize :: stack.val) :
    Frame.step s = .staticCallRequest { s with stack }
      ⟨gas, address, 0, inputOffset, inputSize, outputOffset, outputSize⟩ :=
  Frame.rule_sound (.staticCallSuspend s stack gas address inputOffset inputSize outputOffset outputSize at_ items)

-- Fewer than six operands underflow, whatever the static flag.
theorem underflow_any_context (s : Frame.State) (at_ : Frame.At s (some .staticcall))
    (short : s.stack.val.length < 6) :
    Frame.step s = .exception { s with stack := Stack.empty } .stackUnderflow :=
  Frame.rule_sound (.staticCallUnderflow s at_ short)

-- An observed suspension came from the STATICCALL rule, so the request value is zero.
theorem suspension_value_zero (s input : Frame.State) (r : Frame.CallRequest)
    (h : Frame.step s = .staticCallRequest input r) : r.value = 0 := by
  have rule := (Frame.step_iff_rule s _).mp h
  cases rule
  rfl

-- The legacy runner reports the suspension as an unsupported STATICCALL.
theorem legacy_boundary (s input : Frame.State) (r : Frame.CallRequest) (fuel : Nat)
    (h : Frame.step s = .staticCallRequest input r) :
    Runner.run (fuel + 1) s = .unsupported input .staticcall := by
  simp [Runner.run, h]

-- Preparation is characterized for every result, in both directions.
theorem prepare_forward (s : Frame.State) (r : Frame.CallRequest) (result : CallPreparation.Result)
    (h : StaticCall.OutcomeSpec s r result) : StaticCall.prepare s r = result :=
  (StaticCall.prepare_iff s r result).mpr h

theorem prepare_converse (s : Frame.State) (r : Frame.CallRequest) (result : CallPreparation.Result)
    (h : StaticCall.prepare s r = result) : StaticCall.OutcomeSpec s r result :=
  (StaticCall.prepare_iff s r result).mp h

-- The only gas failure is the initial check, and it leaves the frame unchanged.
theorem gas_failure_exact (s d : Frame.State) (r : Frame.CallRequest)
    (h : StaticCall.prepare s r = .outOfGas d) : s.gas < StaticCall.initialCost s r ∧ d = s :=
  (StaticCall.outOfGas_iff s d r).mp h

-- A ready preparation never reports a balance failure or a new-account charge.
theorem ready_no_flags (s : Frame.State) (r : Frame.CallRequest) (p : CallPreparation.Prepared)
    (h : StaticCall.prepare s r = .ready p) :
    p.newAccountCharged = false ∧ p.insufficientBalance = false :=
  StaticCall.ready_flags s r p h

-- A ready preparation records exactly two callee reads and no sender read.
theorem ready_reads (s : Frame.State) (r : Frame.CallRequest) (p : CallPreparation.Prepared)
    (h : StaticCall.prepare s r = .ready p) :
    p.parent.tracker.accountReads =
      Frame.balanceAddress r.address :: Frame.balanceAddress r.address :: s.tracker.accountReads := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htracker, _⟩ := StaticCall.ready_refines s r p h
  rw [htracker]

-- The parent pays the initial cost and the forwarded grant, and nothing else.
theorem ready_gas (s : Frame.State) (r : Frame.CallRequest) (p : CallPreparation.Prepared)
    (h : StaticCall.prepare s r = .ready p) :
    p.parent.gas + p.childGas + StaticCall.initialCost s r = s.gas := by
  have spec := StaticCall.ready_refines s r p h
  obtain ⟨hg, _, _, _, _, hchild, _, _, _, _, _, _, hgas, _⟩ := spec
  have hf : StaticCall.Forwarded s r ≤ s.gas - StaticCall.initialCost s r := by
    unfold StaticCall.Forwarded; omega
  omega

-- Every entered STATICCALL child is static, whatever the parent's flag.
theorem entered_child_static (m : NestedRunner.Machine) (request : Frame.CallRequest)
    (p : CallPreparation.Prepared) (out : NestedRunner.Machine)
    (hp : ¬ NestedRunner.PrecompileAddress p.address)
    (h : NestedRunner.staticDispatch m request p = .next out) (hd : m.depth + 1 ≤ 1024) :
    out.frame.isStatic = true ∧ out.depth = m.depth + 1 ∧
      out.callers = ⟨p.parent, request, m.depth, false⟩ :: m.callers := by
  rcases (NestedRunner.staticDispatch_iff m request p _).mp h with ⟨hdeep, _⟩ | ⟨_, child, he, hr⟩
  · omega
  · rcases hr with ⟨h3, _⟩ | ⟨_, hpre, _⟩ | ⟨_, _, hnext⟩
    · exact False.elim (hp (Or.inl ⟨by omega, by omega⟩))
    · exact False.elim (hp hpre)
    · cases hnext
      exact ⟨he.2.2.2.2.2.2.2.2.2.2.2.1, rfl, rfl⟩

-- The depth limit returns both grants and pushes zero, with no state-gas refund.
theorem depth_reject (m : NestedRunner.Machine) (request : Frame.CallRequest)
    (p : CallPreparation.Prepared) (result : NestedRunner.Transition) (hd : 1024 < m.depth + 1) :
    NestedRunner.staticDispatch m request p = result ↔ NestedRunner.StaticRejectSpec m p result := by
  rw [NestedRunner.staticDispatch_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨hl, _⟩)
    · exact h
    · omega
  · intro h
    exact Or.inl ⟨hd, h⟩

-- An actual STATICCALL step is equivalent to the independent route.
theorem step_route (m : NestedRunner.Machine) (input : Frame.State) (request : Frame.CallRequest)
    (result : NestedRunner.Transition) (hf : Frame.Rule m.frame (.staticCallRequest input request)) :
    NestedRunner.step m = result ↔ NestedRunner.StaticRoute m input request result :=
  NestedRunner.staticRoute_iff m input request result (Frame.rule_sound hf)

-- A ready preparation and an allowed depth enter a static child at the next depth.
theorem step_enters_static_child (m : NestedRunner.Machine) (input : Frame.State)
    (request : Frame.CallRequest) (p : CallPreparation.Prepared) (out : NestedRunner.Machine)
    (hf : Frame.Rule m.frame (.staticCallRequest input request))
    (hp : StaticCall.ReadySpec input request p) (hd : m.depth + 1 ≤ 1024)
    (hpre : ¬ NestedRunner.PrecompileAddress p.address)
    (h : NestedRunner.step m = .next out) :
    out.frame.isStatic = true ∧ out.frame.gas = p.childGas ∧ out.depth = m.depth + 1 := by
  obtain ⟨prep, hprep, hdec⟩ := (step_route m input request _ hf).mp h
  have h1 := (StaticCall.prepare_iff input request prep).mpr hprep
  have h2 := (StaticCall.ready_iff input request p).mpr hp
  rw [h2] at h1
  cases h1
  have hdisp := (NestedRunner.staticDispatch_iff m request p _).mpr hdec
  obtain ⟨hs, hdepth, _⟩ := entered_child_static m request p out hpre hdisp hd
  rcases hdec with ⟨hdeep, _⟩ | ⟨_, child, he, hr⟩
  · omega
  · rcases hr with ⟨h3, _⟩ | ⟨_, hpre', _⟩ | ⟨_, _, hnext⟩
    · exact False.elim (hpre (Or.inl ⟨by omega, by omega⟩))
    · exact False.elim (hpre hpre')
    · cases hnext
      exact ⟨hs, he.2.2.2.1, hdepth⟩

-- A preparation gas failure takes the exceptional route with the unchanged input frame.
theorem step_gas_failure (m : NestedRunner.Machine) (input : Frame.State) (request : Frame.CallRequest)
    (result : NestedRunner.Transition) (hf : Frame.Rule m.frame (.staticCallRequest input request))
    (hg : input.gas < StaticCall.initialCost input request) :
    NestedRunner.step m = result ↔ NestedRunner.ExceptionalRoute m input .outOfGas result := by
  rw [step_route m input request result hf]
  constructor
  · rintro ⟨prep, hprep, hdec⟩
    have h1 := (StaticCall.prepare_iff input request prep).mpr hprep
    rw [StaticCall.initial_gas_failure input request hg] at h1
    subst h1
    exact hdec
  · intro h
    exact ⟨.outOfGas input, ⟨hg, rfl⟩, h⟩

-- A static-context write in a child fails that child and resumes the caller with status zero.
theorem static_write_resumes (m : NestedRunner.Machine) (t : Frame.State)
    (c : NestedRunner.Continuation) (rest : List NestedRunner.Continuation) (result : NestedRunner.Transition)
    (hcallers : m.callers = c :: rest) (hf : Frame.Rule m.frame (.exception t .writeInStaticContext)) :
    NestedRunner.step m = result ↔ NestedRunner.ResumeOutcomeSpec c t false 0 ByteArray.empty rest result := by
  simpa [NestedRunner.NonCallRoute, hcallers] using
    NestedRunner.nonCallRoute_iff m (.exception t .writeInStaticContext) result (Frame.rule_sound hf) trivial

-- SSTORE, TSTORE and a nonzero-value CALL in a static child all take that route.
theorem static_sstore (m : NestedRunner.Machine) (c : NestedRunner.Continuation)
    (rest : List NestedRunner.Continuation) (result : NestedRunner.Transition)
    (hcallers : m.callers = c :: rest) (at_ : Frame.At m.frame (some .sstore)) (hs : m.frame.isStatic = true) :
    NestedRunner.step m = result ↔
      NestedRunner.ResumeOutcomeSpec c m.frame false 0 ByteArray.empty rest result :=
  static_write_resumes m m.frame c rest result hcallers (.sstoreStatic m.frame at_ hs)

theorem static_tstore (m : NestedRunner.Machine) (c : NestedRunner.Continuation)
    (rest : List NestedRunner.Continuation) (result : NestedRunner.Transition)
    (hcallers : m.callers = c :: rest) (at_ : Frame.At m.frame (some .tstore)) (hs : m.frame.isStatic = true) :
    NestedRunner.step m = result ↔
      NestedRunner.ResumeOutcomeSpec c m.frame false 0 ByteArray.empty rest result :=
  static_write_resumes m m.frame c rest result hcallers (.tstoreStatic m.frame at_ hs)

theorem static_value_call (m : NestedRunner.Machine) (c : NestedRunner.Continuation)
    (rest : List NestedRunner.Continuation) (result : NestedRunner.Transition) (stack : Stack)
    (gas address value inputOffset inputSize outputOffset outputSize : Word)
    (hcallers : m.callers = c :: rest) (at_ : Frame.At m.frame (some .call))
    (items : m.frame.stack.val = gas :: address :: value :: inputOffset :: inputSize :: outputOffset :: outputSize :: stack.val)
    (hs : m.frame.isStatic = true) (hv : value ≠ 0) :
    NestedRunner.step m = result ↔
      NestedRunner.ResumeOutcomeSpec c { m.frame with stack } false 0 ByteArray.empty rest result :=
  static_write_resumes m _ c rest result hcallers
    (.callStatic m.frame stack gas address value inputOffset inputSize outputOffset outputSize at_ items hs hv)

-- Bounded runs that contain STATICCALL steps keep the independent trace equivalence.
theorem trace_iff (fuel : Nat) (m : NestedRunner.Machine) (result : NestedRunner.Result) :
    NestedRunner.run fuel m = result ↔ NestedRunner.RuleTrace fuel m result :=
  NestedRunner.run_iff_ruleTrace fuel m result

-- Missing code, forward: the independent map conditions and diagnostic construct the result.
theorem missing_forward (s d : Frame.State) (r : Frame.CallRequest)
    (hg : StaticCall.initialCost s r ≤ s.gas)
    (hhash : (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
      (Frame.balanceAddress r.address)).codeHash ≠ World.emptyCodeHash)
    (hwrite : (TransactionState.Reference.observe s.tracker).writes.code
      (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
        (Frame.balanceAddress r.address)).codeHash = none)
    (hparent : (TransactionState.Reference.observe s.tracker).parentCode
      (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
        (Frame.balanceAddress r.address)).codeHash = none)
    (hd : d = { s with
      warmAddresses := if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses
        else Frame.balanceAddress r.address :: s.warmAddresses,
      tracker := { s.tracker with accountReads := Frame.balanceAddress r.address :: s.tracker.accountReads } }) :
    StaticCall.prepare s r = .tooling d .missingCode :=
  (StaticCall.missingCode_iff s d r).mpr ⟨hg, hhash, hwrite, hparent, hd⟩

-- Missing code, converse: the result exposes every condition and the complete diagnostic.
theorem missing_converse (s d : Frame.State) (r : Frame.CallRequest)
    (h : StaticCall.prepare s r = .tooling d .missingCode) :
    StaticCall.initialCost s r ≤ s.gas ∧
    (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
      (Frame.balanceAddress r.address)).codeHash ≠ World.emptyCodeHash ∧
    (TransactionState.Reference.observe s.tracker).writes.code
      (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
        (Frame.balanceAddress r.address)).codeHash = none ∧
    (TransactionState.Reference.observe s.tracker).parentCode
      (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
        (Frame.balanceAddress r.address)).codeHash = none ∧
    d.code = s.code ∧ d.pc = s.pc ∧ d.stack = s.stack ∧ d.gas = s.gas ∧ d.memory = s.memory ∧
    d.context = s.context ∧ d.returnData = s.returnData ∧ d.warmSlots = s.warmSlots ∧
    d.isStatic = s.isStatic ∧ d.stateGas = s.stateGas ∧ d.logs = s.logs ∧
    d.warmAddresses = (if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses
      else Frame.balanceAddress r.address :: s.warmAddresses) ∧
    d.tracker = { s.tracker with accountReads := Frame.balanceAddress r.address :: s.tracker.accountReads } := by
  obtain ⟨hg, hhash, hwrite, hparent, hd⟩ := (StaticCall.missingCode_iff s d r).mp h
  have hd' : d = _ := hd
  subst hd'
  exact ⟨hg, hhash, hwrite, hparent, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Delegation, forward: selected designator code and the diagnostic construct the result.
theorem delegation_forward (s d : Frame.State) (r : Frame.CallRequest) (code : ByteArray)
    (hg : StaticCall.initialCost s r ≤ s.gas) (hc : CallPreparation.SelectedCode s r code)
    (hdes : CallPreparation.Designator code)
    (hd : d = { s with
      warmAddresses := if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses
        else Frame.balanceAddress r.address :: s.warmAddresses,
      tracker := { s.tracker with accountReads := Frame.balanceAddress r.address :: s.tracker.accountReads } }) :
    StaticCall.prepare s r = .tooling d .delegation :=
  (StaticCall.delegation_iff s d r).mpr ⟨hg, code, hc, hdes, hd⟩

-- Delegation, converse: the selected code is a 23-byte designator and the diagnostic is complete.
theorem delegation_converse (s d : Frame.State) (r : Frame.CallRequest)
    (h : StaticCall.prepare s r = .tooling d .delegation) :
    StaticCall.initialCost s r ≤ s.gas ∧
    (∃ code, CallPreparation.SelectedCode s r code ∧ code.size = 23 ∧
      code.data.toList.take 3 = [0xef, 0x01, 0x00]) ∧
    d.code = s.code ∧ d.pc = s.pc ∧ d.stack = s.stack ∧ d.gas = s.gas ∧ d.memory = s.memory ∧
    d.context = s.context ∧ d.returnData = s.returnData ∧ d.warmSlots = s.warmSlots ∧
    d.isStatic = s.isStatic ∧ d.stateGas = s.stateGas ∧ d.logs = s.logs ∧
    d.warmAddresses = (if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses
      else Frame.balanceAddress r.address :: s.warmAddresses) ∧
    d.tracker = { s.tracker with accountReads := Frame.balanceAddress r.address :: s.tracker.accountReads } := by
  obtain ⟨hg, code, hc, hdes, hd⟩ := (StaticCall.delegation_iff s d r).mp h
  have hd' : d = _ := hd
  subst hd'
  exact ⟨hg, ⟨code, hc, hdes.1, hdes.2⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Missing code and delegation exclude each other: the selected code decides which one occurs.
theorem missing_not_delegation (s d e : Frame.State) (r : Frame.CallRequest)
    (hm : StaticCall.prepare s r = .tooling d .missingCode) :
    StaticCall.prepare s r ≠ .tooling e .delegation := by
  intro hdel
  rw [hm] at hdel
  cases hdel

/-- Every field of a ready STATICCALL preparation, stated without the `ReadySpec` name. -/
def ReadyFields (s : Frame.State) (r : Frame.CallRequest) (p : CallPreparation.Prepared) : Prop :=
  StaticCall.initialCost s r ≤ s.gas ∧ CallPreparation.SelectedCode s r p.code ∧
    ¬ (p.code.size = 23 ∧ p.code.data.toList.take 3 = [0xef, 0x01, 0x00]) ∧
    p.request = r ∧ p.address = Frame.balanceAddress r.address ∧
    p.childGas = min r.gas.toNat ((s.gas - StaticCall.initialCost s r) - (s.gas - StaticCall.initialCost s r) / 64) ∧
    p.stateGrant = s.stateGas.reservoir ∧ p.newAccountCharged = false ∧ p.insufficientBalance = false ∧
    p.parent.code = s.code ∧ p.parent.pc = s.pc ∧ p.parent.stack = s.stack ∧
    p.parent.gas = s.gas - StaticCall.initialCost s r - p.childGas ∧
    p.parent.memory.store = s.memory.store ∧
    p.parent.memory.words = max (max s.memory.words (Memory.Allocation.requiredWords r.inputOffset.toNat r.inputSize.toNat))
      (Memory.Allocation.requiredWords r.outputOffset.toNat r.outputSize.toNat) ∧
    p.parent.context = s.context ∧ p.parent.returnData = ByteArray.empty ∧
    p.parent.tracker.parent = s.tracker.parent ∧ p.parent.tracker.writes = s.tracker.writes ∧
    p.parent.tracker.accountReads =
      Frame.balanceAddress r.address :: Frame.balanceAddress r.address :: s.tracker.accountReads ∧
    p.parent.tracker.storageReads = s.tracker.storageReads ∧
    p.parent.tracker.createdAccounts = s.tracker.createdAccounts ∧
    p.parent.tracker.snapshots = s.tracker.snapshots ∧
    p.parent.warmAddresses = (if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses
      else Frame.balanceAddress r.address :: s.warmAddresses) ∧
    p.parent.warmSlots = s.warmSlots ∧ p.parent.isStatic = s.isStatic ∧
    p.parent.stateGas.reservoir = 0 ∧ p.parent.stateGas.baseline = s.stateGas.baseline ∧
    p.parent.stateGas.refundCounter = s.stateGas.refundCounter ∧
    p.parent.stateGas.spilled = s.stateGas.spilled ∧
    p.parent.stateGas.committedSpill = s.stateGas.committedSpill ∧ p.parent.logs = s.logs

-- Ready, converse: the actual result exposes every field.
theorem ready_converse (s : Frame.State) (r : Frame.CallRequest) (p : CallPreparation.Prepared)
    (h : StaticCall.prepare s r = .ready p) : ReadyFields s r p := by
  obtain ⟨hg, hc, hd, hr, ha, hchild, hgrant, hn, hb, hcode, hpc, hstack, hgas, hstore, hwords, hctx,
    hdata, htracker, hwarm, hslots, hstatic, hstate, hlogs⟩ := StaticCall.ready_refines s r p h
  refine ⟨hg, hc, hd, hr, ha, hchild, hgrant, hn, hb, hcode, hpc, hstack, ?_, hstore, hwords, hctx, hdata,
    ?_, ?_, ?_, ?_, ?_, ?_, hwarm, hslots, hstatic, ?_, ?_, ?_, ?_, ?_, hlogs⟩
  · rw [hgas, hchild]
  all_goals simp [htracker, hstate]

-- Ready, forward: the field equations alone determine the actual preparation.
theorem ready_forward (s : Frame.State) (r : Frame.CallRequest) (p : CallPreparation.Prepared)
    (h : ReadyFields s r p) : StaticCall.prepare s r = .ready p := by
  obtain ⟨hg, hc, hd, hr, ha, hchild, hgrant, hn, hb, hcode, hpc, hstack, hgas, hstore, hwords, hctx,
    hdata, htp, htw, htr, hts, htc, htn, hwarm, hslots, hstatic, hres, hbase, hrefund, hspill, hcommit,
    hlogs⟩ := h
  apply (StaticCall.ready_iff s r p).mpr
  refine ⟨hg, hc, hd, hr, ha, hchild, hgrant, hn, hb, hcode, hpc, hstack, ?_, hstore, hwords, hctx, hdata,
    ?_, hwarm, hslots, hstatic, ?_, hlogs⟩
  · rw [hgas, hchild]; rfl
  · cases ht : p.parent.tracker
    simp_all
  · cases hm : p.parent.stateGas
    simp_all

-- Depth rejection with stack room: every field of the resumed parent, from the restored grants.
-- The state-gas fields other than the reservoir are the parent's, since no refund applies.
theorem depth_reject_next (m : NestedRunner.Machine) (request : Frame.CallRequest)
    (p : CallPreparation.Prepared) (out : NestedRunner.Machine) (hd : 1024 < m.depth + 1)
    (h : NestedRunner.staticDispatch m request p = .next out) :
    p.parent.stack.val.length < 1024 ∧ out.depth = m.depth ∧ out.callers = m.callers ∧
    out.frame.code = p.parent.code ∧ out.frame.pc = p.parent.pc + 1 ∧
    out.frame.stack.val = 0 :: p.parent.stack.val ∧ out.frame.gas = p.parent.gas + p.childGas ∧
    out.frame.memory = p.parent.memory ∧ out.frame.context = p.parent.context ∧
    out.frame.returnData = p.parent.returnData ∧ out.frame.tracker = p.parent.tracker ∧
    out.frame.warmAddresses = p.parent.warmAddresses ∧ out.frame.warmSlots = p.parent.warmSlots ∧
    out.frame.isStatic = p.parent.isStatic ∧ out.frame.logs = p.parent.logs ∧
    out.frame.stateGas.reservoir = p.parent.stateGas.reservoir + p.stateGrant ∧
    out.frame.stateGas.baseline = p.parent.stateGas.baseline ∧
    out.frame.stateGas.refundCounter = p.parent.stateGas.refundCounter ∧
    out.frame.stateGas.spilled = p.parent.stateGas.spilled ∧
    out.frame.stateGas.committedSpill = p.parent.stateGas.committedSpill := by
  obtain ⟨restored, hr, hz⟩ := (depth_reject m request p _ hd).mp h
  obtain ⟨hcode, hpc, hstack, hgas, hmem, hctx, hdata, htr, hwarm, hslots, hstatic, hlogs,
    hres, hbase, hrefund, hspill, hcommit⟩ := hr
  obtain ⟨hroom, hdepth, hcallers, hcode', hpc', hstack', hgas', hmem', hctx', hdata', htr', hwarm',
    hslots', hstatic', hstate', hlogs'⟩ := hz
  rw [hstack] at hroom hstack'
  rw [hstate']
  exact ⟨hroom, hdepth, hcallers, hcode'.trans hcode, by rw [hpc', hpc], hstack', hgas'.trans hgas,
    hmem'.trans hmem, hctx'.trans hctx, hdata'.trans hdata, htr'.trans htr, hwarm'.trans hwarm,
    hslots'.trans hslots, hstatic'.trans hstatic, hlogs'.trans hlogs, hres, hbase, hrefund, hspill, hcommit⟩

-- Depth rejection with a full stack reports exactly the restored parent.
theorem depth_reject_full (m : NestedRunner.Machine) (request : Frame.CallRequest)
    (p : CallPreparation.Prepared) (d : Frame.State) (hd : 1024 < m.depth + 1)
    (h : NestedRunner.staticDispatch m request p = .done (.tooling d .invalidContinuation)) :
    p.parent.stack.val.length = 1024 ∧ NestedRunner.GrantRestore p d := by
  obtain ⟨restored, hr, hz⟩ := (depth_reject m request p _ hd).mp h
  obtain ⟨hfull, rfl⟩ := hz
  rw [hr.2.2.1] at hfull
  exact ⟨hfull, hr⟩

/-- The RIPEMD-160 charge on the entered child's input. -/
def RipemdCost (p : CallPreparation.Prepared) : Nat :=
  600 + 120 * (((NestedRunner.staticChildFrame p).context.data.size + 31) / 32)

-- An affordable RIPEMD-160 STATICCALL commits the child and copies the digest prefix.
theorem ripemd_success (m : NestedRunner.Machine) (request : Frame.CallRequest)
    (p : CallPreparation.Prepared) (out : NestedRunner.Machine) (hd : m.depth + 1 ≤ 1024)
    (h3 : p.address.val = 3) (hgas : RipemdCost p ≤ p.childGas)
    (h : NestedRunner.staticDispatch m request p = .next out) :
    ∃ incorporated,
      ChildSettlement.Effect p.parent (NestedRunner.staticChildFrame p) incorporated true
        (p.childGas - RipemdCost p)
        (EthLib.Execution.Evm.Precompiles.Ripemd160.ripemd160 (NestedRunner.staticChildFrame p).context.data) ∧
      out.depth = m.depth ∧ out.callers = m.callers ∧
      out.frame.pc = p.parent.pc + 1 ∧ out.frame.stack.val = 1 :: p.parent.stack.val ∧
      out.frame.gas = incorporated.gas ∧
      out.frame.returnData =
        EthLib.Execution.Evm.Precompiles.Ripemd160.ripemd160 (NestedRunner.staticChildFrame p).context.data ∧
      out.frame.memory.store = List.zip
        (List.range' request.outputOffset.toNat
          ((EthLib.Execution.Evm.Precompiles.Ripemd160.ripemd160 (NestedRunner.staticChildFrame p).context.data).data.toList.take
            request.outputSize.toNat).length)
        ((EthLib.Execution.Evm.Precompiles.Ripemd160.ripemd160 (NestedRunner.staticChildFrame p).context.data).data.toList.take
          request.outputSize.toNat) ++ p.parent.memory.store ∧
      out.frame.isStatic = p.parent.isStatic := by
  rcases (NestedRunner.staticDispatch_iff m request p _).mp h with ⟨hdeep, _⟩ | ⟨_, child, he, hr⟩
  · omega
  have hchild := (NestedRunner.staticEntry_iff p child).mpr he
  subst hchild
  rcases hr with ⟨_, hspec⟩ | ⟨h3', _⟩ | ⟨h3', _⟩
  · rcases hspec with ⟨hshort, _⟩ | ⟨_, hres⟩
    · have : (NestedRunner.staticChildFrame p).gas = p.childGas := rfl
      unfold RipemdCost at hgas
      omega
    · obtain ⟨inc, credited, heff, hcredit, _, hdepth, hcallers, _, hpc, hstack, hg, hstore, _,
        _, hret, _, _, _, hstatic, _, _⟩ := hres
      rcases hcredit with ⟨_, rfl⟩ | ⟨hf, _⟩
      · have heff' := heff
        obtain ⟨_, _, _, _, _, hpc0, hstk, hmem, _, hout, hst, _⟩ := heff'
        refine ⟨credited, heff, hdepth, hcallers, by rw [hpc, hpc0], ?_, hg, hret.trans hout, ?_,
          hstatic.trans hst⟩
        · simp [hstack, hstk]
        · rw [hstore, hmem]
      · cases hf
  · exact False.elim (h3' h3)
  · exact False.elim (h3' h3)

-- A short RIPEMD-160 grant fails the child: status 0, no output and the grant burned.
theorem ripemd_short (m : NestedRunner.Machine) (request : Frame.CallRequest)
    (p : CallPreparation.Prepared) (out : NestedRunner.Machine) (hd : m.depth + 1 ≤ 1024)
    (h3 : p.address.val = 3) (hgas : p.childGas < RipemdCost p)
    (h : NestedRunner.staticDispatch m request p = .next out) :
    out.depth = m.depth ∧ out.callers = m.callers ∧
      out.frame.pc = p.parent.pc + 1 ∧ out.frame.stack.val = 0 :: p.parent.stack.val ∧
      out.frame.returnData = ByteArray.empty ∧ out.frame.memory.store = p.parent.memory.store ∧
      out.frame.logs = p.parent.logs ∧ out.frame.warmAddresses = p.parent.warmAddresses := by
  rcases (NestedRunner.staticDispatch_iff m request p _).mp h with ⟨hdeep, _⟩ | ⟨_, child, he, hr⟩
  · omega
  have hchild := (NestedRunner.staticEntry_iff p child).mpr he
  subst hchild
  rcases hr with ⟨_, hspec⟩ | ⟨h3', _⟩ | ⟨h3', _⟩
  · rcases hspec with ⟨_, hres⟩ | ⟨hlong, _⟩
    · obtain ⟨inc, credited, heff, hcredit, _, hdepth, hcallers, _, hpc, hstack, _, hstore, _,
        _, hret, _, hwarm, _, _, _, hlogs⟩ := hres
      rcases hcredit with ⟨hok, rfl⟩ | ⟨_, hc, _⟩
      · obtain ⟨saved, rest, _, _, _, hpc0, hstk, hmem, _, hout, _, _, _, _, _, _, _, hlog, hw, _⟩ := heff
        refine ⟨hdepth, hcallers, by rw [hpc, hpc0], ?_, hret.trans hout, ?_, ?_, ?_⟩
        · simp [hstack, hstk]
        · rw [hstore, hmem]; simp
        · rw [hlogs, hlog]; rfl
        · rw [hwarm, hw]; rfl
      · cases hc
    · have : (NestedRunner.staticChildFrame p).gas = p.childGas := rfl
      unfold RipemdCost at hgas
      omega
  · exact False.elim (h3' h3)
  · exact False.elim (h3' h3)

-- `Frame.staticCallEntry_items` applied to an arbitrary frame: no opcode, PC or code premise.
-- Every field of the suspended frame and of the request is observed.
theorem entry_items_applied (s input : Frame.State) (r : Frame.CallRequest) (stack : Stack)
    (gas address inputOffset inputSize outputOffset outputSize : Word)
    (items : s.stack.val = gas :: address :: inputOffset :: inputSize :: outputOffset :: outputSize :: stack.val)
    (h : Frame.staticCallEntry s = .staticCallRequest input r) :
    input.code = s.code ∧ input.pc = s.pc ∧ input.stack = stack ∧ input.gas = s.gas ∧
    input.memory = s.memory ∧ input.context = s.context ∧ input.returnData = s.returnData ∧
    input.tracker = s.tracker ∧ input.warmAddresses = s.warmAddresses ∧ input.warmSlots = s.warmSlots ∧
    input.isStatic = s.isStatic ∧ input.stateGas = s.stateGas ∧ input.logs = s.logs ∧
    r.gas = gas ∧ r.address = address ∧ r.value = 0 ∧ r.inputOffset = inputOffset ∧
    r.inputSize = inputSize ∧ r.outputOffset = outputOffset ∧ r.outputSize = outputSize := by
  rw [Frame.staticCallEntry_items s stack gas address inputOffset inputSize outputOffset outputSize items] at h
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- `Frame.staticCallEntry_short` applied to an arbitrary frame: every diagnostic field is observed.
theorem entry_short_applied (s d : Frame.State) (reason : Frame.Exception) (short : s.stack.val.length < 6)
    (h : Frame.staticCallEntry s = .exception d reason) :
    reason = .stackUnderflow ∧ d.stack.val = [] ∧
    d.code = s.code ∧ d.pc = s.pc ∧ d.gas = s.gas ∧ d.memory = s.memory ∧ d.context = s.context ∧
    d.returnData = s.returnData ∧ d.tracker = s.tracker ∧ d.warmAddresses = s.warmAddresses ∧
    d.warmSlots = s.warmSlots ∧ d.isStatic = s.isStatic ∧ d.stateGas = s.stateGas ∧ d.logs = s.logs := by
  rw [Frame.staticCallEntry_short s short] at h
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Together the two lemmas decide the entry helper on any frame by the stack length alone.
theorem entry_cases (s : Frame.State) :
    (s.stack.val.length < 6 ∧ Frame.staticCallEntry s = .exception { s with stack := Stack.empty } .stackUnderflow) ∨
    (∃ gas address inputOffset inputSize outputOffset outputSize, ∃ stack : Stack,
      Frame.staticCallEntry s = .staticCallRequest { s with stack }
        ⟨gas, address, 0, inputOffset, inputSize, outputOffset, outputSize⟩) := by
  by_cases short : s.stack.val.length < 6
  · exact Or.inl ⟨short, Frame.staticCallEntry_short s short⟩
  · right
    match items : s.stack.val with
    | gas :: address :: inputOffset :: inputSize :: outputOffset :: outputSize :: rest =>
      let stack : Stack := ⟨rest, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
      exact ⟨gas, address, inputOffset, inputSize, outputOffset, outputSize, stack,
        Frame.staticCallEntry_items s stack gas address inputOffset inputSize outputOffset outputSize items⟩
    | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] => simp [items] at short

-- Depth rejection with a full stack: every diagnostic field, both grant restorations, no refund.
theorem depth_reject_full_fields (m : NestedRunner.Machine) (request : Frame.CallRequest)
    (p : CallPreparation.Prepared) (d : Frame.State) (hd : 1024 < m.depth + 1)
    (h : NestedRunner.staticDispatch m request p = .done (.tooling d .invalidContinuation)) :
    p.parent.stack.val.length = 1024 ∧ d.stack = p.parent.stack ∧ d.pc = p.parent.pc ∧
    d.code = p.parent.code ∧ d.gas = p.parent.gas + p.childGas ∧ d.memory = p.parent.memory ∧
    d.context = p.parent.context ∧ d.returnData = p.parent.returnData ∧ d.tracker = p.parent.tracker ∧
    d.warmAddresses = p.parent.warmAddresses ∧ d.warmSlots = p.parent.warmSlots ∧
    d.isStatic = p.parent.isStatic ∧ d.logs = p.parent.logs ∧
    d.stateGas.reservoir = p.parent.stateGas.reservoir + p.stateGrant ∧
    d.stateGas.baseline = p.parent.stateGas.baseline ∧
    d.stateGas.refundCounter = p.parent.stateGas.refundCounter ∧
    d.stateGas.spilled = p.parent.stateGas.spilled ∧
    d.stateGas.committedSpill = p.parent.stateGas.committedSpill := by
  obtain ⟨hfull, hcode, hpc, hstack, hgas, hmem, hctx, hdata, htr, hwarm, hslots, hstatic, hlogs,
    hres, hbase, hrefund, hspill, hcommit⟩ := depth_reject_full m request p d hd h
  exact ⟨hfull, hstack, hpc, hcode, hgas, hmem, hctx, hdata, htr, hwarm, hslots, hstatic, hlogs,
    hres, hbase, hrefund, hspill, hcommit⟩

/-- Concrete settlement of the entered STATICCALL child, for either outcome.

The child is `staticChildFrame p`: its tracker is the parent's with one checkpoint, it has no logs,
no spill and the grant as both reservoir and baseline. A precompile child makes no tracker writes,
so commit and rollback both return the parent's tracker.
-/
theorem static_effect_fields (p : CallPreparation.Prepared) (inc : Frame.State) (success : Bool)
    (gas : Nat) (output : ByteArray)
    (h : ChildSettlement.Effect p.parent (NestedRunner.staticChildFrame p) inc success gas output) :
    inc.code = p.parent.code ∧ inc.pc = p.parent.pc ∧ inc.stack = p.parent.stack ∧
    inc.memory = p.parent.memory ∧ inc.context = p.parent.context ∧ inc.returnData = output ∧
    inc.isStatic = p.parent.isStatic ∧
    inc.tracker.writes = (if success then (NestedRunner.staticChildFrame p).tracker.writes
      else p.parent.tracker.writes) ∧
    inc.tracker = p.parent.tracker ∧ inc.logs = p.parent.logs ∧
    inc.warmAddresses = (if success then p.parent.warmAddresses ++ p.parent.warmAddresses
      else p.parent.warmAddresses) ∧
    inc.warmSlots = (if success then p.parent.warmSlots ++ p.parent.warmSlots else p.parent.warmSlots) ∧
    inc.gas = p.parent.gas + gas +
      (if success then min (p.parent.stateGas.reservoir + p.stateGrant) p.parent.stateGas.spilled else 0) ∧
    inc.stateGas.reservoir = p.parent.stateGas.reservoir + p.stateGrant -
      (if success then min (p.parent.stateGas.reservoir + p.stateGrant) p.parent.stateGas.spilled else 0) ∧
    inc.stateGas.baseline = p.parent.stateGas.baseline ∧
    inc.stateGas.refundCounter = p.parent.stateGas.refundCounter ∧
    inc.stateGas.spilled = p.parent.stateGas.spilled -
      (if success then min (p.parent.stateGas.reservoir + p.stateGrant) p.parent.stateGas.spilled else 0) ∧
    inc.stateGas.committedSpill = p.parent.stateGas.committedSpill := by
  obtain ⟨saved, rest, _, hsnap, hcode, hpc, hstack, hmem, hctx, hout, hstatic, htp, htw, htr, hts, htc,
    htn, hlogs, hwarm, hslots, hgas, hres, hbase, hrefund, hspill, hcommit⟩ := h
  -- The child's checkpoint saved the parent's writes over the parent's snapshots.
  have hs : p.parent.tracker.writes :: p.parent.tracker.snapshots = saved :: rest := hsnap
  obtain ⟨rfl, rfl⟩ := List.cons.inj hs
  have htracker : inc.tracker = p.parent.tracker := by
    cases ht : inc.tracker
    cases hp : p.parent.tracker
    simp only [ht, hp] at htp htw htr hts htc htn ⊢
    cases success <;> simp_all [NestedRunner.staticChildFrame, NestedRunner.childFrame, TransactionState.snapshot]
  refine ⟨hcode, hpc, hstack, hmem, hctx, hout, hstatic, ?_, htracker, ?_, ?_, ?_, ?_, ?_, hbase, ?_, ?_, hcommit⟩
  · cases success <;> simpa using htw
  all_goals cases success <;> simp_all [NestedRunner.staticChildFrame, NestedRunner.childFrame]

-- An affordable RIPEMD-160 STATICCALL: complete resumed frame, settlement arithmetic and caller.
theorem ripemd_success_fields (m : NestedRunner.Machine) (request : Frame.CallRequest)
    (p : CallPreparation.Prepared) (out : NestedRunner.Machine) (hd : m.depth + 1 ≤ 1024)
    (h3 : p.address.val = 3) (hgas : RipemdCost p ≤ p.childGas)
    (h : NestedRunner.staticDispatch m request p = .next out) :
    let digest := EthLib.Execution.Evm.Precompiles.Ripemd160.ripemd160 (NestedRunner.staticChildFrame p).context.data
    let bytes := digest.data.toList.take request.outputSize.toNat
    let repayment := min (p.parent.stateGas.reservoir + p.stateGrant) p.parent.stateGas.spilled
    out.depth = m.depth ∧ out.callers = m.callers ∧
    out.frame.code = p.parent.code ∧ out.frame.pc = p.parent.pc + 1 ∧
    out.frame.stack.val = 1 :: p.parent.stack.val ∧
    out.frame.gas = p.parent.gas + (p.childGas - RipemdCost p) + repayment ∧
    out.frame.memory.store = List.zip (List.range' request.outputOffset.toNat bytes.length) bytes ++
      p.parent.memory.store ∧
    out.frame.memory.words = max p.parent.memory.words
      (Memory.Allocation.requiredWords request.outputOffset.toNat bytes.length) ∧
    out.frame.context = p.parent.context ∧ out.frame.returnData = digest ∧
    out.frame.tracker = p.parent.tracker ∧ out.frame.logs = p.parent.logs ∧
    out.frame.warmAddresses = p.parent.warmAddresses ++ p.parent.warmAddresses ∧
    out.frame.warmSlots = p.parent.warmSlots ++ p.parent.warmSlots ∧
    out.frame.isStatic = p.parent.isStatic ∧
    out.frame.stateGas.reservoir = p.parent.stateGas.reservoir + p.stateGrant - repayment ∧
    out.frame.stateGas.baseline = p.parent.stateGas.baseline ∧
    out.frame.stateGas.refundCounter = p.parent.stateGas.refundCounter ∧
    out.frame.stateGas.spilled = p.parent.stateGas.spilled - repayment ∧
    out.frame.stateGas.committedSpill = p.parent.stateGas.committedSpill := by
  intro digest bytes repayment
  rcases (NestedRunner.staticDispatch_iff m request p _).mp h with ⟨hdeep, _⟩ | ⟨_, child, he, hr⟩
  · omega
  have hchild := (NestedRunner.staticEntry_iff p child).mpr he
  subst hchild
  rcases hr with ⟨_, hspec⟩ | ⟨h3', _⟩ | ⟨h3', _⟩
  · rcases hspec with ⟨hshort, _⟩ | ⟨_, hres⟩
    · have : (NestedRunner.staticChildFrame p).gas = p.childGas := rfl
      unfold RipemdCost at hgas
      omega
    · obtain ⟨inc, credited, heff, hcredit, _, hdepth, hcallers, hcode, hpc, hstack, hg, hstore, hwords,
        hctx, hret, htr, hwarm, hslots, hstatic, hstate, hlogs⟩ := hres
      rcases hcredit with ⟨_, rfl⟩ | ⟨hf, _⟩
      · obtain ⟨icode, ipc, istack, imem, ictx, iout, istatic, _, itracker, ilogs, iwarm, islots, igas,
          ires, ibase, irefund, ispill, icommit⟩ := static_effect_fields p _ true _ _ heff
        have hcost : (NestedRunner.staticChildFrame p).gas -
            (600 + 120 * (((NestedRunner.staticChildFrame p).context.data.size + 31) / 32)) =
            p.childGas - RipemdCost p := rfl
        rw [hstate]
        refine ⟨hdepth, hcallers, hcode.trans icode, by rw [hpc, ipc], ?_, ?_, ?_, ?_, hctx.trans ictx,
          hret.trans iout, htr.trans itracker, hlogs.trans ilogs, by simpa using hwarm.trans iwarm,
          by simpa using hslots.trans islots, hstatic.trans istatic, by simpa using ires, ibase,
          by simpa using irefund, by simpa using ispill, icommit⟩
        · simp [hstack, istack]
        · rw [hg, igas, hcost]; simp [repayment]
        · rw [hstore, imem]
        · rw [hwords, imem]
      · cases hf
  · exact False.elim (h3' h3)
  · exact False.elim (h3' h3)

-- A short RIPEMD-160 grant: complete resumed frame; the grant is burned, the reservoir restored, the tracker rolled back.
theorem ripemd_short_fields (m : NestedRunner.Machine) (request : Frame.CallRequest)
    (p : CallPreparation.Prepared) (out : NestedRunner.Machine) (hd : m.depth + 1 ≤ 1024)
    (h3 : p.address.val = 3) (hgas : p.childGas < RipemdCost p)
    (h : NestedRunner.staticDispatch m request p = .next out) :
    out.depth = m.depth ∧ out.callers = m.callers ∧
    out.frame.code = p.parent.code ∧ out.frame.pc = p.parent.pc + 1 ∧
    out.frame.stack.val = 0 :: p.parent.stack.val ∧ out.frame.gas = p.parent.gas ∧
    out.frame.memory.store = p.parent.memory.store ∧
    out.frame.memory.words = max p.parent.memory.words
      (Memory.Allocation.requiredWords request.outputOffset.toNat 0) ∧
    out.frame.context = p.parent.context ∧ out.frame.returnData = ByteArray.empty ∧
    out.frame.tracker = p.parent.tracker ∧ out.frame.logs = p.parent.logs ∧
    out.frame.warmAddresses = p.parent.warmAddresses ∧ out.frame.warmSlots = p.parent.warmSlots ∧
    out.frame.isStatic = p.parent.isStatic ∧
    out.frame.stateGas.reservoir = p.parent.stateGas.reservoir + p.stateGrant ∧
    out.frame.stateGas.baseline = p.parent.stateGas.baseline ∧
    out.frame.stateGas.refundCounter = p.parent.stateGas.refundCounter ∧
    out.frame.stateGas.spilled = p.parent.stateGas.spilled ∧
    out.frame.stateGas.committedSpill = p.parent.stateGas.committedSpill := by
  rcases (NestedRunner.staticDispatch_iff m request p _).mp h with ⟨hdeep, _⟩ | ⟨_, child, he, hr⟩
  · omega
  have hchild := (NestedRunner.staticEntry_iff p child).mpr he
  subst hchild
  rcases hr with ⟨_, hspec⟩ | ⟨h3', _⟩ | ⟨h3', _⟩
  · rcases hspec with ⟨_, hres⟩ | ⟨hlong, _⟩
    · obtain ⟨inc, credited, heff, hcredit, _, hdepth, hcallers, hcode, hpc, hstack, hg, hstore, hwords,
        hctx, hret, htr, hwarm, hslots, hstatic, hstate, hlogs⟩ := hres
      rcases hcredit with ⟨_, rfl⟩ | ⟨_, hc, _⟩
      · obtain ⟨icode, ipc, istack, imem, ictx, iout, istatic, _, itracker, ilogs, iwarm, islots, igas,
          ires, ibase, irefund, ispill, icommit⟩ := static_effect_fields p _ false _ _ heff
        rw [hstate]
        refine ⟨hdepth, hcallers, hcode.trans icode, by rw [hpc, ipc], ?_, by simpa using hg.trans igas,
          ?_, ?_, hctx.trans ictx, hret.trans iout, htr.trans itracker, hlogs.trans ilogs,
          by simpa using hwarm.trans iwarm, by simpa using hslots.trans islots, hstatic.trans istatic,
          by simpa using ires, ibase, by simpa using irefund, by simpa using ispill, icommit⟩
        · simp [hstack, istack]
        · rw [hstore, imem]; simp
        · rw [hwords, imem]; simp
      · cases hc
    · have : (NestedRunner.staticChildFrame p).gas = p.childGas := rfl
      unfold RipemdCost at hgas
      omega
  · exact False.elim (h3' h3)
  · exact False.elim (h3' h3)

-- A full parent stack on the RIPEMD-160 route: the settled parent is reported, with its complete settlement.
-- The child always has a checkpoint and no committed spill, so this is the only invalid continuation.
theorem ripemd_full_fields (m : NestedRunner.Machine) (request : Frame.CallRequest)
    (p : CallPreparation.Prepared) (d : Frame.State) (hd : m.depth + 1 ≤ 1024) (h3 : p.address.val = 3)
    (h : NestedRunner.staticDispatch m request p = .done (.tooling d .invalidContinuation)) :
    let success := decide (RipemdCost p ≤ p.childGas)
    let repayment := if success then min (p.parent.stateGas.reservoir + p.stateGrant) p.parent.stateGas.spilled else 0
    p.parent.stack.val.length = 1024 ∧
    d.code = p.parent.code ∧ d.pc = p.parent.pc ∧ d.stack = p.parent.stack ∧ d.memory = p.parent.memory ∧
    d.context = p.parent.context ∧
    d.returnData = (if success then
      EthLib.Execution.Evm.Precompiles.Ripemd160.ripemd160 (NestedRunner.staticChildFrame p).context.data
      else ByteArray.empty) ∧
    d.gas = p.parent.gas + (if success then p.childGas - RipemdCost p else 0) + repayment ∧
    d.tracker = p.parent.tracker ∧ d.logs = p.parent.logs ∧ d.isStatic = p.parent.isStatic ∧
    d.warmAddresses = (if success then p.parent.warmAddresses ++ p.parent.warmAddresses else p.parent.warmAddresses) ∧
    d.warmSlots = (if success then p.parent.warmSlots ++ p.parent.warmSlots else p.parent.warmSlots) ∧
    d.stateGas.reservoir = p.parent.stateGas.reservoir + p.stateGrant - repayment ∧
    d.stateGas.baseline = p.parent.stateGas.baseline ∧
    d.stateGas.refundCounter = p.parent.stateGas.refundCounter ∧
    d.stateGas.spilled = p.parent.stateGas.spilled - repayment ∧
    d.stateGas.committedSpill = p.parent.stateGas.committedSpill := by
  intro success repayment
  simp only [repayment, success]
  rcases (NestedRunner.staticDispatch_iff m request p _).mp h with ⟨hdeep, _⟩ | ⟨_, child, he, hr⟩
  · omega
  have hchild := (NestedRunner.staticEntry_iff p child).mpr he
  subst hchild
  have hcost : RipemdCost p = 600 + 120 * (((NestedRunner.staticChildFrame p).context.data.size + 31) / 32) := rfl
  have hcg : (NestedRunner.staticChildFrame p).gas = p.childGas := rfl
  rcases hr with ⟨_, hspec⟩ | ⟨h3', _⟩ | ⟨h3', _⟩
  · rcases hspec with ⟨hshort, hres⟩ | ⟨hlong, hres⟩
    · have hs : ¬ RipemdCost p ≤ p.childGas := by unfold RipemdCost; omega
      rcases hres with ⟨rfl, hbad⟩ | ⟨inc, credited, heff, hcredit, hfull, rfl⟩
      · simp [NestedRunner.staticChildFrame, NestedRunner.childFrame, TransactionState.snapshot] at hbad
      rcases hcredit with ⟨_, rfl⟩ | ⟨_, hc, _⟩
      · obtain ⟨icode, ipc, istack, imem, ictx, iout, istatic, _, itracker, ilogs, iwarm, islots, igas,
          ires, ibase, irefund, ispill, icommit⟩ := static_effect_fields p _ false _ _ heff
        simp only [hs, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [istack] at hfull
        refine ⟨hfull, icode, ipc, istack, imem, ictx, iout, ?_, itracker, ilogs, istatic, iwarm, islots,
          ?_, ibase, by simpa using irefund, ?_, icommit⟩
        all_goals simp_all
      · cases hc
    · have hs : RipemdCost p ≤ p.childGas := by unfold RipemdCost; omega
      rcases hres with ⟨rfl, hbad⟩ | ⟨inc, credited, heff, hcredit, hfull, rfl⟩
      · simp [NestedRunner.staticChildFrame, NestedRunner.childFrame, TransactionState.snapshot] at hbad
      rcases hcredit with ⟨_, rfl⟩ | ⟨hf, _⟩
      · obtain ⟨icode, ipc, istack, imem, ictx, iout, istatic, _, itracker, ilogs, iwarm, islots, igas,
          ires, ibase, irefund, ispill, icommit⟩ := static_effect_fields p _ true _ _ heff
        simp only [hs, decide_true, ↓reduceIte]
        rw [istack] at hfull
        refine ⟨hfull, icode, ipc, istack, imem, ictx, iout, ?_, itracker, ilogs, istatic, iwarm, islots,
          ?_, ibase, by simpa using irefund, ?_, icommit⟩
        · rw [igas, hcg, hcost]; simp
        · simpa using ires
        · simpa using ispill
      · cases hf
  · exact False.elim (h3' h3)
  · exact False.elim (h3' h3)

end StaticCallConsumer
-- Generated by staticcall-review-repair-audit.py: each scoped public theorem, guarded.
-- Every observed inventory below was checked to be within propext, Classical.choice and Quot.sound.

/-- info: 'EthLib.EVM.StaticCall.grant_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCall.grant_eq

/-- info: 'EthLib.EVM.StaticCall.charge_affordable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCall.charge_affordable

/-- info: 'EthLib.EVM.StaticCall.initial_gas_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCall.initial_gas_failure

/-- info: 'EthLib.EVM.StaticCall.outOfGas_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCall.outOfGas_iff

/-- info: 'EthLib.EVM.StaticCall.missingCode_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCall.missingCode_iff

/-- info: 'EthLib.EVM.StaticCall.delegation_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCall.delegation_iff

/-- info: 'EthLib.EVM.StaticCall.valueTransfer_unreachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCall.valueTransfer_unreachable

/-- info: 'EthLib.EVM.StaticCall.ready_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCall.ready_refines

/-- info: 'EthLib.EVM.StaticCall.readySpec_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCall.readySpec_unique

/-- info: 'EthLib.EVM.StaticCall.ready_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCall.ready_complete

/-- info: 'EthLib.EVM.StaticCall.ready_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCall.ready_iff

/-- info: 'EthLib.EVM.StaticCall.prepare_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCall.prepare_iff

/-- info: 'EthLib.EVM.StaticCall.ready_flags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCall.ready_flags

/-- info: 'EthLib.EVM.NestedRunner.nonCallRoute_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.nonCallRoute_iff

/-- info: 'EthLib.EVM.NestedRunner.nonCallStep_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.nonCallStep_iff

/-- info: 'EthLib.EVM.NestedRunner.grantRestore_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms NestedRunner.grantRestore_iff

/-- info: 'EthLib.EVM.NestedRunner.zeroPush_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.zeroPush_iff

/-- info: 'EthLib.EVM.NestedRunner.reject_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.reject_iff

/-- info: 'EthLib.EVM.NestedRunner.precompileAddress_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.precompileAddress_iff

/-- info: 'EthLib.EVM.NestedRunner.ripemdCall_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.ripemdCall_iff

/-- info: 'EthLib.EVM.NestedRunner.entryDecision_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.entryDecision_iff

/-- info: 'EthLib.EVM.NestedRunner.childRoute_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.childRoute_iff

/-- info: 'EthLib.EVM.NestedRunner.preparedRoute_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.preparedRoute_iff

/-- info: 'EthLib.EVM.NestedRunner.exceptionalRoute_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.exceptionalRoute_iff

/-- info: 'EthLib.EVM.NestedRunner.callDecision_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.callDecision_iff

/-- info: 'EthLib.EVM.NestedRunner.callRoute_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.callRoute_iff

/-- info: 'EthLib.EVM.NestedRunner.staticReject_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.staticReject_iff

/-- info: 'EthLib.EVM.NestedRunner.staticEntry_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.staticEntry_iff

/-- info: 'EthLib.EVM.NestedRunner.staticChildDecision_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.staticChildDecision_iff

/-- info: 'EthLib.EVM.NestedRunner.staticDispatch_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.staticDispatch_iff

/-- info: 'EthLib.EVM.NestedRunner.staticPrepDecision_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.staticPrepDecision_iff

/-- info: 'EthLib.EVM.NestedRunner.staticRoute_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.staticRoute_iff

/-- info: 'EthLib.EVM.NestedRunner.step_iff_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.step_iff_spec

/-- info: 'EthLib.EVM.NestedRunner.run_ruleTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.run_ruleTrace

/-- info: 'EthLib.EVM.NestedRunner.run_of_ruleTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.run_of_ruleTrace

/-- info: 'EthLib.EVM.NestedRunner.run_iff_ruleTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.run_iff_ruleTrace

/-- info: 'EthLib.EVM.NestedRunner.ruleTrace_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.ruleTrace_split

/-- info: 'EthLib.EVM.NestedRunner.ruleTrace_final_extra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NestedRunner.ruleTrace_final_extra

/-- info: 'EthLib.EVM.Runner.run_of_stops' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.run_of_stops

/-- info: 'EthLib.EVM.Runner.stops_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.stops_of_run

/-- info: 'EthLib.EVM.Runner.run_of_terminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.run_of_terminates

/-- info: 'EthLib.EVM.Runner.terminates_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.terminates_of_run

/-- info: 'EthLib.EVM.Runner.run_exhausted_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.run_exhausted_iff

/-- info: 'EthLib.EVM.Runner.run_characterization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.run_characterization

/-- info: 'EthLib.EVM.Runner.run_not_reverted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.run_not_reverted

/-- info: 'EthLib.EVM.Runner.terminates_not_reverted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.terminates_not_reverted

/-- info: 'EthLib.EVM.Runner.run_terminal_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.run_terminal_stable

/-- info: 'EthLib.EVM.Runner.terminates_deterministic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.terminates_deterministic

/-- info: 'EthLib.EVM.Runner.run_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.run_add

/-- info: 'EthLib.EVM.Runner.settle_cases' does not depend on any axioms -/
#guard_msgs in
#print axioms Runner.settle_cases

/-- info: 'EthLib.EVM.Runner.run_code_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.run_code_unchanged

/-- info: 'EthLib.EVM.Runner.run_context_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.run_context_unchanged

/-- info: 'EthLib.EVM.Runner.run_returnData_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.run_returnData_unchanged

/-- info: 'EthLib.EVM.Runner.run_memory_unchanged_of_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.run_memory_unchanged_of_pure

/-- info: 'EthLib.EVM.Runner.BalanceProgram.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.BalanceProgram.run

/-- info: 'EthLib.EVM.Runner.BalanceProgram.run_warm_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.BalanceProgram.run_warm_monotone

/-- info: 'EthLib.EVM.Runner.BlobFeeProgram.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.BlobFeeProgram.run

/-- info: 'EthLib.EVM.Runner.BlobFeeProgram.run_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.BlobFeeProgram.run_preserves

/-- info: 'EthLib.EVM.Runner.BlobFeeProgram.program_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.BlobFeeProgram.program_pure

/-- info: 'EthLib.EVM.Runner.BlobFeeProgram.program_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.BlobFeeProgram.program_memory

/-- info: 'EthLib.EVM.Runner.BlobHashProgram.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.BlobHashProgram.run

/-- info: 'EthLib.EVM.Runner.BlobHashProgram.run_in_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.BlobHashProgram.run_in_out

/-- info: 'EthLib.EVM.Runner.BlobHashProgram.run_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.BlobHashProgram.run_preserves

/-- info: 'EthLib.EVM.Runner.BlobHashProgram.run_preserves_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.BlobHashProgram.run_preserves_memory

/-- info: 'EthLib.EVM.Runner.BlobHashProgram.program_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.BlobHashProgram.program_pure

/-- info: 'EthLib.EVM.Runner.BlobHashProgram.program_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.BlobHashProgram.program_memory

/-- info: 'EthLib.EVM.Runner.BlockHashProgram.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.BlockHashProgram.run

/-- info: 'EthLib.EVM.Runner.BlockHashProgram.run_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.BlockHashProgram.run_preserves

/-- info: 'EthLib.EVM.Runner.BlockHashProgram.run_preserves_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.BlockHashProgram.run_preserves_memory

/-- info: 'EthLib.EVM.Runner.BlockHashProgram.program_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.BlockHashProgram.program_pure

/-- info: 'EthLib.EVM.Runner.BlockHashProgram.program_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.BlockHashProgram.program_memory

/-- info: 'EthLib.EVM.Runner.run_logs_unchanged_of_noLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.run_logs_unchanged_of_noLog

/-- info: 'EthLib.EVM.Runner.run_logs_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.run_logs_prefix

/-- info: 'EthLib.EVM.Runner.SelfBalanceProgram.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.SelfBalanceProgram.run

/-- info: 'EthLib.EVM.Runner.SelfBalanceProgram.run_tracker_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.SelfBalanceProgram.run_tracker_retained

/-- info: 'EthLib.EVM.Runner.SelfBalanceProgram.run_persistent_writes_unchanged_of_no_sstore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Runner.SelfBalanceProgram.run_persistent_writes_unchanged_of_no_sstore

/-- info: 'EthLib.EVM.Runner.SelfBalanceProgram.run_tracker_metadata_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Runner.SelfBalanceProgram.run_tracker_metadata_retained

/-- info: 'EthLib.EVM.Runner.SelfBalanceProgram.run_static_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.SelfBalanceProgram.run_static_retained

/-- info: 'EthLib.EVM.Runner.SelfBalanceProgram.run_stateGas_unchanged_of_no_sstore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Runner.SelfBalanceProgram.run_stateGas_unchanged_of_no_sstore

/-- info: 'EthLib.EVM.Runner.run_storageReads_unchanged_of_no_sload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.run_storageReads_unchanged_of_no_sload

/-- info: 'EthLib.EVM.Runner.SloadProgram.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.SloadProgram.run

/-- info: 'EthLib.EVM.Runner.SloadProgram.run_slots_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Runner.SloadProgram.run_slots_monotone

/-- info: 'StaticCallConsumer.suspend_any_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.suspend_any_context

/-- info: 'StaticCallConsumer.underflow_any_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.underflow_any_context

/-- info: 'StaticCallConsumer.suspension_value_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.suspension_value_zero

/-- info: 'StaticCallConsumer.legacy_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.legacy_boundary

/-- info: 'StaticCallConsumer.prepare_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.prepare_forward

/-- info: 'StaticCallConsumer.prepare_converse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.prepare_converse

/-- info: 'StaticCallConsumer.gas_failure_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.gas_failure_exact

/-- info: 'StaticCallConsumer.ready_no_flags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.ready_no_flags

/-- info: 'StaticCallConsumer.ready_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.ready_reads

/-- info: 'StaticCallConsumer.ready_gas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.ready_gas

/-- info: 'StaticCallConsumer.entered_child_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.entered_child_static

/-- info: 'StaticCallConsumer.depth_reject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.depth_reject

/-- info: 'StaticCallConsumer.step_route' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.step_route

/-- info: 'StaticCallConsumer.step_enters_static_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.step_enters_static_child

/-- info: 'StaticCallConsumer.step_gas_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.step_gas_failure

/-- info: 'StaticCallConsumer.static_write_resumes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.static_write_resumes

/-- info: 'StaticCallConsumer.static_sstore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.static_sstore

/-- info: 'StaticCallConsumer.static_tstore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.static_tstore

/-- info: 'StaticCallConsumer.static_value_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.static_value_call

/-- info: 'StaticCallConsumer.trace_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.trace_iff

/-- info: 'StaticCallConsumer.missing_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.missing_forward

/-- info: 'StaticCallConsumer.missing_converse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.missing_converse

/-- info: 'StaticCallConsumer.delegation_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.delegation_forward

/-- info: 'StaticCallConsumer.delegation_converse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.delegation_converse

/-- info: 'StaticCallConsumer.missing_not_delegation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.missing_not_delegation

/-- info: 'StaticCallConsumer.ready_converse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.ready_converse

/-- info: 'StaticCallConsumer.ready_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.ready_forward

/-- info: 'StaticCallConsumer.depth_reject_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.depth_reject_next

/-- info: 'StaticCallConsumer.depth_reject_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.depth_reject_full

/-- info: 'StaticCallConsumer.ripemd_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.ripemd_success

/-- info: 'StaticCallConsumer.ripemd_short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.ripemd_short

/-- info: 'StaticCallConsumer.entry_items_applied' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.entry_items_applied

/-- info: 'StaticCallConsumer.entry_short_applied' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.entry_short_applied

/-- info: 'StaticCallConsumer.entry_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.entry_cases

/-- info: 'StaticCallConsumer.depth_reject_full_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.depth_reject_full_fields

/-- info: 'StaticCallConsumer.static_effect_fields' depends on axioms: [propext] -/
#guard_msgs in
#print axioms StaticCallConsumer.static_effect_fields

/-- info: 'StaticCallConsumer.ripemd_success_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.ripemd_success_fields

/-- info: 'StaticCallConsumer.ripemd_short_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.ripemd_short_fields

/-- info: 'StaticCallConsumer.ripemd_full_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StaticCallConsumer.ripemd_full_fields

/-- info: 'EthLib.EVM.Frame.step_staticcall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frame.step_staticcall

/-- info: 'EthLib.EVM.Frame.staticCallEntry_items' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Frame.staticCallEntry_items

/-- info: 'EthLib.EVM.Frame.staticCallEntry_short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frame.staticCallEntry_short

/-- info: 'EthLib.EVM.Frame.rule_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frame.rule_sound

/-- info: 'EthLib.EVM.Frame.rule_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frame.rule_total

/-- info: 'EthLib.EVM.Frame.step_iff_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frame.step_iff_rule

/-- info: 'EthLib.EVM.Frame.outcome_code_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frame.outcome_code_unchanged

/-- info: 'EthLib.EVM.Frame.outcome_context_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frame.outcome_context_unchanged

/-- info: 'EthLib.EVM.Frame.outcome_returnData_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frame.outcome_returnData_unchanged

/-- info: 'EthLib.EVM.Frame.outcome_memory_unchanged_of_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frame.outcome_memory_unchanged_of_pure
