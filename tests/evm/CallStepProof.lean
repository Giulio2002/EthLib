import EthLib.EVM.Proofs.NestedRunner.Step

open EthLib.EVM

-- Construct and eliminate arbitrary independent nested steps.
theorem call_step_rule_forward (m : NestedRunner.Machine) (result : NestedRunner.Transition)
    (h : NestedRunner.StepSpec m result) : NestedRunner.step m = result :=
  (NestedRunner.step_iff_spec m result).mpr h

theorem call_step_rule_converse (m : NestedRunner.Machine) (result : NestedRunner.Transition)
    (h : NestedRunner.step m = result) :
    ∃ outcome, Frame.Rule m.frame outcome ∧
      match outcome with
      | .callRequest input request => NestedRunner.CallRoute m input request result
      | .staticCallRequest input request => NestedRunner.StaticRoute m input request result
      | _ => NestedRunner.NonCallRoute m outcome result := by
  obtain ⟨outcome, hframe, hroute⟩ := (NestedRunner.step_iff_spec m result).mp h
  exact ⟨outcome, hframe, hroute⟩

-- A continuing frame keeps the complete caller stack and depth.
theorem call_step_continue_observed (m : NestedRunner.Machine) (next : Frame.State)
    (result : NestedRunner.Transition) (hf : Frame.Rule m.frame (.continue next))
    (h : NestedRunner.step m = result) : result = .next { m with frame := next } := by
  have hframe := Frame.rule_sound hf
  have route := (NestedRunner.nonCallRoute_iff m (.continue next) result hframe trivial).mp h
  exact route

-- Construct a continuing nested step from an independent frame rule.
theorem call_step_continue_constructed (m : NestedRunner.Machine) (next : Frame.State)
    (hf : Frame.Rule m.frame (.continue next)) : NestedRunner.step m = .next { m with frame := next } := by
  apply (NestedRunner.step_iff_spec _ _).mpr
  exact ⟨.continue next, hf, rfl⟩

-- Nested STOP incorporates the terminal child according to the independent continuation contract.
theorem call_step_stop_child_observed (m : NestedRunner.Machine) (child : Frame.State)
    (c : NestedRunner.Continuation) (rest : List NestedRunner.Continuation) (result : NestedRunner.Transition)
    (hcallers : m.callers = c :: rest) (hf : Frame.Rule m.frame (.stop child))
    (h : NestedRunner.step m = result) :
    NestedRunner.ResumeOutcomeSpec c child true child.gas ByteArray.empty rest result := by
  have route := (NestedRunner.nonCallRoute_iff m (.stop child) result (Frame.rule_sound hf) trivial).mp h
  simpa [NestedRunner.NonCallRoute, hcallers] using route

-- An independent child-settlement condition constructs nested STOP routing.
theorem call_step_stop_child_constructed (m : NestedRunner.Machine) (child : Frame.State)
    (c : NestedRunner.Continuation) (rest : List NestedRunner.Continuation) (result : NestedRunner.Transition)
    (hcallers : m.callers = c :: rest) (hf : Frame.Rule m.frame (.stop child))
    (h : NestedRunner.ResumeOutcomeSpec c child true child.gas ByteArray.empty rest result) :
    NestedRunner.step m = result := by
  apply (NestedRunner.step_iff_spec _ _).mpr
  refine ⟨.stop child, hf, ?_⟩
  simpa [NestedRunner.NonCallRoute, hcallers] using h

-- An actual CALL suspension exposes the independent preparation and decision cases.
theorem call_step_request_observed (m : NestedRunner.Machine) (input : Frame.State)
    (request : Frame.CallRequest) (result : NestedRunner.Transition)
    (hf : Frame.Rule m.frame (.callRequest input request)) (h : NestedRunner.step m = result) :
    ∃ prep, CallPreparation.OutcomeSpec input request prep ∧
      NestedRunner.CallDecision m request prep result := by
  obtain ⟨prep, hpreparation, hdecision⟩ :=
    (NestedRunner.callRoute_iff m input request result (Frame.rule_sound hf)).mp h
  exact ⟨prep, hpreparation, hdecision⟩

-- The preparation and routing relations construct an actual CALL step.
theorem call_step_request_constructed (m : NestedRunner.Machine) (input : Frame.State)
    (request : Frame.CallRequest) (result : NestedRunner.Transition) (prep : CallPreparation.Result)
    (hf : Frame.Rule m.frame (.callRequest input request))
    (hp : CallPreparation.OutcomeSpec input request prep)
    (hr : NestedRunner.CallDecision m request prep result) : NestedRunner.step m = result := by
  apply (NestedRunner.step_iff_spec _ _).mpr
  exact ⟨.callRequest input request, hf, prep, hp, hr⟩

-- Exhausted traces resume with additional fuel; finished traces remain finished.
theorem call_rule_fuel_split (fuel extra : Nat) (m next : NestedRunner.Machine) (result : NestedRunner.Result)
    (h : NestedRunner.RuleTrace fuel m (.exhausted next)) :
    NestedRunner.RuleTrace (fuel + extra) m result ↔ NestedRunner.RuleTrace extra next result :=
  NestedRunner.ruleTrace_split fuel extra m next result h

theorem call_rule_final_stable (fuel extra : Nat) (m : NestedRunner.Machine) (final : NestedRunner.Final)
    (h : NestedRunner.RuleTrace fuel m final.result) : NestedRunner.RuleTrace (fuel + extra) m final.result :=
  NestedRunner.ruleTrace_final_extra fuel extra m final h

-- RETURN retains its output and uses the same successful continuation contract.
theorem call_step_return_child_observed (m : NestedRunner.Machine) (child : Frame.State)
    (output : ByteArray) (c : NestedRunner.Continuation) (rest : List NestedRunner.Continuation)
    (result : NestedRunner.Transition) (hcallers : m.callers = c :: rest)
    (hf : Frame.Rule m.frame (.returned child output)) (h : NestedRunner.step m = result) :
    NestedRunner.ResumeOutcomeSpec c child true child.gas output rest result := by
  have route := (NestedRunner.nonCallRoute_iff m (.returned child output) result (Frame.rule_sound hf) trivial).mp h
  simpa [NestedRunner.NonCallRoute, hcallers] using route

-- REVERT restores the child spill before passing its gas and bytes to settlement.
theorem call_step_revert_child_observed (m : NestedRunner.Machine) (child : Frame.State)
    (gas : Nat) (output : ByteArray) (c : NestedRunner.Continuation) (rest : List NestedRunner.Continuation)
    (result : NestedRunner.Transition) (hcallers : m.callers = c :: rest)
    (hf : Frame.Rule m.frame (.revert child gas output)) (h : NestedRunner.step m = result) :
    NestedRunner.ResumeOutcomeSpec c child false (gas + child.stateGas.spilled) output rest result := by
  have route := (NestedRunner.nonCallRoute_iff m (.revert child gas output) result (Frame.rule_sound hf) trivial).mp h
  simpa [NestedRunner.NonCallRoute, hcallers] using route

-- A protocol exception runs failure settlement with no child output or execution gas.
theorem call_step_exception_child_observed (m : NestedRunner.Machine) (child : Frame.State)
    (reason : Frame.Exception) (c : NestedRunner.Continuation) (rest : List NestedRunner.Continuation)
    (result : NestedRunner.Transition) (hcallers : m.callers = c :: rest)
    (hreason : reason ≠ .missingCode ∧ reason ≠ .missingStorageAccount)
    (hf : Frame.Rule m.frame (.exception child reason)) (h : NestedRunner.step m = result) :
    NestedRunner.ResumeOutcomeSpec c child false 0 ByteArray.empty rest result := by
  have route := (NestedRunner.nonCallRoute_iff m (.exception child reason) result (Frame.rule_sound hf) trivial).mp h
  simpa [NestedRunner.NonCallRoute, hcallers, hreason.1, hreason.2] using route

-- Missing world data remains tooling regardless of the caller stack.
theorem call_step_missing_code_observed (m : NestedRunner.Machine) (child : Frame.State)
    (result : NestedRunner.Transition) (hf : Frame.Rule m.frame (.exception child .missingCode))
    (h : NestedRunner.step m = result) : result = .done (.tooling child .incompleteWorld) := by
  have route := (NestedRunner.nonCallRoute_iff m (.exception child .missingCode) result (Frame.rule_sound hf) trivial).mp h
  simpa [NestedRunner.NonCallRoute] using route

-- An independently specified ready preparation exposes rejection or child-entry routing.
theorem call_step_ready_observed (m : NestedRunner.Machine) (input : Frame.State)
    (request : Frame.CallRequest) (p : CallPreparation.Prepared) (result : NestedRunner.Transition)
    (hf : Frame.Rule m.frame (.callRequest input request)) (hp : CallPreparation.ReadySpec input request p)
    (h : NestedRunner.step m = result) : NestedRunner.PreparedRoute m request p result := by
  obtain ⟨prep, hpreparation, hdecision⟩ := call_step_request_observed m input request result hf h
  have h1 := (CallPreparation.prepare_iff input request prep).mpr hpreparation
  have h2 := (CallPreparation.ready_iff input request p).mpr hp
  rw [h2] at h1
  cases h1
  exact hdecision

-- Ready preparation and independent route construct the real CALL suspension step.
theorem call_step_ready_constructed (m : NestedRunner.Machine) (input : Frame.State)
    (request : Frame.CallRequest) (p : CallPreparation.Prepared) (result : NestedRunner.Transition)
    (hf : Frame.Rule m.frame (.callRequest input request)) (hp : CallPreparation.ReadySpec input request p)
    (hr : NestedRunner.PreparedRoute m request p result) : NestedRunner.step m = result := by
  apply call_step_request_constructed m input request result (.ready p) hf
  · exact hp
  · exact hr

-- An observed depth rejection recovers restored grants, refund handling and the status result.
theorem call_step_depth_reject_observed (m : NestedRunner.Machine) (input : Frame.State)
    (request : Frame.CallRequest) (p : CallPreparation.Prepared) (result : NestedRunner.Transition)
    (hf : Frame.Rule m.frame (.callRequest input request)) (hp : CallPreparation.ReadySpec input request p)
    (hd : 1024 < m.depth + 1) (h : NestedRunner.step m = result) :
    ∃ restored credited, NestedRunner.GrantRestore p restored ∧
      NestedRunner.RefundSpec false p.newAccountCharged restored credited ∧ NestedRunner.ZeroPushSpec m credited result := by
  have route := call_step_ready_observed m input request p result hf hp h
  rcases route with ⟨_, restored, credited, hrestore, hrefund, hpush⟩ | ⟨hdepth, _, _⟩
  · exact ⟨restored, credited, hrestore, hrefund, hpush⟩
  · omega

-- Insufficient balance has the same restoration path at any depth.
theorem call_step_balance_reject_observed (m : NestedRunner.Machine) (input : Frame.State)
    (request : Frame.CallRequest) (p : CallPreparation.Prepared) (result : NestedRunner.Transition)
    (hf : Frame.Rule m.frame (.callRequest input request)) (hp : CallPreparation.ReadySpec input request p)
    (hb : p.insufficientBalance = true) (h : NestedRunner.step m = result) :
    ∃ restored credited, NestedRunner.GrantRestore p restored ∧
      NestedRunner.RefundSpec false p.newAccountCharged restored credited ∧ NestedRunner.ZeroPushSpec m credited result := by
  have route := call_step_ready_observed m input request p result hf hp h
  rcases route with ⟨_, restored, credited, hrestore, hrefund, hpush⟩ | ⟨_, hbalance, _⟩
  · exact ⟨restored, credited, hrestore, hrefund, hpush⟩
  · simp_all

-- With depth and balance permitted, an actual step exposes the independent entry result.
theorem call_step_entry_observed (m : NestedRunner.Machine) (input : Frame.State)
    (request : Frame.CallRequest) (p : CallPreparation.Prepared) (result : NestedRunner.Transition)
    (hf : Frame.Rule m.frame (.callRequest input request)) (hp : CallPreparation.ReadySpec input request p)
    (hd : m.depth + 1 ≤ 1024) (hb : p.insufficientBalance = false) (h : NestedRunner.step m = result) :
    ∃ entry, NestedRunner.EntrySpec p entry ∧ NestedRunner.EntryDecision m request p entry result := by
  have route := call_step_ready_observed m input request p result hf hp h
  rcases route with ⟨hbad, _⟩ | ⟨_, _, entry, hentry, hdecision⟩
  · rcases hbad with hdeep | hbalance
    · omega
    · simp_all
  · exact ⟨entry, hentry, hdecision⟩

-- Independent rejection, refund and status equations construct the rejected CALL step.
theorem call_step_reject_constructed (m : NestedRunner.Machine) (input : Frame.State)
    (request : Frame.CallRequest) (p : CallPreparation.Prepared) (result : NestedRunner.Transition)
    (restored credited : Frame.State) (hf : Frame.Rule m.frame (.callRequest input request))
    (hp : CallPreparation.ReadySpec input request p)
    (hreject : 1024 < m.depth + 1 ∨ p.insufficientBalance = true)
    (hrestore : NestedRunner.GrantRestore p restored)
    (hrefund : NestedRunner.RefundSpec false p.newAccountCharged restored credited)
    (hpush : NestedRunner.ZeroPushSpec m credited result) : NestedRunner.step m = result :=
  call_step_ready_constructed m input request p result hf hp (Or.inl ⟨hreject, restored, credited, hrestore, hrefund, hpush⟩)

-- A successful non-precompile entry constructs the exact next machine and caller stack.
theorem call_step_child_constructed (m : NestedRunner.Machine) (input : Frame.State)
    (request : Frame.CallRequest) (p : CallPreparation.Prepared) (child : Frame.State)
    (hf : Frame.Rule m.frame (.callRequest input request)) (hp : CallPreparation.ReadySpec input request p)
    (hd : m.depth + 1 ≤ 1024) (hb : p.insufficientBalance = false)
    (he : NestedRunner.EntrySpec p (.ok child)) (hpre : ¬ NestedRunner.PrecompileAddress p.address) :
    NestedRunner.step m = .next ⟨child, m.depth + 1, ⟨p.parent, request, m.depth, p.newAccountCharged⟩ :: m.callers⟩ := by
  apply call_step_ready_constructed m input request p _ hf hp
  have h3 : p.address.val ≠ 3 := by
    intro h
    apply hpre
    simp [NestedRunner.PrecompileAddress, h]
  exact Or.inr ⟨hd, hb, .ok child, he, Or.inr (Or.inr ⟨h3, hpre, rfl⟩)⟩

-- An unavailable precompile is a tooling boundary after independently characterized entry.
theorem call_step_precompile_constructed (m : NestedRunner.Machine) (input : Frame.State)
    (request : Frame.CallRequest) (p : CallPreparation.Prepared) (child : Frame.State)
    (hf : Frame.Rule m.frame (.callRequest input request)) (hp : CallPreparation.ReadySpec input request p)
    (hd : m.depth + 1 ≤ 1024) (hb : p.insufficientBalance = false)
    (he : NestedRunner.EntrySpec p (.ok child)) (hpre : NestedRunner.PrecompileAddress p.address)
    (h3 : p.address.val ≠ 3) :
    NestedRunner.step m = .done (.tooling child .precompile) := by
  apply call_step_ready_constructed m input request p _ hf hp
  exact Or.inr ⟨hd, hb, .ok child, he, Or.inr (Or.inl ⟨h3, hpre, rfl⟩)⟩

-- A checked entry error is preserved as tooling rather than turned into a child halt.
theorem call_step_transfer_error_constructed (m : NestedRunner.Machine) (input : Frame.State)
    (request : Frame.CallRequest) (p : CallPreparation.Prepared) (child : Frame.State)
    (reason : TransactionTransfer.TransferError) (hf : Frame.Rule m.frame (.callRequest input request))
    (hp : CallPreparation.ReadySpec input request p) (hd : m.depth + 1 ≤ 1024)
    (hb : p.insufficientBalance = false) (he : NestedRunner.EntrySpec p (.error (reason, child))) :
    NestedRunner.step m = .done (.tooling child (.transfer reason)) := by
  apply call_step_ready_constructed m input request p _ hf hp
  exact Or.inr ⟨hd, hb, .error (reason, child), he, rfl⟩

-- Preparation tooling is returned without treating it as a protocol exception.
theorem call_step_preparation_tooling_constructed (m : NestedRunner.Machine) (input diagnostic : Frame.State)
    (request : Frame.CallRequest) (reason : CallPreparation.Tooling)
    (hf : Frame.Rule m.frame (.callRequest input request))
    (hp : CallPreparation.OutcomeSpec input request (.tooling diagnostic reason)) :
    NestedRunner.step m = .done (.tooling diagnostic (.preparation reason)) := by
  apply call_step_request_constructed m input request _ (.tooling diagnostic reason) hf hp
  rfl

-- An observed child transition recovers entry, depth, frame and suspended callers.
theorem call_step_child_observed (m : NestedRunner.Machine) (input : Frame.State)
    (request : Frame.CallRequest) (p : CallPreparation.Prepared) (out : NestedRunner.Machine)
    (hf : Frame.Rule m.frame (.callRequest input request)) (hp : CallPreparation.ReadySpec input request p)
    (hd : m.depth + 1 ≤ 1024) (hb : p.insufficientBalance = false)
    (h3 : p.address.val ≠ 3) (h : NestedRunner.step m = .next out) :
    NestedRunner.EntrySpec p (.ok out.frame) ∧ ¬ NestedRunner.PrecompileAddress p.address ∧
      out.depth = m.depth + 1 ∧ out.callers = ⟨p.parent, request, m.depth, p.newAccountCharged⟩ :: m.callers := by
  obtain ⟨entry, he, hdecision⟩ := call_step_entry_observed m input request p (.next out) hf hp hd hb h
  cases entry with
  | error e => cases e; simp [NestedRunner.EntryDecision] at hdecision
  | ok child =>
    simp only [NestedRunner.EntryDecision, NestedRunner.Transition.next.injEq] at hdecision
    rcases hdecision with ⟨ha, _⟩ | ⟨_, _, impossible⟩ | ⟨_, hpre, hmachine⟩
    · contradiction
    · contradiction
    · cases hmachine
      exact ⟨he, hpre, rfl, rfl⟩

-- An observed precompile boundary recovers its address class and exact child entry.
theorem call_step_precompile_observed (m : NestedRunner.Machine) (input : Frame.State)
    (request : Frame.CallRequest) (p : CallPreparation.Prepared) (child : Frame.State)
    (hf : Frame.Rule m.frame (.callRequest input request)) (hp : CallPreparation.ReadySpec input request p)
    (hd : m.depth + 1 ≤ 1024) (hb : p.insufficientBalance = false)
    (h3 : p.address.val ≠ 3) (h : NestedRunner.step m = .done (.tooling child .precompile)) :
    NestedRunner.EntrySpec p (.ok child) ∧ NestedRunner.PrecompileAddress p.address := by
  obtain ⟨entry, he, hdecision⟩ := call_step_entry_observed m input request p _ hf hp hd hb h
  cases entry with
  | error e => cases e; simp [NestedRunner.EntryDecision] at hdecision
  | ok entered =>
    simp only [NestedRunner.EntryDecision, NestedRunner.Transition.done.injEq,
      NestedRunner.Final.tooling.injEq] at hdecision
    rcases hdecision with ⟨ha, _⟩ | ⟨_, hpre, hframe, _⟩ | ⟨_, _, impossible⟩
    · contradiction
    · subst entered
      exact ⟨he, hpre⟩
    · contradiction

-- A transfer tooling result recovers the matching independent failed entry.
theorem call_step_transfer_error_observed (m : NestedRunner.Machine) (input : Frame.State)
    (request : Frame.CallRequest) (p : CallPreparation.Prepared) (child : Frame.State)
    (reason : TransactionTransfer.TransferError) (hf : Frame.Rule m.frame (.callRequest input request))
    (hp : CallPreparation.ReadySpec input request p) (hd : m.depth + 1 ≤ 1024)
    (hb : p.insufficientBalance = false)
    (h : NestedRunner.step m = .done (.tooling child (.transfer reason))) :
    NestedRunner.EntrySpec p (.error (reason, child)) := by
  obtain ⟨entry, he, hdecision⟩ := call_step_entry_observed m input request p _ hf hp hd hb h
  cases entry with
  | ok entered =>
    simp only [NestedRunner.EntryDecision] at hdecision
    rcases hdecision with ⟨_, hripemd⟩ | ⟨_, _, impossible⟩ | ⟨_, _, impossible⟩
    · simp [NestedRunner.RipemdSpec, NestedRunner.ResumeOutcomeSpec] at hripemd
    · simp at impossible
    · simp at impossible
  | error err =>
    rcases err with ⟨why, entered⟩
    simp only [NestedRunner.EntryDecision, NestedRunner.Transition.done.injEq,
      NestedRunner.Final.tooling.injEq, NestedRunner.Tooling.transfer.injEq] at hdecision
    rcases hdecision with ⟨hframe, hreason⟩
    subst entered
    subst why
    exact he

-- Independent RETURN settlement constructs the corresponding nested step.
theorem call_step_return_child_constructed (m : NestedRunner.Machine) (child : Frame.State)
    (output : ByteArray) (c : NestedRunner.Continuation) (rest : List NestedRunner.Continuation)
    (result : NestedRunner.Transition) (hcallers : m.callers = c :: rest)
    (hf : Frame.Rule m.frame (.returned child output))
    (hr : NestedRunner.ResumeOutcomeSpec c child true child.gas output rest result) :
    NestedRunner.step m = result := by
  apply (NestedRunner.step_iff_spec _ _).mpr
  refine ⟨.returned child output, hf, ?_⟩
  simpa [NestedRunner.NonCallRoute, hcallers] using hr

-- Independent REVERT settlement constructs the corresponding nested step.
theorem call_step_revert_child_constructed (m : NestedRunner.Machine) (child : Frame.State)
    (gas : Nat) (output : ByteArray) (c : NestedRunner.Continuation) (rest : List NestedRunner.Continuation)
    (result : NestedRunner.Transition) (hcallers : m.callers = c :: rest)
    (hf : Frame.Rule m.frame (.revert child gas output))
    (hr : NestedRunner.ResumeOutcomeSpec c child false (gas + child.stateGas.spilled) output rest result) :
    NestedRunner.step m = result := by
  apply (NestedRunner.step_iff_spec _ _).mpr
  refine ⟨.revert child gas output, hf, ?_⟩
  simpa [NestedRunner.NonCallRoute, hcallers] using hr

-- A source protocol exception uses failure settlement in the caller.
theorem call_step_exception_child_constructed (m : NestedRunner.Machine) (child : Frame.State)
    (reason : Frame.Exception) (c : NestedRunner.Continuation) (rest : List NestedRunner.Continuation)
    (result : NestedRunner.Transition) (hcallers : m.callers = c :: rest)
    (hreason : reason ≠ .missingCode ∧ reason ≠ .missingStorageAccount)
    (hf : Frame.Rule m.frame (.exception child reason))
    (hr : NestedRunner.ResumeOutcomeSpec c child false 0 ByteArray.empty rest result) :
    NestedRunner.step m = result := by
  apply (NestedRunner.step_iff_spec _ _).mpr
  refine ⟨.exception child reason, hf, ?_⟩
  simpa [NestedRunner.NonCallRoute, hcallers, hreason.1, hreason.2] using hr

-- An independently specified preparation gas error takes the exception route.
theorem call_step_preparation_gas_constructed (m : NestedRunner.Machine) (input diagnostic : Frame.State)
    (request : Frame.CallRequest) (result : NestedRunner.Transition)
    (hf : Frame.Rule m.frame (.callRequest input request))
    (hp : CallPreparation.OutcomeSpec input request (.outOfGas diagnostic))
    (hr : NestedRunner.ExceptionalRoute m diagnostic .outOfGas result) : NestedRunner.step m = result := by
  apply call_step_request_constructed m input request result (.outOfGas diagnostic) hf hp
  exact hr

-- Observing a preparation gas branch recovers the exception route for its diagnostic.
theorem call_step_preparation_gas_observed (m : NestedRunner.Machine) (input diagnostic : Frame.State)
    (request : Frame.CallRequest) (result : NestedRunner.Transition)
    (hf : Frame.Rule m.frame (.callRequest input request))
    (hp : CallPreparation.OutcomeSpec input request (.outOfGas diagnostic))
    (h : NestedRunner.step m = result) : NestedRunner.ExceptionalRoute m diagnostic .outOfGas result := by
  obtain ⟨prep, hpreparation, hdecision⟩ := call_step_request_observed m input request result hf h
  have h1 := (CallPreparation.prepare_iff input request prep).mpr hpreparation
  have h2 := (CallPreparation.prepare_iff input request (.outOfGas diagnostic)).mpr hp
  rw [h2] at h1
  cases h1
  exact hdecision

-- Preparation tooling has a unique diagnostic, recovered from the independent specification.
theorem call_step_preparation_tooling_observed (m : NestedRunner.Machine) (input diagnostic : Frame.State)
    (request : Frame.CallRequest) (reason : CallPreparation.Tooling) (result : NestedRunner.Transition)
    (hf : Frame.Rule m.frame (.callRequest input request))
    (hp : CallPreparation.OutcomeSpec input request (.tooling diagnostic reason))
    (h : NestedRunner.step m = result) : result = .done (.tooling diagnostic (.preparation reason)) := by
  obtain ⟨prep, hpreparation, hdecision⟩ := call_step_request_observed m input request result hf h
  have h1 := (CallPreparation.prepare_iff input request prep).mpr hpreparation
  have h2 := (CallPreparation.prepare_iff input request (.tooling diagnostic reason)).mpr hp
  rw [h2] at h1
  cases h1
  exact hdecision

-- Root STOP has exactly the terminal stopped result.
theorem call_step_root_stop_iff (m : NestedRunner.Machine) (child : Frame.State)
    (result : NestedRunner.Transition) (hcallers : m.callers = [])
    (hf : Frame.Rule m.frame (.stop child)) :
    NestedRunner.step m = result ↔ result = .done (.terminal (.stopped child)) := by
  simpa [NestedRunner.NonCallRoute, hcallers] using
    NestedRunner.nonCallRoute_iff m (.stop child) result (Frame.rule_sound hf) trivial

-- Root RETURN retains its actual byte output.
theorem call_step_root_return_iff (m : NestedRunner.Machine) (child : Frame.State) (output : ByteArray)
    (result : NestedRunner.Transition) (hcallers : m.callers = [])
    (hf : Frame.Rule m.frame (.returned child output)) :
    NestedRunner.step m = result ↔ result = .done (.terminal (.returned child output)) := by
  simpa [NestedRunner.NonCallRoute, hcallers] using
    NestedRunner.nonCallRoute_iff m (.returned child output) result (Frame.rule_sound hf) trivial

-- Root REVERT retains the supplied gas and bytes.
theorem call_step_root_revert_iff (m : NestedRunner.Machine) (child : Frame.State) (gas : Nat)
    (output : ByteArray) (result : NestedRunner.Transition) (hcallers : m.callers = [])
    (hf : Frame.Rule m.frame (.revert child gas output)) :
    NestedRunner.step m = result ↔ result = .done (.terminal (.reverted child gas output)) := by
  simpa [NestedRunner.NonCallRoute, hcallers] using
    NestedRunner.nonCallRoute_iff m (.revert child gas output) result (Frame.rule_sound hf) trivial

-- Root protocol exceptions retain their diagnostic frame and exception kind.
theorem call_step_root_exception_iff (m : NestedRunner.Machine) (child : Frame.State)
    (reason : Frame.Exception) (result : NestedRunner.Transition) (hcallers : m.callers = [])
    (hreason : reason ≠ .missingCode ∧ reason ≠ .missingStorageAccount)
    (hf : Frame.Rule m.frame (.exception child reason)) :
    NestedRunner.step m = result ↔ result = .done (.terminal (.exception child reason)) := by
  simpa [NestedRunner.NonCallRoute, hcallers, hreason.1, hreason.2] using
    NestedRunner.nonCallRoute_iff m (.exception child reason) result (Frame.rule_sound hf) trivial

-- Either missing-state diagnostic is a tooling result for any caller stack.
theorem call_step_missing_storage_iff (m : NestedRunner.Machine) (child : Frame.State)
    (result : NestedRunner.Transition) (hf : Frame.Rule m.frame (.exception child .missingStorageAccount)) :
    NestedRunner.step m = result ↔ result = .done (.tooling child .incompleteWorld) := by
  simpa [NestedRunner.NonCallRoute] using
    NestedRunner.nonCallRoute_iff m (.exception child .missingStorageAccount) result (Frame.rule_sound hf) trivial

theorem call_step_missing_code_iff (m : NestedRunner.Machine) (child : Frame.State)
    (result : NestedRunner.Transition) (hf : Frame.Rule m.frame (.exception child .missingCode)) :
    NestedRunner.step m = result ↔ result = .done (.tooling child .incompleteWorld) := by
  simpa [NestedRunner.NonCallRoute] using
    NestedRunner.nonCallRoute_iff m (.exception child .missingCode) result (Frame.rule_sound hf) trivial

-- Unsupported instructions retain their opcode and diagnostic frame.
theorem call_step_unsupported_iff (m : NestedRunner.Machine) (child : Frame.State) (op : Opcode)
    (result : NestedRunner.Transition) (hf : Frame.Rule m.frame (.unsupported child op)) :
    NestedRunner.step m = result ↔ result = .done (.tooling child (.unsupported op)) := by
  simpa [NestedRunner.NonCallRoute] using
    NestedRunner.nonCallRoute_iff m (.unsupported child op) result (Frame.rule_sound hf) trivial

-- A rejected CALL that continues exposes every restored and resulting machine field.
theorem call_step_reject_next_fields (m : NestedRunner.Machine) (input : Frame.State)
    (request : Frame.CallRequest) (p : CallPreparation.Prepared) (out : NestedRunner.Machine)
    (hf : Frame.Rule m.frame (.callRequest input request)) (hp : CallPreparation.ReadySpec input request p)
    (hd : 1024 < m.depth + 1) (h : NestedRunner.step m = .next out) :
    ∃ restored credited : Frame.State,
      restored.code = p.parent.code ∧ restored.pc = p.parent.pc ∧ restored.stack = p.parent.stack ∧
      restored.gas = p.parent.gas + p.childGas ∧ restored.memory = p.parent.memory ∧
      restored.context = p.parent.context ∧ restored.returnData = p.parent.returnData ∧
      restored.tracker = p.parent.tracker ∧ restored.warmAddresses = p.parent.warmAddresses ∧
      restored.warmSlots = p.parent.warmSlots ∧ restored.isStatic = p.parent.isStatic ∧ restored.logs = p.parent.logs ∧
      restored.stateGas.reservoir = p.parent.stateGas.reservoir + p.stateGrant ∧
      restored.stateGas.baseline = p.parent.stateGas.baseline ∧
      restored.stateGas.refundCounter = p.parent.stateGas.refundCounter ∧
      restored.stateGas.spilled = p.parent.stateGas.spilled ∧
      restored.stateGas.committedSpill = p.parent.stateGas.committedSpill ∧
      NestedRunner.RefundSpec false p.newAccountCharged restored credited ∧
      credited.stack.val.length < 1024 ∧ out.depth = m.depth ∧ out.callers = m.callers ∧
      out.frame.code = credited.code ∧ out.frame.pc = credited.pc + 1 ∧
      out.frame.stack.val = 0 :: credited.stack.val ∧ out.frame.gas = credited.gas ∧
      out.frame.memory = credited.memory ∧ out.frame.context = credited.context ∧
      out.frame.returnData = credited.returnData ∧ out.frame.tracker = credited.tracker ∧
      out.frame.warmAddresses = credited.warmAddresses ∧ out.frame.warmSlots = credited.warmSlots ∧
      out.frame.isStatic = credited.isStatic ∧ out.frame.stateGas = credited.stateGas ∧ out.frame.logs = credited.logs := by
  obtain ⟨restored, credited, hrestore, hrefund, hpush⟩ :=
    call_step_depth_reject_observed m input request p (.next out) hf hp hd h
  rcases hrestore with ⟨hcode, hpc, hstack, hgas, hmemory, hcontext, hdata, htracker,
    hwarm, hslots, hstatic, hlogs, hres, hbase, hcounter, hspill, hcommitted⟩
  rcases hpush with ⟨hroom, hdepth, hcallers, hcode', hpc', hstack', hgas', hmemory',
    hcontext', hdata', htracker', hwarm', hslots', hstatic', hstate', hlogs'⟩
  exact ⟨restored, credited, hcode, hpc, hstack, hgas, hmemory, hcontext, hdata, htracker,
    hwarm, hslots, hstatic, hlogs, hres, hbase, hcounter, hspill, hcommitted, hrefund,
    hroom, hdepth, hcallers, hcode', hpc', hstack', hgas', hmemory', hcontext', hdata',
    htracker', hwarm', hslots', hstatic', hstate', hlogs'⟩

-- A protocol terminal trace and the bounded run determine each other.
theorem call_rule_terminal_iff (fuel : Nat) (m : NestedRunner.Machine) (terminal : Runner.Result) :
    NestedRunner.run fuel m = .terminal terminal ↔ NestedRunner.RuleTrace fuel m (.terminal terminal) :=
  NestedRunner.run_iff_ruleTrace fuel m (.terminal terminal)

-- Fuel exhaustion records a resumable machine rather than a protocol terminal result.
theorem call_rule_exhaustion_iff (fuel : Nat) (m next : NestedRunner.Machine) :
    NestedRunner.run fuel m = .exhausted next ↔ NestedRunner.RuleTrace fuel m (.exhausted next) :=
  NestedRunner.run_iff_ruleTrace fuel m (.exhausted next)

-- At zero fuel the trace retains the whole machine exactly.
theorem call_rule_zero (m : NestedRunner.Machine) : NestedRunner.RuleTrace 0 m (.exhausted m) :=
  .exhausted m

-- Tooling results also have an independent bounded trace.
theorem call_rule_tooling_iff (fuel : Nat) (m : NestedRunner.Machine) (frame : Frame.State)
    (reason : NestedRunner.Tooling) :
    NestedRunner.run fuel m = .tooling frame reason ↔
      NestedRunner.RuleTrace fuel m (.tooling frame reason) :=
  NestedRunner.run_iff_ruleTrace fuel m (.tooling frame reason)

-- An observed precompile transition separates the exact gas and settlement cases.
theorem ripemd_observed (c : NestedRunner.Continuation) (child : Frame.State)
    (rest : List NestedRunner.Continuation) (result : NestedRunner.Transition)
    (h : NestedRunner.ripemdCall c child rest = result) :
    (child.gas < 600 + 120 * ((child.context.data.size + 31) / 32) ∧
      NestedRunner.ResumeOutcomeSpec c child false 0 ByteArray.empty rest result) ∨
    (600 + 120 * ((child.context.data.size + 31) / 32) ≤ child.gas ∧
      NestedRunner.ResumeOutcomeSpec c child true
        (child.gas - (600 + 120 * ((child.context.data.size + 31) / 32)))
        (EthLib.Execution.Evm.Precompiles.Ripemd160.ripemd160 child.context.data) rest result) :=
  (NestedRunner.ripemdCall_iff c child rest result).mp h

-- Independent affordable-gas and settlement facts construct the transition.
theorem ripemd_success_constructed (c : NestedRunner.Continuation) (child : Frame.State)
    (rest : List NestedRunner.Continuation) (result : NestedRunner.Transition)
    (hgas : 600 + 120 * ((child.context.data.size + 31) / 32) ≤ child.gas)
    (hresume : NestedRunner.ResumeOutcomeSpec c child true
      (child.gas - (600 + 120 * ((child.context.data.size + 31) / 32)))
      (EthLib.Execution.Evm.Precompiles.Ripemd160.ripemd160 child.context.data) rest result) :
    NestedRunner.ripemdCall c child rest = result :=
  (NestedRunner.ripemdCall_iff c child rest result).mpr (Or.inr ⟨hgas, hresume⟩)

-- Insufficient precompile gas constructs an exceptional child with no output.
theorem ripemd_oog_constructed (c : NestedRunner.Continuation) (child : Frame.State)
    (rest : List NestedRunner.Continuation) (result : NestedRunner.Transition)
    (hgas : child.gas < 600 + 120 * ((child.context.data.size + 31) / 32))
    (hresume : NestedRunner.ResumeOutcomeSpec c child false 0 ByteArray.empty rest result) :
    NestedRunner.ripemdCall c child rest = result :=
  (NestedRunner.ripemdCall_iff c child rest result).mpr (Or.inl ⟨hgas, hresume⟩)

-- A prepared address-3 call composes independent entry and precompile settlement.
theorem call_step_ripemd_constructed (m : NestedRunner.Machine) (input : Frame.State)
    (request : Frame.CallRequest) (p : CallPreparation.Prepared) (child : Frame.State)
    (result : NestedRunner.Transition)
    (hf : Frame.Rule m.frame (.callRequest input request)) (hp : CallPreparation.ReadySpec input request p)
    (hd : m.depth + 1 ≤ 1024) (hb : p.insufficientBalance = false)
    (he : NestedRunner.EntrySpec p (.ok child)) (h3 : p.address.val = 3)
    (hr : NestedRunner.RipemdSpec ⟨p.parent, request, m.depth, p.newAccountCharged⟩ child m.callers result) :
    NestedRunner.step m = result := by
  apply call_step_ready_constructed m input request p result hf hp
  exact Or.inr ⟨hd, hb, .ok child, he, Or.inl ⟨h3, hr⟩⟩

-- An observed address-3 continuation recovers the independently specified entry and settlement.
theorem call_step_ripemd_observed (m : NestedRunner.Machine) (input : Frame.State)
    (request : Frame.CallRequest) (p : CallPreparation.Prepared) (out : NestedRunner.Machine)
    (hf : Frame.Rule m.frame (.callRequest input request)) (hp : CallPreparation.ReadySpec input request p)
    (hd : m.depth + 1 ≤ 1024) (hb : p.insufficientBalance = false)
    (h3 : p.address.val = 3) (h : NestedRunner.step m = .next out) :
    ∃ child, NestedRunner.EntrySpec p (.ok child) ∧
      NestedRunner.RipemdSpec ⟨p.parent, request, m.depth, p.newAccountCharged⟩ child m.callers (.next out) := by
  obtain ⟨entry, he, hr⟩ := call_step_entry_observed m input request p (.next out) hf hp hd hb h
  cases entry with
  | error e => cases e; simp [NestedRunner.EntryDecision] at hr
  | ok child =>
    rcases hr with ⟨_, hspec⟩ | ⟨hne, _⟩ | ⟨hne, _⟩
    · exact ⟨child, he, hspec⟩
    · contradiction
    · contradiction

-- A failed hash that resumes the caller exposes rollback and the refund meter cases.
theorem ripemd_failed_next_fields (c : NestedRunner.Continuation) (child : Frame.State)
    (rest : List NestedRunner.Continuation) (out : NestedRunner.Machine)
    (hgas : child.gas < 600 + 120 * ((child.context.data.size + 31) / 32))
    (hcharged : c.newAccountCharged = true)
    (h : NestedRunner.ripemdCall c child rest = .next out) :
    ∃ incorporated credited : Frame.State, ∃ saved tail,
      child.stateGas.committedSpill = 0 ∧ child.tracker.snapshots = saved :: tail ∧
      incorporated.tracker.writes = saved ∧ incorporated.tracker.accountReads = child.tracker.accountReads ∧
      incorporated.tracker.storageReads = child.tracker.storageReads ∧
      incorporated.tracker.createdAccounts = child.tracker.createdAccounts ∧
      incorporated.tracker.snapshots = tail ∧ incorporated.logs = c.parent.logs ∧
      incorporated.warmAddresses = c.parent.warmAddresses ∧ incorporated.warmSlots = c.parent.warmSlots ∧
      incorporated.returnData = ByteArray.empty ∧
      incorporated.gas = c.parent.gas ∧
      incorporated.stateGas.reservoir = c.parent.stateGas.reservoir + child.stateGas.baseline ∧
      incorporated.stateGas.baseline = c.parent.stateGas.baseline ∧
      incorporated.stateGas.refundCounter = c.parent.stateGas.refundCounter ∧
      incorporated.stateGas.spilled = c.parent.stateGas.spilled ∧
      incorporated.stateGas.committedSpill = c.parent.stateGas.committedSpill ∧
      Gas.StateMeter.CreditEffect (Frame.stateMeter incorporated) (Frame.stateMeter credited) 183600 ∧
      credited.stack.val.length < 1024 ∧ out.depth = c.depth ∧ out.callers = rest ∧
      out.frame.code = credited.code ∧ out.frame.pc = credited.pc + 1 ∧
      out.frame.stack.val = 0 :: credited.stack.val ∧ out.frame.gas = credited.gas ∧
      out.frame.context = credited.context ∧ out.frame.returnData = credited.returnData ∧
      out.frame.tracker = credited.tracker ∧ out.frame.warmAddresses = credited.warmAddresses ∧
      out.frame.warmSlots = credited.warmSlots ∧ out.frame.isStatic = credited.isStatic ∧
      out.frame.stateGas = credited.stateGas ∧ out.frame.logs = credited.logs := by
  have hs := (ripemd_observed c child rest (.next out) h)
  rcases hs with ⟨_, hs⟩ | ⟨ha, _⟩
  · change NestedRunner.ResumeSuccess c child false 0 ByteArray.empty rest out at hs
    rcases hs with ⟨inc, credit, he, hr, hroom, hdepth, hcallers, hc, hp, hstack, hg, hm, hw,
      hctx, hret, ht, ha, hslots, hstatic, hstate, hlogs⟩
    rcases he with ⟨saved, tail, he⟩
    rcases hr with ⟨bad, _⟩ | ⟨_, _, hcredit⟩
    · simp [hcharged] at bad
    · refine ⟨inc, credit, saved, tail, ?_⟩
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
        Nat.sub_zero] at he
      simp only [NestedRunner.CreditFields] at hcredit
      rcases he with ⟨hz, hsnap, _, _, _, _, _, hdata, _, _, hwrites, hreads, hstorage, hcreated,
        hsnapout, hlog, hwarm, hslot, hgas', hres, hbase, hrefund, hspill, hcommitted⟩
      simp only [Int.add_zero] at hrefund
      exact ⟨hz, hsnap, hwrites, hreads, hstorage, hcreated, hsnapout, hlog, hwarm, hslot,
        hdata, hgas', hres, hbase, hrefund, hspill, hcommitted, hcredit.2.2.2.2.2.2.2.2.2.2.2,
        hroom, hdepth, hcallers, hc, hp, hstack, hg, hctx, hret, ht, ha, hslots, hstatic, hstate, hlogs⟩
  · omega

-- The prepared zero-request value call receives the stipend and records the new-account charge.
theorem prepared_new_account_stipend (s : Frame.State) (r : Frame.CallRequest)
    (p : CallPreparation.Prepared) (hprepare : CallPreparation.prepare s r = .ready p)
    (hzero : r.gas = 0) (hvalue : r.value ≠ 0)
    (hnew : CallPreparation.NewAccount s r) :
    p.childGas = 2300 ∧ p.newAccountCharged = true ∧
      ∃ meter, Gas.StateMeter.ChargeEffect (CallPreparation.InitialMeter s r) meter 183600 ∧
        p.stateGrant = meter.stateGas ∧ p.parent.gas = meter.executionGas := by
  have ready := CallPreparation.ready_refines s r p hprepare
  rcases ready with ⟨code, meter, forwarded, _, _, _, hcharge, hforward, _, _, _, hchild, hgrant, hflag, _, _, _, _, hparent, _⟩
  have hf : forwarded = 0 := by simp [hforward, hzero]
  have hv : r.value.toNat ≠ 0 := by
    intro hz
    apply hvalue
    apply BitVec.eq_of_toNat_eq
    simpa using hz
  rcases hcharge with ⟨_, hcharge⟩ | ⟨hn, _⟩
  · refine ⟨?_, (hflag.mpr hnew), meter, hcharge, hgrant, ?_⟩
    · simpa [hf, hv] using hchild
    · simpa [hf] using hparent
  · contradiction

-- Preparation, entry, execution and observed continuation compose for the failed new-account case.
theorem call_step_failed_new_account_refund (m : NestedRunner.Machine) (input : Frame.State)
    (r : Frame.CallRequest) (p : CallPreparation.Prepared) (out : NestedRunner.Machine)
    (hf : Frame.Rule m.frame (.callRequest input r)) (hprepare : CallPreparation.prepare input r = .ready p)
    (hd : m.depth + 1 ≤ 1024) (hb : p.insufficientBalance = false)
    (haddress : p.address.val = 3) (hzero : r.gas = 0) (hvalue : r.value ≠ 0)
    (hnew : CallPreparation.NewAccount input r) (hlen : r.inputSize.toNat = 1400)
    (hstep : NestedRunner.step m = .next out) :
    ∃ (child incorporated credited : Frame.State) (saved : TransactionState.Snapshot) (tail : List TransactionState.Snapshot),
      child.gas = 2300 ∧ child.context.data.size = 1400 ∧
      child.stateGas.committedSpill = 0 ∧ child.tracker.snapshots = saved :: tail ∧
      incorporated.tracker.writes = saved ∧ incorporated.logs = p.parent.logs ∧
      incorporated.gas = p.parent.gas ∧
      incorporated.stateGas.reservoir = p.parent.stateGas.reservoir + child.stateGas.baseline ∧
      Gas.StateMeter.CreditEffect (Frame.stateMeter incorporated) (Frame.stateMeter credited) 183600 ∧
      out.frame.stack.val = 0 :: credited.stack.val ∧ out.frame.tracker = credited.tracker ∧
      out.frame.stateGas = credited.stateGas ∧ out.depth = m.depth ∧ out.callers = m.callers := by
  have hp := CallPreparation.ready_refines input r p hprepare
  obtain ⟨child, he, hr⟩ := call_step_ripemd_observed m input r p out hf hp hd hb haddress hstep
  have ⟨hgrant, hflag, _⟩ := prepared_new_account_stipend input r p hprepare hzero hvalue hnew
  rcases he with ⟨_, _, hshape, _⟩
  rcases hshape with ⟨_, _, _, hchildgas, _, _, _, hbytes, _⟩
  have hrequest : p.request = r := by
    rcases hp with ⟨_, _, _, _, _, _, _, _, hrequest, _⟩
    exact hrequest
  have hcgas : child.gas = 2300 := hchildgas.trans hgrant
  have hcsize : child.context.data.size = 1400 := by
    have hsize := hbytes.1
    rw [hrequest, hlen] at hsize
    exact hsize
  have hoom : child.gas < 600 + 120 * ((child.context.data.size + 31) / 32) := by
    rw [hcgas, hcsize]
    decide
  have hcall := (NestedRunner.ripemdCall_iff _ _ _ _).mpr hr
  have hfields := ripemd_failed_next_fields ⟨p.parent, r, m.depth, p.newAccountCharged⟩ child m.callers out hoom hflag hcall
  rcases hfields with ⟨inc, credit, saved, tail, hz, hsnap, hwrites, _, _, _, _, hlogs,
    _, _, _, hgas, hres, _, _, _, _, hcredit, _, hdepth, hcallers, _, _, hstack, _,
    _, _, htracker, _, _, _, hstate, _⟩
  exact ⟨child, inc, credit, saved, tail, hcgas, hcsize, hz, hsnap, hwrites, hlogs,
    hgas, hres, hcredit, hstack, htracker, hstate, hdepth, hcallers⟩

-- An observed out-of-gas diagnostic exposes spill priority, missing checkpoint, or a full caller stack.
theorem ripemd_failed_diagnostic (c : NestedRunner.Continuation) (child diagnostic : Frame.State)
    (rest : List NestedRunner.Continuation)
    (hgas : child.gas < 600 + 120 * ((child.context.data.size + 31) / 32))
    (h : NestedRunner.ripemdCall c child rest = .done (.tooling diagnostic .invalidContinuation)) :
    (diagnostic = child ∧ (child.stateGas.committedSpill ≠ 0 ∨
      (child.stateGas.committedSpill = 0 ∧ child.tracker.snapshots = []))) ∨
    ∃ incorporated credited : Frame.State, ∃ saved tail,
      child.stateGas.committedSpill = 0 ∧ child.tracker.snapshots = saved :: tail ∧
      incorporated.tracker.writes = saved ∧ incorporated.logs = c.parent.logs ∧
      incorporated.returnData = ByteArray.empty ∧
      NestedRunner.RefundSpec false c.newAccountCharged incorporated credited ∧
      credited.stack.val.length = 1024 ∧ diagnostic = credited := by
  rcases ripemd_observed c child rest (.done (.tooling diagnostic .invalidContinuation)) h with ⟨_, hr⟩ | ⟨ha, _⟩
  · change NestedRunner.ResumeFailure c child false 0 ByteArray.empty diagnostic at hr
    rcases hr with hbad | ⟨inc, credit, he, hrefund, hfull, hdiag⟩
    · exact Or.inl hbad
    · rcases he with ⟨saved, tail, hz, hs, _, _, _, _, _, hdata, _, _, hwrites, _, _, _, _, hlogs, _⟩
      exact Or.inr ⟨inc, credit, saved, tail, hz, hs, hwrites, hlogs, hdata, hrefund, hfull, hdiag⟩
  · omega

-- An affordable observed hash exposes the committed child and the complete parent continuation.
theorem ripemd_success_next_fields (c : NestedRunner.Continuation) (child : Frame.State)
    (rest : List NestedRunner.Continuation) (out : NestedRunner.Machine)
    (hgas : 600 + 120 * ((child.context.data.size + 31) / 32) ≤ child.gas)
    (h : NestedRunner.ripemdCall c child rest = .next out) :
    ∃ incorporated : Frame.State, ∃ saved tail,
      child.stateGas.committedSpill = 0 ∧ child.tracker.snapshots = saved :: tail ∧
      incorporated.code = c.parent.code ∧ incorporated.pc = c.parent.pc ∧
      incorporated.stack = c.parent.stack ∧ incorporated.memory = c.parent.memory ∧
      incorporated.context = c.parent.context ∧
      incorporated.returnData = EthLib.Execution.Evm.Precompiles.Ripemd160.ripemd160 child.context.data ∧
      incorporated.isStatic = c.parent.isStatic ∧
      incorporated.tracker.parent = child.tracker.parent ∧ incorporated.tracker.writes = child.tracker.writes ∧
      incorporated.tracker.accountReads = child.tracker.accountReads ∧
      incorporated.tracker.storageReads = child.tracker.storageReads ∧
      incorporated.tracker.createdAccounts = child.tracker.createdAccounts ∧
      incorporated.tracker.snapshots = tail ∧ incorporated.logs = c.parent.logs ++ child.logs ∧
      incorporated.warmAddresses = child.warmAddresses ++ c.parent.warmAddresses ∧
      incorporated.warmSlots = child.warmSlots ++ c.parent.warmSlots ∧
      incorporated.stack.val.length < 1024 ∧ out.depth = c.depth ∧ out.callers = rest ∧
      out.frame.code = incorporated.code ∧ out.frame.pc = incorporated.pc + 1 ∧
      out.frame.stack.val = 1 :: incorporated.stack.val ∧ out.frame.gas = incorporated.gas ∧
      out.frame.memory.store = List.zip
        (List.range' c.request.outputOffset.toNat
          ((EthLib.Execution.Evm.Precompiles.Ripemd160.ripemd160 child.context.data).data.toList.take c.request.outputSize.toNat).length)
        ((EthLib.Execution.Evm.Precompiles.Ripemd160.ripemd160 child.context.data).data.toList.take c.request.outputSize.toNat) ++ incorporated.memory.store ∧
      out.frame.memory.words = max incorporated.memory.words
        (Memory.Allocation.requiredWords c.request.outputOffset.toNat
          ((EthLib.Execution.Evm.Precompiles.Ripemd160.ripemd160 child.context.data).data.toList.take c.request.outputSize.toNat).length) ∧
      out.frame.context = incorporated.context ∧ out.frame.returnData = incorporated.returnData ∧
      out.frame.tracker = incorporated.tracker ∧ out.frame.warmAddresses = incorporated.warmAddresses ∧
      out.frame.warmSlots = incorporated.warmSlots ∧ out.frame.isStatic = incorporated.isStatic ∧
      out.frame.stateGas = incorporated.stateGas ∧ out.frame.logs = incorporated.logs ∧
      incorporated.gas = c.parent.gas + (child.gas - (600 + 120 * ((child.context.data.size + 31) / 32))) +
        min (c.parent.stateGas.reservoir + child.stateGas.reservoir) (c.parent.stateGas.spilled + child.stateGas.spilled) ∧
      incorporated.stateGas.reservoir = c.parent.stateGas.reservoir + child.stateGas.reservoir -
        min (c.parent.stateGas.reservoir + child.stateGas.reservoir) (c.parent.stateGas.spilled + child.stateGas.spilled) ∧
      incorporated.stateGas.baseline = c.parent.stateGas.baseline ∧
      incorporated.stateGas.refundCounter = c.parent.stateGas.refundCounter + child.stateGas.refundCounter ∧
      incorporated.stateGas.spilled = c.parent.stateGas.spilled + child.stateGas.spilled -
        min (c.parent.stateGas.reservoir + child.stateGas.reservoir) (c.parent.stateGas.spilled + child.stateGas.spilled) ∧
      incorporated.stateGas.committedSpill = c.parent.stateGas.committedSpill := by
  rcases ripemd_observed c child rest (.next out) h with ⟨ha, _⟩ | ⟨_, hr⟩
  · omega
  · change NestedRunner.ResumeSuccess c child true _ _ rest out at hr
    rcases hr with ⟨inc, credit, he, hrefund, hroom, hdepth, hcallers, hc, hp, hstack, hg, hstore,
      hwords, hctx, hdata, ht, hwarm, hslots, hstatic, hstate, hlogs⟩
    have hcredit : credit = inc := by
      rcases hrefund with ⟨_, eq⟩ | ⟨bad, _⟩
      · exact eq
      · contradiction
    subst credit
    rcases he with ⟨saved, tail, hz, hs, hic, hip, histack, himem, hictx, hidata, histatic,
      hiparent, hiwrites, hireads, historage, hicreated, hisnap, hilogs, hiwarm, hislots, himeters⟩
    simp only [↓reduceIte] at himeters
    exact ⟨inc, saved, tail, hz, hs, hic, hip, histack, himem, hictx, hidata, histatic, hiparent,
      hiwrites, hireads, historage, hicreated, hisnap, hilogs, hiwarm, hislots, hroom, hdepth,
      hcallers, hc, hp, hstack, hg, hstore, hwords, hctx, hdata, ht, hwarm, hslots, hstatic, hstate, hlogs, himeters⟩

-- These equations expose the failed-child incorporation and both refund cases.
def FailedCreditFields (charged : Bool) (before after : Frame.State) : Prop :=
  (charged = false ∧ after = before) ∨
  (charged = true ∧ after.code = before.code ∧ after.pc = before.pc ∧ after.stack = before.stack ∧
    after.memory = before.memory ∧ after.context = before.context ∧ after.returnData = before.returnData ∧
    after.tracker = before.tracker ∧ after.warmAddresses = before.warmAddresses ∧
    after.warmSlots = before.warmSlots ∧ after.isStatic = before.isStatic ∧ after.logs = before.logs ∧
    after.stateGas.baseline = before.stateGas.baseline ∧
    after.stateGas.refundCounter = before.stateGas.refundCounter ∧
    after.stateGas.committedSpill = before.stateGas.committedSpill ∧
    ((183600 ≤ before.stateGas.spilled ∧ after.gas = before.gas + 183600 ∧
      after.stateGas.spilled + 183600 = before.stateGas.spilled ∧
      after.stateGas.reservoir = before.stateGas.reservoir) ∨
     (before.stateGas.spilled < 183600 ∧ after.gas = before.gas + before.stateGas.spilled ∧
      after.stateGas.spilled = 0 ∧ after.stateGas.reservoir = before.stateGas.reservoir + (183600 - before.stateGas.spilled))))

theorem failed_credit_fields (charged : Bool) (before after : Frame.State)
    (h : NestedRunner.RefundSpec false charged before after) : FailedCreditFields charged before after := by
  cases charged <;> simpa [NestedRunner.RefundSpec, NestedRunner.CreditFields,
    Gas.StateMeter.CreditEffect, Gas.StateMeter.Retained, Frame.stateMeter, FailedCreditFields, and_assoc] using h

def FailedSettlementFields (parent child incorporated : Frame.State) : Prop :=
  ∃ saved tail, child.stateGas.committedSpill = 0 ∧ child.tracker.snapshots = saved :: tail ∧
    incorporated.code = parent.code ∧ incorporated.pc = parent.pc ∧ incorporated.stack = parent.stack ∧
    incorporated.memory = parent.memory ∧ incorporated.context = parent.context ∧
    incorporated.returnData = ByteArray.empty ∧ incorporated.isStatic = parent.isStatic ∧
    incorporated.tracker.parent = child.tracker.parent ∧ incorporated.tracker.writes = saved ∧
    incorporated.tracker.accountReads = child.tracker.accountReads ∧
    incorporated.tracker.storageReads = child.tracker.storageReads ∧
    incorporated.tracker.createdAccounts = child.tracker.createdAccounts ∧ incorporated.tracker.snapshots = tail ∧
    incorporated.logs = parent.logs ∧ incorporated.warmAddresses = parent.warmAddresses ∧
    incorporated.warmSlots = parent.warmSlots ∧ incorporated.gas = parent.gas ∧
    incorporated.stateGas.reservoir = parent.stateGas.reservoir + child.stateGas.baseline ∧
    incorporated.stateGas.baseline = parent.stateGas.baseline ∧
    incorporated.stateGas.refundCounter = parent.stateGas.refundCounter ∧
    incorporated.stateGas.spilled = parent.stateGas.spilled ∧
    incorporated.stateGas.committedSpill = parent.stateGas.committedSpill

theorem failed_settlement_fields (parent child incorporated : Frame.State)
    (h : ChildSettlement.Effect parent child incorporated false 0 ByteArray.empty) :
    FailedSettlementFields parent child incorporated := by
  simpa [ChildSettlement.Effect, FailedSettlementFields] using h

-- Every field and both credit branches follow from an observed out-of-gas continuation.
theorem ripemd_failed_next_complete (c : NestedRunner.Continuation) (child : Frame.State)
    (rest : List NestedRunner.Continuation) (out : NestedRunner.Machine)
    (hgas : child.gas < 600 + 120 * ((child.context.data.size + 31) / 32))
    (h : NestedRunner.ripemdCall c child rest = .next out) :
    ∃ incorporated credited : Frame.State,
      FailedSettlementFields c.parent child incorporated ∧ FailedCreditFields c.newAccountCharged incorporated credited ∧
      credited.stack.val.length < 1024 ∧ out.depth = c.depth ∧ out.callers = rest ∧
      out.frame.code = credited.code ∧ out.frame.pc = credited.pc + 1 ∧
      out.frame.stack.val = 0 :: credited.stack.val ∧ out.frame.gas = credited.gas ∧
      out.frame.memory.store = credited.memory.store ∧
      out.frame.memory.words = max credited.memory.words (Memory.Allocation.requiredWords c.request.outputOffset.toNat 0) ∧
      out.frame.context = credited.context ∧ out.frame.returnData = credited.returnData ∧
      out.frame.tracker = credited.tracker ∧ out.frame.warmAddresses = credited.warmAddresses ∧
      out.frame.warmSlots = credited.warmSlots ∧ out.frame.isStatic = credited.isStatic ∧
      out.frame.stateGas = credited.stateGas ∧ out.frame.logs = credited.logs := by
  rcases ripemd_observed c child rest (.next out) h with ⟨_, hr⟩ | ⟨ha, _⟩
  · change NestedRunner.ResumeSuccess c child false 0 ByteArray.empty rest out at hr
    rcases hr with ⟨inc, credit, he, hc, hroom, hdepth, hcallers, hcode, hpc, hstack, hgas', hstore,
      hwords, hctx, hdata, ht, hwarm, hslots, hstatic, hstate, hlogs⟩
    refine ⟨inc, credit, failed_settlement_fields _ _ _ he, failed_credit_fields _ _ _ hc,
      hroom, hdepth, hcallers, hcode, hpc, hstack, hgas', ?_, ?_, hctx, hdata, ht, hwarm,
      hslots, hstatic, hstate, hlogs⟩
    · simpa only [ByteArray.data_empty, Array.toList_empty, List.take_nil, List.length_nil,
        List.zip_nil_right, List.nil_append] using hstore
    · simpa only [ByteArray.data_empty, Array.toList_empty, List.take_nil, List.length_nil] using hwords
  · omega

-- The diagnostic exposes checkpoint priority or all fields of the full-stack path.
theorem ripemd_failed_diagnostic_complete (c : NestedRunner.Continuation) (child diagnostic : Frame.State)
    (rest : List NestedRunner.Continuation)
    (hgas : child.gas < 600 + 120 * ((child.context.data.size + 31) / 32))
    (h : NestedRunner.ripemdCall c child rest = .done (.tooling diagnostic .invalidContinuation)) :
    (diagnostic = child ∧ child.stateGas.committedSpill ≠ 0) ∨
    (diagnostic = child ∧ child.stateGas.committedSpill = 0 ∧ child.tracker.snapshots = []) ∨
    ∃ incorporated : Frame.State,
      FailedSettlementFields c.parent child incorporated ∧
      FailedCreditFields c.newAccountCharged incorporated diagnostic ∧ diagnostic.stack.val.length = 1024 := by
  rcases ripemd_observed c child rest (.done (.tooling diagnostic .invalidContinuation)) h with ⟨_, hr⟩ | ⟨ha, _⟩
  · change NestedRunner.ResumeFailure c child false 0 ByteArray.empty diagnostic at hr
    rcases hr with ⟨hdiag, hspill | ⟨hspill, hsnap⟩⟩ | ⟨inc, credit, he, hc, hfull, hdiag⟩
    · exact Or.inl ⟨hdiag, hspill⟩
    · exact Or.inr (Or.inl ⟨hdiag, hspill, hsnap⟩)
    · subst diagnostic
      exact Or.inr (Or.inr ⟨inc, failed_settlement_fields _ _ _ he, failed_credit_fields _ _ _ hc, hfull⟩)
  · omega

-- Out-of-gas output copies no bytes, so every parent memory observation is retained.
theorem ripemd_failed_next_bytes (c : NestedRunner.Continuation) (child : Frame.State)
    (rest : List NestedRunner.Continuation) (out : NestedRunner.Machine)
    (hgas : child.gas < 600 + 120 * ((child.context.data.size + 31) / 32))
    (h : NestedRunner.ripemdCall c child rest = .next out) :
    ∀ offset, Memory.readByte out.frame.memory.store offset = Memory.readByte c.parent.memory.store offset := by
  obtain ⟨inc, credit, hs, hc, _, _, _, _, _, _, _, hm, _⟩ := ripemd_failed_next_complete c child rest out hgas h
  rcases hs with ⟨_, _, _, _, _, _, _, himem, _⟩
  have hcredit : credit.memory = inc.memory := by
    rcases hc with ⟨_, heq⟩ | ⟨_, _, _, _, hmem, _⟩
    · cases heq; rfl
    · exact hmem
  intro offset
  rw [hm, hcredit, himem]
