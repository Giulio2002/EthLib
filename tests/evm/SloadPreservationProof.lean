import EthLib.EVM.Proofs.Runner.SelfBalance
import EthLib.EVM.Proofs.Runner.Sload

open EthLib.EVM

namespace StorageReadPreservationConsumer

private theorem notAtOfAt {s : Frame.State} {op target : Opcode}
    (at_ : Frame.At s (some op)) (different : op ≠ target) :
    ¬ Frame.At s (some target) := by
  obtain ⟨bounds, decoded⟩ := at_
  rintro ⟨_, other⟩
  have equal : op = target := Option.some.inj (decoded.symm.trans other)
  exact different equal

-- Both account-reading opcodes remain within the preservation scope.
theorem balance_step (s : Frame.State) (at_ : Frame.At s (some .balance)) :
    (Frame.step s).frame.tracker.storageReads = s.tracker.storageReads :=
  Frame.step_storageReads_unchanged_of_not_sload s (notAtOfAt at_ (by decide)) (notAtOfAt at_ (by decide))

theorem selfbalance_step (s : Frame.State) (at_ : Frame.At s (some .selfbalance)) :
    (Frame.step s).frame.tracker.storageReads = s.tracker.storageReads :=
  Frame.step_storageReads_unchanged_of_not_sload s (notAtOfAt at_ (by decide)) (notAtOfAt at_ (by decide))

-- The predicate accepts an actual BALANCE, SELFBALANCE, STOP trace.
theorem mixed_trace (s t u v : Frame.State)
    (balanceAt : Frame.At s (some .balance)) (balanceStep : Frame.step s = .continue t)
    (selfAt : Frame.At t (some .selfbalance)) (selfStep : Frame.step t = .continue u)
    (stopAt : Frame.At u (some .stop)) (stopStep : Frame.step u = .stop v) :
    (Runner.run 3 s).frame.tracker.storageReads = s.tracker.storageReads := by
  have trace : Runner.NoSloadRun 3 s := by
    simp only [Runner.NoSloadRun, balanceStep, selfStep, stopStep]
    exact ⟨notAtOfAt balanceAt (by decide), notAtOfAt selfAt (by decide),
      notAtOfAt stopAt (by decide), trivial⟩
  have noStore : Runner.NoSstoreRun 3 s := by
    simp only [Runner.NoSstoreRun, balanceStep, selfStep, stopStep]
    exact ⟨notAtOfAt balanceAt (by decide), notAtOfAt selfAt (by decide),
      notAtOfAt stopAt (by decide), trivial⟩
  exact Runner.run_storageReads_unchanged_of_no_sload 3 s trace noStore

theorem exhausted_result (fuel : Nat) (s t : Frame.State) (trace : Runner.NoSloadRun fuel s) (noStore : Runner.NoSstoreRun fuel s)
    (run : Runner.run fuel s = .exhausted t) : t.tracker.storageReads = s.tracker.storageReads := by
  have result := Runner.run_storageReads_unchanged_of_no_sload fuel s trace noStore
  simpa [run, Runner.Result.frame] using result

theorem stopped_result (fuel : Nat) (s t : Frame.State) (trace : Runner.NoSloadRun fuel s) (noStore : Runner.NoSstoreRun fuel s)
    (run : Runner.run fuel s = .stopped t) : t.tracker.storageReads = s.tracker.storageReads := by
  have result := Runner.run_storageReads_unchanged_of_no_sload fuel s trace noStore
  simpa [run, Runner.Result.frame] using result

theorem exception_result (fuel : Nat) (s t : Frame.State) (reason : Frame.Exception) (trace : Runner.NoSloadRun fuel s) (noStore : Runner.NoSstoreRun fuel s)
    (run : Runner.run fuel s = .exception t reason) : t.tracker.storageReads = s.tracker.storageReads := by
  have result := Runner.run_storageReads_unchanged_of_no_sload fuel s trace noStore
  simpa [run, Runner.Result.frame] using result

theorem unsupported_result (fuel : Nat) (s t : Frame.State) (op : Opcode) (trace : Runner.NoSloadRun fuel s) (noStore : Runner.NoSstoreRun fuel s)
    (run : Runner.run fuel s = .unsupported t op) : t.tracker.storageReads = s.tracker.storageReads := by
  have result := Runner.run_storageReads_unchanged_of_no_sload fuel s trace noStore
  simpa [run, Runner.Result.frame] using result



-- These applications use opcode exclusions, not an assumed output equality.
theorem writes_step (s : Frame.State) (out : Frame.Outcome)
    (notSstore : ¬ Frame.At s (some .sstore)) (notTstore : ¬ Frame.At s (some .tstore)) (rule : Frame.Rule s out) :
    out.frame.tracker.writes = s.tracker.writes :=
  (Frame.outcome_tracker_retained notSstore notTstore rule).2.1

theorem warm_slots_step (s : Frame.State) (out : Frame.Outcome)
    (notSload : ¬ Frame.At s (some .sload)) (notSstore : ¬ Frame.At s (some .sstore))
    (rule : Frame.Rule s out) : out.frame.warmSlots = s.warmSlots :=
  Frame.outcome_slots_unchanged_of_not_sload notSload notSstore rule

theorem warm_slots_actual_step (s : Frame.State)
    (notSload : ¬ Frame.At s (some .sload)) (notSstore : ¬ Frame.At s (some .sstore)) :
    (Frame.step s).frame.warmSlots = s.warmSlots :=
  Frame.outcome_slots_unchanged_of_not_sload notSload notSstore ((Frame.step_iff_rule s _).mp rfl)

theorem state_gas_actual_step (s : Frame.State) (notSstore : ¬ Frame.At s (some .sstore)) :
    (Frame.step s).frame.stateGas = s.stateGas :=
  Frame.outcome_stateGas_unchanged_of_not_sstore notSstore ((Frame.step_iff_rule s _).mp rfl)

theorem tracker_actual_step (s : Frame.State) (notSelf : ¬ Frame.At s (some .selfbalance))
    (notBalance : ¬ Frame.At s (some .balance)) (notSload : ¬ Frame.At s (some .sload))
    (notSstore : ¬ Frame.At s (some .sstore)) (notTstore : ¬ Frame.At s (some .tstore)) (notSize : ¬ Frame.At s (some .extcodesize)) (notHash : ¬ Frame.At s (some .extcodehash)) : (Frame.step s).frame.tracker = s.tracker :=
  Frame.outcome_tracker_unchanged_of_not_selfBalance notSelf notBalance notSload notSstore notTstore notSize notHash
    ((Frame.step_iff_rule s _).mp rfl)

theorem account_read_balance (s : Frame.State) (at_ : Frame.At s (some .balance)) :
    (Frame.step s).frame.tracker = s.tracker ∨
    (∃ a, (Frame.step s).frame.tracker = Frame.BalanceRead s a) ∨
    ∃ key, (Frame.step s).frame.tracker = Frame.SloadRead s key :=
  Frame.outcome_tracker_read (notAtOfAt at_ (by decide)) (notAtOfAt at_ (by decide)) ((Frame.step_iff_rule s _).mp rfl)

theorem account_read_selfbalance (s : Frame.State) (at_ : Frame.At s (some .selfbalance)) :
    (Frame.step s).frame.tracker = s.tracker ∨
    (∃ a, (Frame.step s).frame.tracker = Frame.BalanceRead s a) ∨
    ∃ key, (Frame.step s).frame.tracker = Frame.SloadRead s key :=
  Frame.outcome_tracker_read (notAtOfAt at_ (by decide)) (notAtOfAt at_ (by decide)) ((Frame.step_iff_rule s _).mp rfl)

theorem writes_exhausted (fuel : Nat) (s t : Frame.State) (trace : Runner.NoSstoreRun fuel s) (noTransient : Runner.NoTstoreRun fuel s)
    (run : Runner.run fuel s = .exhausted t) : t.tracker.writes = s.tracker.writes := by
  have result := (Runner.SelfBalanceProgram.run_tracker_retained fuel s trace noTransient).2.1
  simpa [run, Runner.Result.frame] using result

theorem writes_stopped (fuel : Nat) (s t : Frame.State) (trace : Runner.NoSstoreRun fuel s) (noTransient : Runner.NoTstoreRun fuel s)
    (run : Runner.run fuel s = .stopped t) : t.tracker.writes = s.tracker.writes := by
  have result := (Runner.SelfBalanceProgram.run_tracker_retained fuel s trace noTransient).2.1
  simpa [run, Runner.Result.frame] using result

theorem writes_exception (fuel : Nat) (s t : Frame.State) (reason : Frame.Exception)
    (trace : Runner.NoSstoreRun fuel s) (noTransient : Runner.NoTstoreRun fuel s) (run : Runner.run fuel s = .exception t reason) :
    t.tracker.writes = s.tracker.writes := by
  have result := (Runner.SelfBalanceProgram.run_tracker_retained fuel s trace noTransient).2.1
  simpa [run, Runner.Result.frame] using result

theorem writes_unsupported (fuel : Nat) (s t : Frame.State) (op : Opcode)
    (trace : Runner.NoSstoreRun fuel s) (noTransient : Runner.NoTstoreRun fuel s) (run : Runner.run fuel s = .unsupported t op) :
    t.tracker.writes = s.tracker.writes := by
  have result := (Runner.SelfBalanceProgram.run_tracker_retained fuel s trace noTransient).2.1
  simpa [run, Runner.Result.frame] using result

theorem static_retained (fuel : Nat) (s : Frame.State) :
    (Runner.run fuel s).frame.isStatic = s.isStatic :=
  Runner.SelfBalanceProgram.run_static_retained fuel s

theorem state_gas_retained (fuel : Nat) (s : Frame.State) (trace : Runner.NoSstoreRun fuel s) :
    (Runner.run fuel s).frame.stateGas = s.stateGas :=
  Runner.SelfBalanceProgram.run_stateGas_unchanged_of_no_sstore fuel s trace


-- The paired guarantees apply to each actual bounded result constructor.
theorem fields_exhausted (fuel : Nat) (s t : Frame.State) (trace : Runner.NoSstoreRun fuel s)
    (run : Runner.run fuel s = .exhausted t) : t.isStatic = s.isStatic ∧ t.stateGas = s.stateGas := by
  exact ⟨by simpa [run, Runner.Result.frame] using Runner.SelfBalanceProgram.run_static_retained fuel s,
    by simpa [run, Runner.Result.frame] using Runner.SelfBalanceProgram.run_stateGas_unchanged_of_no_sstore fuel s trace⟩

theorem fields_stopped (fuel : Nat) (s t : Frame.State) (trace : Runner.NoSstoreRun fuel s)
    (run : Runner.run fuel s = .stopped t) : t.isStatic = s.isStatic ∧ t.stateGas = s.stateGas := by
  exact ⟨by simpa [run, Runner.Result.frame] using Runner.SelfBalanceProgram.run_static_retained fuel s,
    by simpa [run, Runner.Result.frame] using Runner.SelfBalanceProgram.run_stateGas_unchanged_of_no_sstore fuel s trace⟩

theorem fields_exception (fuel : Nat) (s t : Frame.State) (reason : Frame.Exception)
    (trace : Runner.NoSstoreRun fuel s) (run : Runner.run fuel s = .exception t reason) :
    t.isStatic = s.isStatic ∧ t.stateGas = s.stateGas := by
  exact ⟨by simpa [run, Runner.Result.frame] using Runner.SelfBalanceProgram.run_static_retained fuel s,
    by simpa [run, Runner.Result.frame] using Runner.SelfBalanceProgram.run_stateGas_unchanged_of_no_sstore fuel s trace⟩

theorem fields_unsupported (fuel : Nat) (s t : Frame.State) (op : Opcode)
    (trace : Runner.NoSstoreRun fuel s) (run : Runner.run fuel s = .unsupported t op) :
    t.isStatic = s.isStatic ∧ t.stateGas = s.stateGas := by
  exact ⟨by simpa [run, Runner.Result.frame] using Runner.SelfBalanceProgram.run_static_retained fuel s,
    by simpa [run, Runner.Result.frame] using Runner.SelfBalanceProgram.run_stateGas_unchanged_of_no_sstore fuel s trace⟩

theorem warm_slots_run (fuel : Nat) (s : Frame.State) (slot : World.Address × Word)
    (warm : slot ∈ s.warmSlots) : slot ∈ (Runner.run fuel s).frame.warmSlots :=
  Runner.SloadProgram.run_slots_monotone fuel s slot warm

theorem warm_exhausted (fuel : Nat) (s t : Frame.State) (slot : World.Address × Word)
    (warm : slot ∈ s.warmSlots) (run : Runner.run fuel s = .exhausted t) : slot ∈ t.warmSlots := by
  simpa [run, Runner.Result.frame] using Runner.SloadProgram.run_slots_monotone fuel s slot warm

theorem warm_stopped (fuel : Nat) (s t : Frame.State) (slot : World.Address × Word)
    (warm : slot ∈ s.warmSlots) (run : Runner.run fuel s = .stopped t) : slot ∈ t.warmSlots := by
  simpa [run, Runner.Result.frame] using Runner.SloadProgram.run_slots_monotone fuel s slot warm

theorem warm_exception (fuel : Nat) (s t : Frame.State) (slot : World.Address × Word)
    (warm : slot ∈ s.warmSlots) (reason : Frame.Exception)
    (run : Runner.run fuel s = .exception t reason) : slot ∈ t.warmSlots := by
  simpa [run, Runner.Result.frame] using Runner.SloadProgram.run_slots_monotone fuel s slot warm

theorem warm_unsupported (fuel : Nat) (s t : Frame.State) (slot : World.Address × Word)
    (warm : slot ∈ s.warmSlots) (op : Opcode)
    (run : Runner.run fuel s = .unsupported t op) : slot ∈ t.warmSlots := by
  simpa [run, Runner.Result.frame] using Runner.SloadProgram.run_slots_monotone fuel s slot warm

theorem metadata_retained (fuel : Nat) (s : Frame.State) :
    (Runner.run fuel s).frame.tracker.parent = s.tracker.parent ∧
    (Runner.run fuel s).frame.tracker.createdAccounts = s.tracker.createdAccounts ∧
    (Runner.run fuel s).frame.tracker.snapshots = s.tracker.snapshots :=
  Runner.SelfBalanceProgram.run_tracker_metadata_retained fuel s

theorem unreachable_revert (fuel : Nat) (s t : Frame.State) (gas : Nat) (output : ByteArray) :
    Runner.run fuel s ≠ .reverted t gas output := Runner.run_not_reverted fuel s t gas output

#print axioms balance_step
#print axioms selfbalance_step
#print axioms mixed_trace
#print axioms exhausted_result
#print axioms stopped_result
#print axioms exception_result
#print axioms unsupported_result
#print axioms writes_step
#print axioms warm_slots_step
#print axioms warm_slots_actual_step
#print axioms state_gas_actual_step
#print axioms tracker_actual_step
#print axioms account_read_balance
#print axioms account_read_selfbalance
#print axioms writes_exhausted
#print axioms writes_stopped
#print axioms writes_exception
#print axioms writes_unsupported
#print axioms static_retained
#print axioms state_gas_retained
#print axioms fields_exhausted
#print axioms fields_stopped
#print axioms fields_exception
#print axioms fields_unsupported
#print axioms warm_slots_run
#print axioms warm_exhausted
#print axioms warm_stopped
#print axioms warm_exception
#print axioms warm_unsupported
#print axioms metadata_retained
#print axioms unreachable_revert

end StorageReadPreservationConsumer
