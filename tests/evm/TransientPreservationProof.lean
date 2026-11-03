import EthLib.EVM.Proofs.Runner.SelfBalance

open EthLib.EVM

namespace TransientPreservationConsumer

private theorem notSstoreOfTstore {s : Frame.State} (at_ : Frame.At s (some .tstore)) :
    ¬ Frame.At s (some .sstore) := by
  obtain ⟨bounds, decoded⟩ := at_
  rintro ⟨_, other⟩
  have : Opcode.tstore = Opcode.sstore := Option.some.inj (decoded.symm.trans other)
  cases this

theorem account_rule (s : Frame.State) (out : Frame.Outcome)
    (notStore : ¬ Frame.At s (some .sstore)) (rule : Frame.Rule s out) :
    out.frame.tracker.writes.accountWrites = s.tracker.writes.accountWrites :=
  (Frame.outcome_persistent_writes_unchanged_of_not_sstore notStore rule).1

theorem storage_rule (s : Frame.State) (out : Frame.Outcome)
    (notStore : ¬ Frame.At s (some .sstore)) (rule : Frame.Rule s out) :
    out.frame.tracker.writes.storageWrites = s.tracker.writes.storageWrites :=
  (Frame.outcome_persistent_writes_unchanged_of_not_sstore notStore rule).2.1

theorem code_rule (s : Frame.State) (out : Frame.Outcome)
    (notStore : ¬ Frame.At s (some .sstore)) (rule : Frame.Rule s out) :
    out.frame.tracker.writes.codeWrites = s.tracker.writes.codeWrites :=
  (Frame.outcome_persistent_writes_unchanged_of_not_sstore notStore rule).2.2.1

theorem clears_rule (s : Frame.State) (out : Frame.Outcome)
    (notStore : ¬ Frame.At s (some .sstore)) (rule : Frame.Rule s out) :
    out.frame.tracker.writes.storageClears = s.tracker.writes.storageClears :=
  (Frame.outcome_persistent_writes_unchanged_of_not_sstore notStore rule).2.2.2

theorem actual_step (s : Frame.State) (notStore : ¬ Frame.At s (some .sstore)) :
    (Frame.step s).frame.tracker.writes.accountWrites = s.tracker.writes.accountWrites ∧
    (Frame.step s).frame.tracker.writes.storageWrites = s.tracker.writes.storageWrites ∧
    (Frame.step s).frame.tracker.writes.codeWrites = s.tracker.writes.codeWrites ∧
    (Frame.step s).frame.tracker.writes.storageClears = s.tracker.writes.storageClears :=
  Frame.step_persistent_writes_unchanged_of_not_sstore s notStore

theorem exhausted (fuel : Nat) (s t : Frame.State) (trace : Runner.NoSstoreRun fuel s)
    (run : Runner.run fuel s = .exhausted t) :
    t.tracker.writes.accountWrites = s.tracker.writes.accountWrites ∧
    t.tracker.writes.storageWrites = s.tracker.writes.storageWrites ∧
    t.tracker.writes.codeWrites = s.tracker.writes.codeWrites ∧
    t.tracker.writes.storageClears = s.tracker.writes.storageClears := by
  have h := Runner.SelfBalanceProgram.run_persistent_writes_unchanged_of_no_sstore fuel s trace
  simpa [run, Runner.Result.frame] using h

theorem stopped (fuel : Nat) (s t : Frame.State) (trace : Runner.NoSstoreRun fuel s)
    (run : Runner.run fuel s = .stopped t) :
    t.tracker.writes.accountWrites = s.tracker.writes.accountWrites ∧
    t.tracker.writes.storageWrites = s.tracker.writes.storageWrites ∧
    t.tracker.writes.codeWrites = s.tracker.writes.codeWrites ∧
    t.tracker.writes.storageClears = s.tracker.writes.storageClears := by
  have h := Runner.SelfBalanceProgram.run_persistent_writes_unchanged_of_no_sstore fuel s trace
  simpa [run, Runner.Result.frame] using h

theorem exception (fuel : Nat) (s t : Frame.State) (reason : Frame.Exception)
    (trace : Runner.NoSstoreRun fuel s) (run : Runner.run fuel s = .exception t reason) :
    t.tracker.writes.accountWrites = s.tracker.writes.accountWrites ∧
    t.tracker.writes.storageWrites = s.tracker.writes.storageWrites ∧
    t.tracker.writes.codeWrites = s.tracker.writes.codeWrites ∧
    t.tracker.writes.storageClears = s.tracker.writes.storageClears := by
  have h := Runner.SelfBalanceProgram.run_persistent_writes_unchanged_of_no_sstore fuel s trace
  simpa [run, Runner.Result.frame] using h

theorem unsupported (fuel : Nat) (s t : Frame.State) (op : Opcode)
    (trace : Runner.NoSstoreRun fuel s) (run : Runner.run fuel s = .unsupported t op) :
    t.tracker.writes.accountWrites = s.tracker.writes.accountWrites ∧
    t.tracker.writes.storageWrites = s.tracker.writes.storageWrites ∧
    t.tracker.writes.codeWrites = s.tracker.writes.codeWrites ∧
    t.tracker.writes.storageClears = s.tracker.writes.storageClears := by
  have h := Runner.SelfBalanceProgram.run_persistent_writes_unchanged_of_no_sstore fuel s trace
  simpa [run, Runner.Result.frame] using h

theorem no_revert (fuel : Nat) (s t : Frame.State) (gas : Nat) (data : ByteArray)
    (run : Runner.run fuel s = .reverted t gas data) : False :=
  Runner.run_not_reverted fuel s t gas data run

-- A decoded TSTORE can be the actual first step of a trace satisfying the restriction.
theorem tstore_trace (s t : Frame.State) (at_ : Frame.At s (some .tstore))
    (step : Frame.step s = .continue t) :
    Runner.NoSstoreRun 1 s ∧ Runner.run 1 s = .exhausted t ∧
    t.tracker.writes.accountWrites = s.tracker.writes.accountWrites ∧
    t.tracker.writes.storageWrites = s.tracker.writes.storageWrites ∧
    t.tracker.writes.codeWrites = s.tracker.writes.codeWrites ∧
    t.tracker.writes.storageClears = s.tracker.writes.storageClears := by
  have trace : Runner.NoSstoreRun 1 s := by
    simp [Runner.NoSstoreRun, step, notSstoreOfTstore at_]
  have result : Runner.run 1 s = .exhausted t := by simp [Runner.run, step]
  exact ⟨trace, result, exhausted 1 s t trace result⟩

end TransientPreservationConsumer
