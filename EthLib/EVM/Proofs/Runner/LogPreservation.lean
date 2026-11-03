module

public import EthLib.EVM.Proofs.Runner
public import EthLib.EVM.Proofs.Frame.LogPreservation

@[expose] public section
namespace EthLib.EVM.Runner

/-- The executed bounded trace contains no LOG instruction. -/
def NoLogRun : Nat → Frame.State → Prop
  | 0, _ => True
  | fuel + 1, s => Frame.NoLogStep s ∧
      match Frame.step s with
      | .continue t => NoLogRun fuel t
      | _ => True

/-- Every result of a bounded trace without LOG retains its initial logs. -/
theorem run_logs_unchanged_of_noLog (fuel : Nat) (s : Frame.State)
    (trace : NoLogRun fuel s) : (run fuel s).frame.logs = s.logs := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    have preserved := Frame.step_logs_unchanged_of_noLog s trace.1
    cases h : Frame.step s with
    | «continue» t =>
      simp only [run, h]
      have tail : NoLogRun fuel t := by simpa [NoLogRun, h] using trace.2
      exact (ih t tail).trans (by simpa [h, Frame.Outcome.frame] using preserved)
    | stop t => simpa [run, h, Frame.Outcome.frame, Result.frame] using preserved
    | returned input output => simpa [run, h, Frame.Outcome.frame, Result.frame] using preserved
    | revert input gas output => simpa [run, h, Frame.Outcome.frame, Result.frame] using preserved
    | exception input error => simpa [run, h, Frame.Outcome.frame, Result.frame] using preserved
    | unsupported input op => simpa [run, h, Frame.Outcome.frame, Result.frame] using preserved

/-- Every bounded result retains the initial logs as a prefix. -/
theorem run_logs_prefix (fuel : Nat) (s : Frame.State) :
    ∃ suffix, (run fuel s).frame.logs = s.logs ++ suffix := by
  induction fuel generalizing s with
  | zero => exact ⟨[], by simp [run, Result.frame]⟩
  | succ fuel ih =>
    have retained :=  Frame.outcome_logs_prefix ((Frame.step_iff_rule s _).mp rfl)
    cases h : Frame.step s with
    | «continue» t =>
      obtain ⟨a, ha⟩ := retained
      have ha' : t.logs = s.logs ++ a := by simpa [h, Frame.Outcome.frame] using ha
      obtain ⟨b, hb⟩ := ih t
      refine ⟨a ++ b, ?_⟩
      simpa [run, h, ha', List.append_assoc] using hb
    | stop t => simpa [run, h, Frame.Outcome.frame, Result.frame] using retained
    | returned input output => simpa [run, h, Frame.Outcome.frame, Result.frame] using retained
    | revert input gas output => simpa [run, h, Frame.Outcome.frame, Result.frame] using retained
    | exception input error => simpa [run, h, Frame.Outcome.frame, Result.frame] using retained
    | unsupported input op => simpa [run, h, Frame.Outcome.frame, Result.frame] using retained

end EthLib.EVM.Runner
