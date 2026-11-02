module

public import EthLib.EVM.Runner
public import EthLib.EVM.Proofs.Frame

/-!
# Bounded runner traces

Terminal traces use the independent frame rules as edges.
The separate stopping trace uses executable steps.
-/

@[expose] public section
namespace EthLib.EVM.Runner

/-- A finite trace of continuing frame steps followed by a stop. -/
inductive Stops : Frame.State → Nat → Frame.State → Prop where
  | stop {s t} : Frame.step s = .stop t → Stops s 1 t
  | next {s t u n} : Frame.step s = .continue t → Stops t n u → Stops s (n + 1) u

/-- Enough fuel executes every finite stopping trace. -/
theorem run_of_stops {s t : Frame.State} {n : Nat} (h : Stops s n t) :
    ∀ extra, run (n + extra) s = .stopped t := by
  induction h with
  | stop hs =>
    intro extra
    simp [Nat.one_add, run, hs]
  | next hs _ ih =>
    intro extra
    have := ih extra
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, run, hs] using this

/-- A stopped runner has a finite stopping trace within its fuel. -/
theorem stops_of_run {fuel : Nat} {s t : Frame.State}
    (h : run fuel s = .stopped t) : ∃ n, n ≤ fuel ∧ Stops s n t := by
  induction fuel generalizing s with
  | zero => simp [run] at h
  | succ fuel ih =>
    cases hs : Frame.step s with
    | «continue» next =>
      simp [run, hs] at h
      obtain ⟨n, hn, ht⟩ := ih h
      exact ⟨n + 1, by omega, .next hs ht⟩
    | stop next =>
      simp [run, hs] at h
      subst next
      exact ⟨1, by omega, .stop hs⟩
    | exception input reason => simp [run, hs] at h
    | unsupported input op => simp [run, hs] at h

/-- A finite trace ending in any terminal EVM or tooling result. -/
inductive Terminates : Frame.State → Nat → Result → Prop where
  | stop {s t} : Frame.Rule s (.stop t) → Terminates s 1 (.stopped t)
  | exception {s input e} : Frame.Rule s (.exception input e) →
      Terminates s 1 (.exception input e)
  | unsupported {s input op} : Frame.Rule s (.unsupported input op) →
      Terminates s 1 (.unsupported input op)
  | next {s t n result} : Frame.Rule s (.continue t) → Terminates t n result →
      Terminates s (n + 1) result

/-- A terminal trace runs with any fuel at least its length. -/
theorem run_of_terminates {s : Frame.State} {n : Nat} {result : Result}
    (h : Terminates s n result) : ∀ extra, run (n + extra) s = result := by
  induction h with
  | stop hs => intro extra; simp [Nat.one_add, run, Frame.rule_sound hs]
  | exception hs => intro extra; simp [Nat.one_add, run, Frame.rule_sound hs]
  | unsupported hs => intro extra; simp [Nat.one_add, run, Frame.rule_sound hs]
  | next hs _ ih =>
    intro extra
    have := ih extra
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, run, Frame.rule_sound hs] using this

/-- Every non-exhausted run has a terminal trace no longer than its fuel. -/
theorem terminates_of_run {fuel : Nat} {s : Frame.State} {result : Result}
    (h : run fuel s = result) (notExhausted : ∀ t, result ≠ .exhausted t) :
    ∃ n, n ≤ fuel ∧ Terminates s n result := by
  induction fuel generalizing s with
  | zero => exact False.elim (notExhausted s h.symm)
  | succ fuel ih =>
    cases hs : Frame.step s with
    | «continue» next =>
      simp [run, hs] at h
      obtain ⟨n, hn, ht⟩ := ih h
      exact ⟨n + 1, by omega,  .next ((Frame.step_iff_rule _ _).mp hs) ht⟩
    | stop next =>
      simp [run, hs] at h
      subst result
      exact ⟨1, by omega,  .stop ((Frame.step_iff_rule _ _).mp hs)⟩
    | exception input e =>
      simp [run, hs] at h
      subst result
      exact ⟨1, by omega,  .exception ((Frame.step_iff_rule _ _).mp hs)⟩
    | unsupported input op =>
      simp [run, hs] at h
      subst result
      exact ⟨1, by omega,  .unsupported ((Frame.step_iff_rule _ _).mp hs)⟩

/-- All bounded runs preserve code and allocated memory. -/
theorem run_unchanged (fuel : Nat) (s : Frame.State) :
    (run fuel s).frame.code = s.code ∧ (run fuel s).frame.memory = s.memory := by
  induction fuel generalizing s with
  | zero => simp [run, Result.frame]
  | succ fuel ih =>
    cases hs : Frame.step s with
    | «continue» next =>
      have same := Frame.outcome_unchanged ((Frame.step_iff_rule _ _).mp hs)
      have rest := ih next
      simp only [Frame.Outcome.frame] at same
      simpa [run, hs, same.1, same.2] using rest
    | stop next =>
      have same := Frame.outcome_unchanged ((Frame.step_iff_rule _ _).mp hs)
      simpa [run, hs, Result.frame, Frame.Outcome.frame] using same
    | exception input e =>
      have same := Frame.outcome_unchanged ((Frame.step_iff_rule _ _).mp hs)
      simpa [run, hs, Result.frame, Frame.Outcome.frame] using same
    | unsupported input op =>
      have same := Frame.outcome_unchanged ((Frame.step_iff_rule _ _).mp hs)
      simpa [run, hs, Result.frame, Frame.Outcome.frame] using same

end EthLib.EVM.Runner
