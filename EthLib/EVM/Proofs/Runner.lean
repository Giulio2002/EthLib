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
    | revert input gas output => exact False.elim (Frame.step_not_revert s input gas output hs)
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
    | revert input gas output => exact False.elim (Frame.step_not_revert s input gas output hs)
    | exception input e =>
      simp [run, hs] at h
      subst result
      exact ⟨1, by omega,  .exception ((Frame.step_iff_rule _ _).mp hs)⟩
    | unsupported input op =>
      simp [run, hs] at h
      subst result
      exact ⟨1, by omega,  .unsupported ((Frame.step_iff_rule _ _).mp hs)⟩

/-- Exactly `n` independent continuing frame rules. -/
inductive Continues : Frame.State → Nat → Frame.State → Prop where
  | nil (s) : Continues s 0 s
  | next {s t u n} : Frame.Rule s (.continue t) → Continues t n u →
      Continues s (n + 1) u

/-- Exhaustion is exactly an all-continuing trace of the supplied length. -/
theorem run_exhausted_iff (fuel : Nat) (s t : Frame.State) :
    run fuel s = .exhausted t ↔ Continues s fuel t := by
  induction fuel generalizing s with
  | zero => simp only [run, Result.exhausted.injEq]; constructor
            · intro h; subst t; exact .nil _
            · intro h; cases h; rfl
  | succ fuel ih =>
    constructor
    · intro h
      cases hs : Frame.step s with
      | «continue» next =>
        exact .next ((Frame.step_iff_rule _ _).mp hs) ((ih next).mp (by simpa [run, hs] using h))
      | stop next => simp [run, hs] at h
      | revert input gas output => exact False.elim (Frame.step_not_revert s input gas output hs)
      | exception input e => simp [run, hs] at h
      | unsupported input op => simp [run, hs] at h
    · intro h
      cases h with
      | next hs ht =>
        simpa [run, Frame.rule_sound hs] using (ih _).mpr ht

/-- Any bounded result is either exact exhaustion or a terminal trace within fuel. -/
theorem run_characterization (fuel : Nat) (s : Frame.State) (r : Result) :
    run fuel s = r ↔
      (∃ t, r = .exhausted t ∧ Continues s fuel t) ∨
      (∃ n, n ≤ fuel ∧ Terminates s n r) := by
  constructor
  · intro h
    cases r with
    | exhausted t => exact .inl ⟨t, rfl, (run_exhausted_iff _ _ _).mp h⟩
    | reverted t gas output => exact .inr (terminates_of_run h (by intros; simp))
    | stopped t => exact .inr (terminates_of_run h (by intros; simp))
    | exception t e => exact .inr (terminates_of_run h (by intros; simp))
    | unsupported t op => exact .inr (terminates_of_run h (by intros; simp))
  · rintro (⟨t, rfl, ht⟩ | ⟨n, hn, ht⟩)
    · exact (run_exhausted_iff _ _ _).mpr ht
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hn
      exact run_of_terminates ht extra

/-- No finite terminal trace in this slice ends in a revert. -/
theorem terminates_not_reverted {s : Frame.State} {n : Nat} {input : Frame.State}
    {gas : Nat} {output : ByteArray} (h : Terminates s n (.reverted input gas output)) : False := by
  generalize hr : Result.reverted input gas output = r at h
  induction h with
  | stop _ => cases hr
  | exception _ => cases hr
  | unsupported _ => cases hr
  | next _ _ ih => exact ih hr

/-- The restricted runner cannot produce a revert for any fuel or input. -/
theorem run_not_reverted (fuel : Nat) (s input : Frame.State) (gas : Nat)
    (output : ByteArray) : run fuel s ≠ .reverted input gas output := by
  intro h
  obtain ⟨_, _, trace⟩ := terminates_of_run h (by intros; simp)
  exact terminates_not_reverted trace

/-- A terminal result remains the same with additional fuel. -/
theorem run_terminal_stable {fuel : Nat} {s : Frame.State} {r : Result}
    (h : run fuel s = r) (terminal : ∀ t, r ≠ .exhausted t) (extra : Nat) :
    run (fuel + extra) s = r := by
  obtain ⟨n, hn, ht⟩ := terminates_of_run h terminal
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa [Nat.add_assoc] using run_of_terminates ht (k + extra)

/-- A finite terminal relation has a unique result. -/
theorem terminates_deterministic {s : Frame.State} {n m : Nat} {r q : Result}
    (h : Terminates s n r) (k : Terminates s m q) : r = q := by
  have a := run_of_terminates h m
  have b := run_of_terminates k n
  rw [Nat.add_comm] at b
  exact a.symm.trans b

/-- Splitting fuel resumes exactly when the first run exhausts. -/
theorem run_add (fuel extra : Nat) (s : Frame.State) :
    run (fuel + extra) s =
      match run fuel s with
      | .exhausted t => run extra t
      | r => r := by
  induction fuel generalizing s with
  | zero => simp [run]
  | succ fuel ih =>
    cases hs : Frame.step s <;> simp [run, hs, Nat.succ_add, ih]

/-- The settlement projection has exactly these cases. -/
theorem settle_cases (r : Result) :
    settle r = match r with
      | .stopped s => some (.stopped s.gas)
      | .reverted _ gas output => some (.reverted gas output)
      | .exception _ e => some (.exceptional 0 e)
      | .unsupported _ _ | .exhausted _ => none := by
  cases r <;> rfl

/-- All bounded runs preserve code. -/
theorem run_code_unchanged (fuel : Nat) (s : Frame.State) :
    (run fuel s).frame.code = s.code := by
  induction fuel generalizing s with
  | zero => simp [run, Result.frame]
  | succ fuel ih =>
    cases hs : Frame.step s with
    | «continue» next =>
      have same := Frame.continue_code_unchanged hs
      have rest := ih next
      simpa [run, hs, same] using rest
    | stop next =>
      have same := Frame.outcome_code_unchanged ((Frame.step_iff_rule _ _).mp hs)
      simpa [run, hs, Result.frame, Frame.Outcome.frame] using same
    | revert input gas output => exact False.elim (Frame.step_not_revert s input gas output hs)
    | exception input e =>
      have same := Frame.outcome_code_unchanged ((Frame.step_iff_rule _ _).mp hs)
      simpa [run, hs, Result.frame, Frame.Outcome.frame] using same
    | unsupported input op =>
      have same := Frame.outcome_code_unchanged ((Frame.step_iff_rule _ _).mp hs)
      simpa [run, hs, Result.frame, Frame.Outcome.frame] using same

/-- All bounded runs preserve context. -/
theorem run_context_unchanged (fuel : Nat) (s : Frame.State) :
    (run fuel s).frame.context = s.context := by
  induction fuel generalizing s with
  | zero => simp [run, Result.frame]
  | succ fuel ih =>
    cases hs : Frame.step s with
    | «continue» next =>
      have same := Frame.continue_context_unchanged hs
      have rest := ih next
      simpa [run, hs, same] using rest
    | stop next =>
      have same := Frame.outcome_context_unchanged ((Frame.step_iff_rule _ _).mp hs)
      simpa [run, hs, Result.frame, Frame.Outcome.frame] using same
    | revert input gas output => exact False.elim (Frame.step_not_revert s input gas output hs)
    | exception input e =>
      have same := Frame.outcome_context_unchanged ((Frame.step_iff_rule _ _).mp hs)
      simpa [run, hs, Result.frame, Frame.Outcome.frame] using same
    | unsupported input op =>
      have same := Frame.outcome_context_unchanged ((Frame.step_iff_rule _ _).mp hs)
      simpa [run, hs, Result.frame, Frame.Outcome.frame] using same

/-- Every executed instruction in the bounded run is outside memory access. -/
def PureMemoryRun : Nat → Frame.State → Prop
  | 0, _ => True
  | fuel + 1, s => Frame.PureMemoryStep s ∧
      match Frame.step s with
      | .continue t => PureMemoryRun fuel t
      | _ => True

/-- A bounded run of pure instructions preserves memory. -/
theorem run_memory_unchanged_of_pure (fuel : Nat) (s : Frame.State)
    (pure : PureMemoryRun fuel s) : (run fuel s).frame.memory = s.memory := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    have current := pure.1
    cases hs : Frame.step s with
    | «continue» next =>
      have same := Frame.continue_memory_unchanged_of_pure current hs
      have rest := ih next (by simpa [PureMemoryRun, hs] using pure.2)
      simpa [run, hs, same] using rest
    | stop next =>
      have same := Frame.outcome_memory_unchanged_of_pure current ((Frame.step_iff_rule _ _).mp hs)
      simpa [run, hs, Result.frame, Frame.Outcome.frame] using same
    | revert input gas output => exact False.elim (Frame.step_not_revert s input gas output hs)
    | exception input e =>
      have same := Frame.outcome_memory_unchanged_of_pure current ((Frame.step_iff_rule _ _).mp hs)
      simpa [run, hs, Result.frame, Frame.Outcome.frame] using same
    | unsupported input op =>
      have same := Frame.outcome_memory_unchanged_of_pure current ((Frame.step_iff_rule _ _).mp hs)
      simpa [run, hs, Result.frame, Frame.Outcome.frame] using same

end EthLib.EVM.Runner
