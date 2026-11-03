module

public import EthLib.EVM.Proofs.Frame
import Aesop

@[expose] public section
namespace EthLib.EVM.Frame

/-- The next instruction is not any member of the LOG family. -/
def NoLogStep (s : State) : Prop := ∀ n, ¬ At s (some (.log n))

/-- A non-LOG rule preserves all accumulated frame logs. -/
theorem outcome_logs_unchanged_of_noLog {s : State} {out : Outcome}
    (noLog : NoLogStep s) (h : Rule s out) : out.frame.logs = s.logs := by
  cases h <;> simp_all [NoLogStep, Outcome.frame, Advances, AdvancesMemory, SstoreReady,
    SstoreReadFields, SstoreCreditFields, SstoreExecutionFields, SstoreChargeFields,
    SstoreMeterRetained, SstoreWriteFields] <;> aesop

/-- Every executable non-LOG outcome preserves all accumulated logs. -/
theorem step_logs_unchanged_of_noLog (s : State) (noLog : NoLogStep s) :
    (step s).frame.logs = s.logs :=
  outcome_logs_unchanged_of_noLog noLog ((step_iff_rule s _).mp rfl)

/-- Every rule retains the original log sequence as a prefix. -/
theorem outcome_logs_prefix {s : State} {out : Outcome} (h : Rule s out) :
    ∃ suffix, out.frame.logs = s.logs ++ suffix := by
  cases h <;> simp_all [Outcome.frame, Advances, AdvancesMemory, SstoreReady,
    SstoreReadFields, SstoreCreditFields, SstoreExecutionFields, SstoreChargeFields,
    SstoreMeterRetained, SstoreWriteFields] <;> aesop

end EthLib.EVM.Frame
