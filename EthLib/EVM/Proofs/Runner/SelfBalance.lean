module

public import EthLib.EVM.Proofs.Runner
public import EthLib.EVM.Proofs.Frame.SelfBalance

/-! A bounded program executes SELFBALANCE, PC and STOP. -/

@[expose] public section
namespace EthLib.EVM.Runner

/-- Every instruction in this bounded trace is different from SSTORE. -/
def NoSstoreRun : Nat → Frame.State → Prop
  | 0, _ => True
  | fuel + 1, s => ¬ Frame.At s (some .sstore) ∧
      match Frame.step s with
      | .continue t => NoSstoreRun fuel t
      | _ => True

/-- Every instruction in this bounded trace is different from TSTORE. -/
def NoTstoreRun : Nat → Frame.State → Prop
  | 0, _ => True
  | fuel + 1, s => ¬ Frame.At s (some .tstore) ∧
      match Frame.step s with
      | .continue t => NoTstoreRun fuel t
      | _ => True

end EthLib.EVM.Runner

namespace EthLib.EVM.Runner.SelfBalanceProgram

/-- The instruction sequence used by the mixed runner theorem. -/
def program : ByteArray := ⟨#[0x47, 0x58, 0x00]⟩

/-- The real runner preserves the tracker except for the current-target read. -/
theorem run (xs : List Word) (room : xs.length ≤ 1022) (g : Nat)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem)
    (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State) (warmAddresses : List World.Address) (warmSlots : List (World.Address × Word)) (static : Bool) (stateGas : Frame.StateGas) (logs : List Frame.LogEntry) :
    let s : Frame.State := ⟨program, 0, ⟨xs, by omega⟩, 7 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots, static, stateGas, logs⟩
    ∃ t, Runner.run 3 s = .stopped t ∧ t.pc = 3 ∧ t.gas = g ∧
      t.stack.val = 1 :: (Frame.SelfBalanceAccount s).balance :: xs ∧
      t.tracker = Frame.SelfBalanceRead s ∧ t.memory = mem ∧ t.context = context ∧
      t.returnData = returnData ∧ t.code = program := by
  let s : Frame.State := ⟨program, 0, ⟨xs, by omega⟩, 7 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots, static, stateGas, logs⟩
  let s1 : Frame.State := { s with tracker := Frame.SelfBalanceRead s, pc := 1, gas := 2 + g, stack := ⟨(Frame.SelfBalanceAccount s).balance :: xs, by simp; omega⟩ }
  let s2 : Frame.State := { s1 with pc := 2, gas := g, stack := ⟨1 :: (Frame.SelfBalanceAccount s).balance :: xs, by simp; omega⟩ }
  let s3 : Frame.State := { s2 with pc := 3 }
  have h1 : Frame.Rule s (.continue s1) := by
    apply Frame.Rule.selfBalance s s1
    · simp [Frame.At, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s]; omega
    · simp [s]; omega
    · simp [Frame.Advances, s, s1]; omega
  have h2 : Frame.Rule s1 (.continue s2) := by
    apply Frame.Rule.observation s1 s2 .pc
    · simp [Frame.At, Frame.Observation.opcode, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s1]
    · simp [s1, s]; omega
    · simp [Frame.Advances, Frame.Observation.value, s1, s2]
  have h3 : Frame.Rule s2 (.stop s3) := by
    apply Frame.Rule.stop
    simp [Frame.At, s2, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
  have trace : Runner.Terminates s 3 (.stopped s3) := .next h1 (.next h2 (.stop h3))
  have result := Runner.run_of_terminates trace 0
  exact ⟨s3, by simpa [s] using result, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every bounded outcome without SSTORE or TSTORE preserves the tracker parent, writes, created accounts and snapshots. -/
theorem run_tracker_retained (fuel : Nat) (s : Frame.State) (trace : Runner.NoSstoreRun fuel s) (noTransient : Runner.NoTstoreRun fuel s) :
    (Runner.run fuel s).frame.tracker.parent = s.tracker.parent ∧
    (Runner.run fuel s).frame.tracker.writes = s.tracker.writes ∧
    (Runner.run fuel s).frame.tracker.createdAccounts = s.tracker.createdAccounts ∧
    (Runner.run fuel s).frame.tracker.snapshots = s.tracker.snapshots := by
  induction fuel generalizing s with
  | zero => simp [Runner.run, Result.frame]
  | succ fuel ih =>
    have current := trace.1
    cases hs : Frame.step s with
    | «continue» next =>
      have same := Frame.outcome_tracker_retained current noTransient.1 ((Frame.step_iff_rule _ _).mp hs)
      have rest := ih next (by simpa [Runner.NoSstoreRun, hs] using trace.2)
        (by simpa [Runner.NoTstoreRun, hs] using noTransient.2)
      simp only [Frame.Outcome.frame] at same
      simp only [Runner.run, hs]
      exact ⟨rest.1.trans same.1, rest.2.1.trans same.2.1,
        rest.2.2.1.trans same.2.2.1, rest.2.2.2.trans same.2.2.2⟩
    | stop next =>
      have same := Frame.outcome_tracker_retained current noTransient.1 ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same
    | returned input output =>
      have same := Frame.outcome_tracker_retained current noTransient.1 ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same
    | revert input gas output =>
      have same := Frame.outcome_tracker_retained current noTransient.1 ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same

    | exception input e =>
      have same := Frame.outcome_tracker_retained current noTransient.1 ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same
    | unsupported input op =>
      have same := Frame.outcome_tracker_retained current noTransient.1 ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same

/-- Every bounded outcome without SSTORE retains the persistent write components. -/
theorem run_persistent_writes_unchanged_of_no_sstore (fuel : Nat) (s : Frame.State)
    (trace : Runner.NoSstoreRun fuel s) :
    (Runner.run fuel s).frame.tracker.writes.accountWrites = s.tracker.writes.accountWrites ∧
    (Runner.run fuel s).frame.tracker.writes.storageWrites = s.tracker.writes.storageWrites ∧
    (Runner.run fuel s).frame.tracker.writes.codeWrites = s.tracker.writes.codeWrites ∧
    (Runner.run fuel s).frame.tracker.writes.storageClears = s.tracker.writes.storageClears := by
  induction fuel generalizing s with
  | zero => simp [Runner.run, Result.frame]
  | succ fuel ih =>
    have current := trace.1
    cases hs : Frame.step s with
    | «continue» next =>
      have same := Frame.outcome_persistent_writes_unchanged_of_not_sstore current ((Frame.step_iff_rule _ _).mp hs)
      have rest := ih next (by simpa [Runner.NoSstoreRun, hs] using trace.2)
      simp only [Frame.Outcome.frame] at same
      simp only [Runner.run, hs]
      exact ⟨rest.1.trans same.1, rest.2.1.trans same.2.1,
        rest.2.2.1.trans same.2.2.1, rest.2.2.2.trans same.2.2.2⟩
    | stop next =>
      have same := Frame.outcome_persistent_writes_unchanged_of_not_sstore current ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same
    | returned input output =>
      have same := Frame.outcome_persistent_writes_unchanged_of_not_sstore current ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same
    | revert input gas output =>
      have same := Frame.outcome_persistent_writes_unchanged_of_not_sstore current ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same

    | exception input e =>
      have same := Frame.outcome_persistent_writes_unchanged_of_not_sstore current ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same
    | unsupported input op =>
      have same := Frame.outcome_persistent_writes_unchanged_of_not_sstore current ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same

/-- Every bounded outcome retains the transaction parent, created markers, and snapshots. -/
theorem run_tracker_metadata_retained (fuel : Nat) (s : Frame.State) :
    (Runner.run fuel s).frame.tracker.parent = s.tracker.parent ∧
    (Runner.run fuel s).frame.tracker.createdAccounts = s.tracker.createdAccounts ∧
    (Runner.run fuel s).frame.tracker.snapshots = s.tracker.snapshots := by
  induction fuel generalizing s with
  | zero => simp [Runner.run, Result.frame]
  | succ fuel ih =>
    cases hs : Frame.step s with
    | «continue» next =>
      have same := Frame.outcome_tracker_metadata_retained ((Frame.step_iff_rule _ _).mp hs)
      have rest := ih next
      simp only [Frame.Outcome.frame] at same
      simp only [Runner.run, hs]
      exact ⟨rest.1.trans same.1, rest.2.1.trans same.2.1, rest.2.2.trans same.2.2⟩
    | stop next =>
      have same := Frame.outcome_tracker_metadata_retained ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same
    | returned input output =>
      have same := Frame.outcome_tracker_metadata_retained ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same
    | revert input gas output =>
      have same := Frame.outcome_tracker_metadata_retained ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same

    | exception input e =>
      have same := Frame.outcome_tracker_metadata_retained ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same
    | unsupported input op =>
      have same := Frame.outcome_tracker_metadata_retained ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same


/-- Every bounded outcome retains the static-context flag. -/
theorem run_static_retained (fuel : Nat) (s : Frame.State) :
    (Runner.run fuel s).frame.isStatic = s.isStatic := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    cases hs : Frame.step s with
    | «continue» next =>
      have same := Frame.outcome_static_retained ((Frame.step_iff_rule _ _).mp hs)
      simp only [Frame.Outcome.frame] at same
      simpa [Runner.run, hs, same] using ih next
    | stop next =>
      have same := Frame.outcome_static_retained ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same
    | returned input output =>
      have same := Frame.outcome_static_retained ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same
    | revert input gas output =>
      have same := Frame.outcome_static_retained ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same

    | exception input e =>
      have same := Frame.outcome_static_retained ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same
    | unsupported input op =>
      have same := Frame.outcome_static_retained ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same

/-- Without SSTORE, every bounded outcome retains the state-gas bookkeeping. -/
theorem run_stateGas_unchanged_of_no_sstore (fuel : Nat) (s : Frame.State)
    (trace : Runner.NoSstoreRun fuel s) : (Runner.run fuel s).frame.stateGas = s.stateGas := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    have current := trace.1
    cases hs : Frame.step s with
    | «continue» next =>
      have same := Frame.outcome_stateGas_unchanged_of_not_sstore current ((Frame.step_iff_rule _ _).mp hs)
      simp only [Frame.Outcome.frame] at same
      have rest := ih next (by simpa [Runner.NoSstoreRun, hs] using trace.2)
      simpa [Runner.run, hs, same] using rest
    | stop next =>
      have same := Frame.outcome_stateGas_unchanged_of_not_sstore current ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same
    | returned input output =>
      have same := Frame.outcome_stateGas_unchanged_of_not_sstore current ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same
    | revert input gas output =>
      have same := Frame.outcome_stateGas_unchanged_of_not_sstore current ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same

    | exception input e =>
      have same := Frame.outcome_stateGas_unchanged_of_not_sstore current ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same
    | unsupported input op =>
      have same := Frame.outcome_stateGas_unchanged_of_not_sstore current ((Frame.step_iff_rule _ _).mp hs)
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same

end EthLib.EVM.Runner.SelfBalanceProgram

namespace EthLib.EVM.Runner

/-- Each executed instruction in this bounded trace is not SLOAD. -/
def NoSloadRun : Nat → Frame.State → Prop
  | 0, _ => True
  | fuel + 1, s => ¬ Frame.At s (some .sload) ∧
      match Frame.step s with
      | .continue t => NoSloadRun fuel t
      | _ => True

/-- Every outcome of a bounded run without SLOAD preserves storage reads. -/
theorem run_storageReads_unchanged_of_no_sload (fuel : Nat) (s : Frame.State)
    (trace : NoSloadRun fuel s) (noStore : NoSstoreRun fuel s) :
    (run fuel s).frame.tracker.storageReads = s.tracker.storageReads := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    have current := trace.1
    cases hs : Frame.step s with
    | «continue» next =>
      have same := Frame.outcome_storageReads_unchanged_of_not_sload current noStore.1 ((Frame.step_iff_rule _ _).mp hs)
      simp only [Frame.Outcome.frame] at same
      have rest := ih next (by simpa [NoSloadRun, hs] using trace.2) (by simpa [NoSstoreRun, hs] using noStore.2)
      simpa [run, hs, same] using rest
    | stop next =>
      have same := Frame.outcome_storageReads_unchanged_of_not_sload current noStore.1 ((Frame.step_iff_rule _ _).mp hs)
      simpa [run, hs, Result.frame, Frame.Outcome.frame] using same
    | returned input output =>
      have same := Frame.outcome_storageReads_unchanged_of_not_sload current noStore.1 ((Frame.step_iff_rule _ _).mp hs)
      simpa [run, hs, Result.frame, Frame.Outcome.frame] using same
    | revert input gas output =>
      have same := Frame.outcome_storageReads_unchanged_of_not_sload current noStore.1 ((Frame.step_iff_rule _ _).mp hs)
      simpa [run, hs, Result.frame, Frame.Outcome.frame] using same

    | exception input e =>
      have same := Frame.outcome_storageReads_unchanged_of_not_sload current noStore.1 ((Frame.step_iff_rule _ _).mp hs)
      simpa [run, hs, Result.frame, Frame.Outcome.frame] using same
    | unsupported input op =>
      have same := Frame.outcome_storageReads_unchanged_of_not_sload current noStore.1 ((Frame.step_iff_rule _ _).mp hs)
      simpa [run, hs, Result.frame, Frame.Outcome.frame] using same

end EthLib.EVM.Runner
