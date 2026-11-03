module

public import EthLib.EVM.Proofs.Runner
public import EthLib.EVM.Proofs.Frame.Sload

/-! SLOAD followed by SWAP1 and a second SLOAD. -/

@[expose] public section
namespace EthLib.EVM.Runner.SloadProgram

/-- The second access observes the slot warmed by the first. -/
def program : ByteArray := ⟨#[0x54, 0x90, 0x54, 0x00]⟩

/-- A cold read followed by a warm read costs 2100 + 3 + 100 gas. -/
theorem run (key : Word) (xs : List Word) (room : xs.length ≤ 1022) (g : Nat)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem)
    (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State)
    (warm : List World.Address) (slots : List (World.Address × Word)) (static : Bool) (stateGas : Frame.StateGas) (logs : List Frame.LogEntry)
    (cold : (context.environment.currentTarget, key) ∉ slots) :
    let s : Frame.State := ⟨program, 0, ⟨key :: key :: xs, by simp; omega⟩,
      2203 + g, mem, valid, context, returnData, tracker, warm, slots, static, stateGas, logs⟩
    ∃ t, Runner.run 4 s = .stopped t ∧ t.pc = 4 ∧ t.gas = g ∧
      t.stack.val = Frame.SloadValue s key :: Frame.SloadValue s key :: xs ∧
      t.warmSlots = (context.environment.currentTarget, key) :: slots ∧ t.warmAddresses = warm ∧
      t.tracker = { tracker with storageReads := (context.environment.currentTarget, key) :: (context.environment.currentTarget, key) :: tracker.storageReads } ∧
      t.code = program ∧ t.memory = mem ∧ t.context = context ∧ t.returnData = returnData := by
  let slot := (context.environment.currentTarget, key)
  let s : Frame.State := ⟨program, 0, ⟨key :: key :: xs, by simp; omega⟩, 2203 + g, mem, valid, context, returnData, tracker, warm, slots, static, stateGas, logs⟩
  let v := Frame.SloadValue s key
  let r1 : Stack := ⟨key :: xs, by simp; omega⟩
  let r2 : Stack := ⟨v :: xs, by simp; omega⟩
  let s1 : Frame.State := { s with tracker := { tracker with storageReads := slot :: tracker.storageReads }, warmSlots := slot :: slots, pc := 1, gas := 103 + g, stack := ⟨v :: key :: xs, by simp; omega⟩ }
  let s2 : Frame.State := { s1 with pc := 2, gas := 100 + g, stack := ⟨key :: v :: xs, by simp; omega⟩ }
  let s3 : Frame.State := { s2 with tracker := { tracker with storageReads := slot :: slot :: tracker.storageReads }, pc := 3, gas := g, stack := ⟨v :: v :: xs, by simp; omega⟩ }
  let s4 : Frame.State := { s3 with pc := 4 }
  have h1 : Frame.Rule s (.continue s1) := by
    apply Frame.Rule.sload s s1 r1 key
    · simp [Frame.At, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [Frame.SloadCost, s, cold]; omega
    · simp [Frame.Advances, Frame.SloadCost, Frame.SloadWarm, Frame.SloadRead, s, s1, r1, slot, v, cold]; omega
  have h2 : Frame.Rule s1 (.continue s2) := by
    apply Frame.Rule.swap s1 s2 ⟨0, by decide⟩ (by simp [s1])
    · simp [Frame.At, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s1]; omega
    · simp [Frame.Advances, s1, s2]; omega
  have h3 : Frame.Rule s2 (.continue s3) := by
    apply Frame.Rule.sload s2 s3 r2 key
    · simp [Frame.At, s2, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [Frame.SloadCost, s2, s1, s, slot]
    · simp [Frame.Advances, Frame.SloadCost, Frame.SloadWarm, Frame.SloadRead, Frame.SloadValue, s2, s1, s3, s, r2, slot, v]
  have h4 : Frame.Rule s3 (.stop s4) := by
    apply Frame.Rule.stop
    simp [Frame.At, s3, s2, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
  have trace : Runner.Terminates s 4 (.stopped s4) := .next h1 (.next h2 (.next h3 (.stop h4)))
  have result := Runner.run_of_terminates trace 0
  exact ⟨s4, by simpa [s] using result, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every bounded result retains all slots that were warm at entry. -/
theorem run_slots_monotone (fuel : Nat) (s : Frame.State) (slot : World.Address × Word)
    (warm : slot ∈ s.warmSlots) : slot ∈ (Runner.run fuel s).frame.warmSlots := by
  induction fuel generalizing s with
  | zero => simpa [Runner.run, Result.frame] using warm
  | succ fuel ih =>
    cases hs : Frame.step s with
    | «continue» next =>
      have same := Frame.outcome_slots_monotone ((Frame.step_iff_rule _ _).mp hs) slot warm
      simp only [Frame.Outcome.frame] at same
      simpa [Runner.run, hs] using ih next same
    | stop next =>
      have same := Frame.outcome_slots_monotone ((Frame.step_iff_rule _ _).mp hs) slot warm
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same
    | returned input output =>
      have same := Frame.outcome_slots_monotone ((Frame.step_iff_rule _ _).mp hs) slot warm
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same
    | revert input gas output =>
      have same := Frame.outcome_slots_monotone ((Frame.step_iff_rule _ _).mp hs) slot warm
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same

    | exception input e =>
      have same := Frame.outcome_slots_monotone ((Frame.step_iff_rule _ _).mp hs) slot warm
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same
    | unsupported input op =>
      have same := Frame.outcome_slots_monotone ((Frame.step_iff_rule _ _).mp hs) slot warm
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same
    | callRequest input request =>
      have same := Frame.outcome_slots_monotone ((Frame.step_iff_rule _ _).mp hs) slot warm
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same

end EthLib.EVM.Runner.SloadProgram
