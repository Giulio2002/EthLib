module

public import EthLib.EVM.Proofs.Runner
public import EthLib.EVM.Proofs.Frame.Balance

/-! BALANCE followed by SWAP1 and a second BALANCE. -/

@[expose] public section
namespace EthLib.EVM.Runner.BalanceProgram

/-- The second access observes the address warmed by the first. -/
def program : ByteArray := ⟨#[0x31, 0x90, 0x31, 0x00]⟩

/-- A cold access followed by a warm access costs 3000 + 3 + 100 gas. -/
theorem run (x : Word) (xs : List Word) (room : xs.length ≤ 1022) (g : Nat)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem)
    (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State)
    (warm : List World.Address) (warmSlots : List (World.Address × Word)) (static : Bool) (stateGas : Frame.StateGas) (logs : List Frame.LogEntry) (cold : Frame.BalanceAddress x ∉ warm) :
    let s : Frame.State := ⟨program, 0, ⟨x :: x :: xs, by simp; omega⟩,
      3103 + g, mem, valid, context, returnData, tracker, warm, warmSlots, static, stateGas, logs⟩
    ∃ t, Runner.run 4 s = .stopped t ∧ t.pc = 4 ∧ t.gas = g ∧
      t.stack.val = (Frame.BalanceAccount s (Frame.BalanceAddress x)).balance ::
        (Frame.BalanceAccount s (Frame.BalanceAddress x)).balance :: xs ∧
      t.warmAddresses = Frame.BalanceAddress x :: warm ∧
      t.tracker = { tracker with accountReads := Frame.BalanceAddress x :: Frame.BalanceAddress x :: tracker.accountReads } ∧
      t.code = program ∧ t.memory = mem ∧ t.context = context ∧ t.returnData = returnData := by
  let a := Frame.BalanceAddress x
  let s : Frame.State := ⟨program, 0, ⟨x :: x :: xs, by simp; omega⟩, 3103 + g, mem, valid, context, returnData, tracker, warm, warmSlots, static, stateGas, logs⟩
  let v := (Frame.BalanceAccount s a).balance
  let r1 : Stack := ⟨x :: xs, by simp; omega⟩
  let r2 : Stack := ⟨v :: xs, by simp; omega⟩
  let s1 : Frame.State := { s with tracker := { tracker with accountReads := a :: tracker.accountReads }, warmAddresses := a :: warm, pc := 1, gas := 103 + g, stack := ⟨v :: x :: xs, by simp; omega⟩ }
  let s2 : Frame.State := { s1 with pc := 2, gas := 100 + g, stack := ⟨x :: v :: xs, by simp; omega⟩ }
  let s3 : Frame.State := { s2 with tracker := { tracker with accountReads := a :: a :: tracker.accountReads }, pc := 3, gas := g, stack := ⟨v :: v :: xs, by simp; omega⟩ }
  let s4 : Frame.State := { s3 with pc := 4 }
  have h1 : Frame.Rule s (.continue s1) := by
    apply Frame.Rule.balance s s1 r1 x
    · simp [Frame.At, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [Frame.BalanceCost, s, cold]; omega
    · simp [Frame.Advances, Frame.BalanceCost, Frame.BalanceWarm, Frame.BalanceRead, s, s1, r1, a, v, cold]; omega
  have h2 : Frame.Rule s1 (.continue s2) := by
    apply Frame.Rule.swap s1 s2 ⟨0, by decide⟩ (by simp [s1])
    · simp [Frame.At, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s1]; omega
    · simp [Frame.Advances, s1, s2]; omega
  have h3 : Frame.Rule s2 (.continue s3) := by
    apply Frame.Rule.balance s2 s3 r2 x
    · simp [Frame.At, s2, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [Frame.BalanceCost, s2, s1, a]
    · simp [Frame.Advances, Frame.BalanceCost, Frame.BalanceWarm, Frame.BalanceRead, Frame.BalanceAccount, s2, s1, s3, s, r2, a, v]
  have h4 : Frame.Rule s3 (.stop s4) := by
    apply Frame.Rule.stop
    simp [Frame.At, s3, s2, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
  have trace : Runner.Terminates s 4 (.stopped s4) := .next h1 (.next h2 (.next h3 (.stop h4)))
  have result := Runner.run_of_terminates trace 0
  exact ⟨s4, by simpa [s] using result, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every bounded outcome retains addresses warm at the start of the run. -/
theorem run_warm_monotone (fuel : Nat) (s : Frame.State) (a : World.Address)
    (warm : a ∈ s.warmAddresses) : a ∈ (Runner.run fuel s).frame.warmAddresses := by
  induction fuel generalizing s with
  | zero => simpa [Runner.run, Result.frame] using warm
  | succ fuel ih =>
    cases hs : Frame.step s with
    | «continue» next =>
      have same := Frame.outcome_warm_monotone ((Frame.step_iff_rule _ _).mp hs) a warm
      simp only [Frame.Outcome.frame] at same
      simpa [Runner.run, hs] using ih next same
    | stop next =>
      have same := Frame.outcome_warm_monotone ((Frame.step_iff_rule _ _).mp hs) a warm
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same
    | returned input output =>
      have same := Frame.outcome_warm_monotone ((Frame.step_iff_rule _ _).mp hs) a warm
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same
    | revert input gas output =>
      have same := Frame.outcome_warm_monotone ((Frame.step_iff_rule _ _).mp hs) a warm
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same

    | exception input e =>
      have same := Frame.outcome_warm_monotone ((Frame.step_iff_rule _ _).mp hs) a warm
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same
    | unsupported input op =>
      have same := Frame.outcome_warm_monotone ((Frame.step_iff_rule _ _).mp hs) a warm
      simpa [Runner.run, hs, Result.frame, Frame.Outcome.frame] using same

end EthLib.EVM.Runner.BalanceProgram
