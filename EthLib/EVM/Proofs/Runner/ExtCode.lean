module

public import EthLib.EVM.Proofs.Frame.ExtCodeSize
public import EthLib.EVM.Proofs.Frame.ExtCodeHash
public import EthLib.EVM.Proofs.Runner

/-! A cold code-size query followed by a warm code-hash query. -/

@[expose] public section
namespace EthLib.EVM.Runner.ExtCodeProgram

/-- EXTCODESIZE, POP, EXTCODEHASH, STOP. -/
def program : ByteArray := ⟨#[0x3b, 0x50, 0x3f, 0x00]⟩

/-- The real runner charges cold then warm access for arbitrary supplied state. -/
theorem run (xs : List Word) (room : xs.length ≤ 1022) (x : Word) (g : Nat)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem)
    (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State)
    (warm : List World.Address) (slots : List (World.Address × Word)) (static : Bool) (meter : Frame.StateGas) (logs : List Frame.LogEntry)
    (cold : Frame.BalanceAddress x ∉ warm) (code : ByteArray)
    (present : Frame.ExtCodeBytes
      ⟨program, 0, ⟨x :: x :: xs, by simp; omega⟩, 3202 + g, mem, valid, context, returnData, tracker, warm, slots, static, meter, logs⟩
      (Frame.BalanceAddress x) = some code) :
    let s : Frame.State := ⟨program, 0, ⟨x :: x :: xs, by simp; omega⟩, 3202 + g,
      mem, valid, context, returnData, tracker, warm, slots, static, meter, logs⟩
    ∃ t, Runner.run 4 s = .stopped t ∧ t.pc = 4 ∧ t.gas = g ∧
      t.stack.val = Frame.ExtCodeHashValue s (Frame.BalanceAddress x) :: xs ∧
      t.tracker = { tracker with accountReads := Frame.BalanceAddress x :: Frame.BalanceAddress x :: tracker.accountReads } ∧
      t.warmAddresses = Frame.BalanceAddress x :: warm := by
  let a := Frame.BalanceAddress x
  let s : Frame.State := ⟨program, 0, ⟨x :: x :: xs, by simp; omega⟩, 3202 + g,
    mem, valid, context, returnData, tracker, warm, slots, static, meter, logs⟩
  let s1 : Frame.State := { s with tracker := Frame.BalanceRead s a, warmAddresses := a :: warm, pc := 1, gas := 102 + g, stack := ⟨BitVec.ofNat 256 code.size :: x :: xs, by simp; omega⟩ }
  let s2 : Frame.State := { s1 with pc := 2, gas := 100 + g, stack := ⟨x :: xs, by simp; omega⟩ }
  let s3 : Frame.State := { s2 with tracker := Frame.BalanceRead s2 a, pc := 3, gas := g, stack := ⟨Frame.ExtCodeHashValue s a :: xs, by simp; omega⟩ }
  let s4 : Frame.State := { s3 with pc := 4 }
  have r1 : Frame.Rule s (.continue s1) := by
    apply Frame.Rule.extCodeSize s s1 ⟨x :: xs, by simp; omega⟩ x code
    · simp [Frame.At, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [Frame.ExtCodeSizeCost, Frame.BalanceCost, s, cold]; omega
    · exact present
    · simp [Frame.Advances, Frame.ExtCodeSizeCost, Frame.BalanceCost, Frame.BalanceWarm, s, s1, a, cold]; omega
  have r2 : Frame.Rule s1 (.continue s2) := by
    apply Frame.Rule.pop s1 s2 (BitVec.ofNat 256 code.size) (x :: xs)
    · simp [Frame.At, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s1]; omega
    · simp [Frame.Advances, s1, s2]; omega
  have r3 : Frame.Rule s2 (.continue s3) := by
    apply Frame.Rule.extCodeHash s2 s3 ⟨xs, by omega⟩ x
    · simp [Frame.At, s2, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [Frame.BalanceCost, s2, s1, a]
    · simp [Frame.Advances, Frame.BalanceCost, Frame.BalanceWarm, Frame.ExtCodeHashValue, Frame.BalanceAccount, s3, s2, s1, s, a, Frame.BalanceRead]; rfl
  have r4 : Frame.Rule s3 (.stop s4) := by
    apply Frame.Rule.stop
    simp [Frame.At, s3, s2, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
  have trace : Runner.Terminates s 4 (.stopped s4) := .next r1 (.next r2 (.next r3 (.stop r4)))
  have result := Runner.run_of_terminates trace 0
  exact ⟨s4, by simpa [s] using result, rfl, rfl, rfl, rfl, rfl⟩

end EthLib.EVM.Runner.ExtCodeProgram
