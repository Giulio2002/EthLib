module

public import EthLib.EVM.Proofs.Runner

/-!
# Straight-line frame contract

Cancun execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`,
`vm/instructions/control_flow.py`, `stop`, advances the counter past STOP.
-/

@[expose] public section
namespace EthLib.EVM.Runner.StraightLine

/-- Two PUSH1 instructions followed by ADD and STOP. -/
def program (a b : UInt8) : ByteArray := ⟨#[0x60, a, 0x60, b, 0x01, 0x00]⟩

/-- Arbitrary immediate bytes execute with two stack slots and nine gas. -/
theorem push_push_add_stop (a b : UInt8) (xs : List Word) (room : xs.length ≤ 1022)
    (g : Nat) (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem) (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State) :
    ∃ t, Runner.run 4 ⟨program a b, 0, ⟨xs, by omega⟩, 9 + g, mem, valid, context, returnData, tracker⟩ = .stopped t ∧
      t.pc = 6 ∧ t.gas = g ∧
      t.stack.val = Word.add (BitVec.ofNat 256 b.toNat) (BitVec.ofNat 256 a.toNat) :: xs := by
  let wa : Word := BitVec.ofNat 256 a.toNat
  let wb : Word := BitVec.ofNat 256 b.toNat
  let s : Frame.State := ⟨program a b, 0, ⟨xs, by omega⟩, 9 + g, mem, valid, context, returnData, tracker⟩
  let s1 : Frame.State := { s with pc := 2, gas := 6 + g, stack := ⟨wa :: xs, by simp; omega⟩ }
  let s2 : Frame.State := { s with pc := 4, gas := 3 + g, stack := ⟨wb :: wa :: xs, by simp; omega⟩ }
  let s3 : Frame.State := { s with pc := 5, gas := g, stack := ⟨Word.add wb wa :: xs, by simp; omega⟩ }
  let s4 : Frame.State := { s3 with pc := 6 }
  have h1 : Frame.Rule s (.continue s1) := by
    apply Frame.Rule.push s s1 ⟨1, by decide⟩
    · simp [Frame.At, s, program, ByteArray.size, -ByteArray.size_data,
        ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s]; omega
    · simp [s]; omega
    · simp [Frame.Advances, s, s1, wa, PushImmediate.nextPC, PushImmediate.value,
        PushImmediate.bytes, PushImmediate.byteAt, program, ByteArray.size, -ByteArray.size_data,
        ByteArray.getElem_eq_getElem_data]
      omega
  have h2 : Frame.Rule s1 (.continue s2) := by
    apply Frame.Rule.push s1 s2 ⟨1, by decide⟩
    · simp [Frame.At, s1, s, program, ByteArray.size, -ByteArray.size_data,
        ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s1]; omega
    · simp [s1]; omega
    · simp [Frame.Advances, s, s1, s2, wb, PushImmediate.nextPC, PushImmediate.value,
        PushImmediate.bytes, PushImmediate.byteAt, program, ByteArray.size, -ByteArray.size_data,
        ByteArray.getElem_eq_getElem_data]
      omega
  have h3 : Frame.Rule s2 (.continue s3) := by
    apply Frame.Rule.add s2 s3 wb wa xs
    · simp [Frame.At, s2, s, program, ByteArray.size, -ByteArray.size_data,
        ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s2]
    · simp [Frame.Advances, s2, s3]
  have h4 : Frame.Rule s3 (.stop s4) := by
    apply Frame.Rule.stop
    simp [Frame.At, s3, s, program, ByteArray.size, -ByteArray.size_data,
      ByteArray.getElem_eq_getElem_data, Opcode.decode]
  have trace : Runner.Terminates s 4 (.stopped s4) :=
    .next h1 (.next h2 (.next h3 (.stop h4)))
  have run := Runner.run_of_terminates trace 0
  refine ⟨s4, ?_, ?_, ?_, ?_⟩
  · simpa [s] using run
  · rfl
  · rfl
  · rfl

/-- PUSH1 2, PUSH1 3, ADD and STOP leave five on an empty stack. -/
theorem two_plus_three (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem) (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State) :
    ∃ t, Runner.run 4 ⟨program 2 3, 0, Stack.empty, 9, mem, valid, context, returnData, tracker⟩ = .stopped t ∧
      t.pc = 6 ∧ t.gas = 0 ∧ t.stack.val = [5] := by
  have h := push_push_add_stop 2 3 [] (by simp) 0 mem valid context returnData tracker
  simpa [Stack.empty, Word.add] using h

end EthLib.EVM.Runner.StraightLine
