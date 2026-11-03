module

public import EthLib.EVM.Proofs.Runner
public import EthLib.EVM.Proofs.Frame.CountLeadingZeros

/-! A mixed arithmetic and CLZ program. -/

@[expose] public section
namespace EthLib.EVM.Runner.CountLeadingZeros

/-- ADD, CLZ, PC and STOP. -/
def program : ByteArray := ⟨#[0x01, 0x1e, 0x58, 0x00]⟩

/-- The program has exact stack and gas for arbitrary context and valid memory. -/
theorem run (x y : Word) (xs : List Word) (room : xs.length ≤ 1022)
    (g : Nat) (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem)
    (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State) (warmAddresses : List World.Address) :
    ∃ t, Runner.run 4 ⟨program, 0, ⟨x :: y :: xs, by simp; omega⟩,
      10 + g, mem, valid, context, returnData, tracker, warmAddresses⟩ = .stopped t ∧
      t.pc = 4 ∧ t.gas = g ∧ t.code = program ∧ t.memory = mem ∧
      t.context = context ∧ t.returnData = returnData ∧
      t.stack.val = 2 :: Word.countLeadingZeros (Word.add x y) :: xs := by
  let z := Word.countLeadingZeros (Word.add x y)
  let s : Frame.State := ⟨program, 0, ⟨x :: y :: xs, by simp; omega⟩,
    10 + g, mem, valid, context, returnData, tracker, warmAddresses⟩
  let s1 : Frame.State := { s with pc := 1, gas := 7 + g, stack := ⟨Word.add x y :: xs, by simp; omega⟩ }
  let s2 : Frame.State := { s with pc := 2, gas := 2 + g, stack := ⟨z :: xs, by simp; omega⟩ }
  let s3 : Frame.State := { s with pc := 3, gas := g, stack := ⟨2 :: z :: xs, by simp; omega⟩ }
  let s4 : Frame.State := { s3 with pc := 4 }
  have h1 : Frame.Rule s (.continue s1) := by
    apply Frame.Rule.add s s1 x y xs
    · simp [Frame.At, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s]; omega
    · simp [Frame.Advances, s, s1]; omega
  have h2 : Frame.Rule s1 (.continue s2) := by
    apply Frame.Rule.clz s1 s2 (Word.add x y) xs
    · simp [Frame.At, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s1]; omega
    · simp [Frame.Advances, s1, s2, z]; omega
  have h3 : Frame.Rule s2 (.continue s3) := by
    apply Frame.Rule.observation s2 s3 .pc
    · simp [Frame.At, Frame.Observation.opcode, s2, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s2]
    · simp [s2]; omega
    · simp [Frame.Advances, Frame.Observation.value, s2, s3]
  have h4 : Frame.Rule s3 (.stop s4) := by
    apply Frame.Rule.stop
    simp [Frame.At, s3, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
  have trace : Runner.Terminates s 4 (.stopped s4) := .next h1 (.next h2 (.next h3 (.stop h4)))
  have result := Runner.run_of_terminates trace 0
  refine ⟨s4, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simpa [s] using result

end EthLib.EVM.Runner.CountLeadingZeros
