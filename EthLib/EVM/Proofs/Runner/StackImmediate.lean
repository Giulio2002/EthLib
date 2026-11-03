module

public import EthLib.EVM.Proofs.Runner

/-! A bounded program using all three Amsterdam immediate stack operations. -/

@[expose] public section
namespace EthLib.EVM.Runner.StackImmediate

/-- DUPN 17, SWAPN 17, EXCHANGE 2 3, STOP. -/
def program : ByteArray := ⟨#[0xe6, 0x80, 0xe7, 0x80, 0xe8, 0x9d, 0x00]⟩

/-- The program preserves the supplied context, memory, return data, and tail. -/
theorem run (a b c z : Word) (xs : List Word) (room : xs.length ≤ 1006)
    (g : Nat) (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem)
    (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State) (warmAddresses : List World.Address) (warmSlots : List (World.Address × Word)) :
    ∃ t, Runner.run 4 ⟨program, 0,
      ⟨a :: b :: c :: List.replicate 14 z ++ xs, by simp; omega⟩,
      9 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots⟩ = .stopped t ∧
      t.pc = 7 ∧ t.gas = g ∧ t.code = program ∧ t.memory = mem ∧
      t.context = context ∧ t.returnData = returnData ∧
      t.stack.val = z :: a :: c :: b :: List.replicate 14 z ++ xs := by
  let s : Frame.State := ⟨program, 0,
    ⟨a :: b :: c :: List.replicate 14 z ++ xs, by simp; omega⟩,
    9 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots⟩
  let s1 : Frame.State := { s with pc := 2, gas := 6 + g, stack := ⟨z :: a :: b :: c :: List.replicate 14 z ++ xs, by simp; omega⟩ }
  let s2 : Frame.State := { s1 with pc := 4, gas := 3 + g }
  let s3 : Frame.State := { s2 with pc := 6, gas := g, stack := ⟨z :: a :: c :: b :: List.replicate 14 z ++ xs, by simp; omega⟩ }
  let s4 : Frame.State := { s3 with pc := 7 }
  have h1 : Frame.step s = .continue s1 := by
    simp [Frame.step, s, s1, program, ByteArray.size, -ByteArray.size_data,
      ByteArray.getElem_eq_getElem_data, Opcode.decode, Frame.dupn, Frame.charge,
      Gas.charge, EthLib.EVM.StackImmediate.byte, PushImmediate.byteAt,
      EthLib.EVM.StackImmediate.decodeSingle, Stack.dupAt,
      List.replicate_succ, Nat.add_assoc, show 3 ≤ 9 + g by omega,
      show xs.length + 17 < 1024 by omega] <;> omega
  have h2 : Frame.step s1 = .continue s2 := by
    simp [Frame.step, s1, s2, s, program, ByteArray.size, -ByteArray.size_data,
      ByteArray.getElem_eq_getElem_data, Opcode.decode, Frame.swapn, Frame.charge,
      Gas.charge, EthLib.EVM.StackImmediate.byte, PushImmediate.byteAt,
      EthLib.EVM.StackImmediate.decodeSingle, Stack.exchangeAt,
      List.replicate_succ, show 3 ≤ 6 + g by omega] <;> omega
  have h3 : Frame.step s2 = .continue s3 := by
    simp [Frame.step, s2, s3, s1, s, program, ByteArray.size, -ByteArray.size_data,
      ByteArray.getElem_eq_getElem_data, Opcode.decode, Frame.exchange, Frame.charge,
      Gas.charge, EthLib.EVM.StackImmediate.byte, PushImmediate.byteAt,
      EthLib.EVM.StackImmediate.decodePair, Stack.exchangeAt,
      List.replicate_succ, show 3 ≤ 3 + g by omega] <;> omega
  have h4 : Frame.step s3 = .stop s4 := by
    simp [Frame.step, s3, s4, s2, s1, s, program, ByteArray.size,
      -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
  have trace : Runner.Terminates s 4 (.stopped s4) :=
    .next ((Frame.step_iff_rule _ _).mp h1)
      (.next ((Frame.step_iff_rule _ _).mp h2)
        (.next ((Frame.step_iff_rule _ _).mp h3) (.stop ((Frame.step_iff_rule _ _).mp h4))))
  have result := Runner.run_of_terminates trace 0
  refine ⟨s4, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simpa [s] using result

end EthLib.EVM.Runner.StackImmediate
