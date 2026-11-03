module

public import EthLib.EVM.Proofs.Frame.ExtCodeCopy
public import EthLib.EVM.Proofs.Runner

/-! A cold EXTCODEHASH, warm EXTCODECOPY and MLOAD program. -/

@[expose] public section
namespace EthLib.EVM.Runner.ExtCodeCopyProgram

/-- Query a hash, discard it, copy code, load memory, then stop. -/
def program : ByteArray := ⟨#[0x3f, 0x50, 0x3c, 0x51, 0x00]⟩

/-- The real runner executes the constructed mixed program for arbitrary supplied tracker and memory. -/
theorem run (xs : List Word) (room : xs.length ≤ 1018) (x destination source length : Word) (g : Nat)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem)
    (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State)
    (warm : List World.Address) (slots : List (World.Address × Word)) (static : Bool) (meter : Frame.StateGas)
    (cold : Frame.BalanceAddress x ∉ warm) (code : ByteArray)
    (present : Frame.ExtCodeBytes
      ⟨program, 0, ⟨x :: x :: destination :: source :: length :: destination :: xs, by simp; omega⟩,
        0, mem, valid, context, returnData, tracker, warm, slots, static, meter⟩ (Frame.BalanceAddress x) = some code) :
    let copied := Memory.Allocation.write (Memory.Allocation.expand mem destination.toNat length.toNat)
      destination.toNat (CallData.readRange code source.toNat length.toNat)
    let copyCost := 200 + 3 * ((length.toNat + 31) / 32) + Gas.rangeCost mem.words destination.toNat length.toNat
    let loadCost := 3 + Gas.rangeCost copied.words destination.toNat 32
    let s : Frame.State := ⟨program, 0, ⟨x :: x :: destination :: source :: length :: destination :: xs, by simp; omega⟩,
      3000 + 2 + copyCost + loadCost + g, mem, valid, context, returnData, tracker, warm, slots, static, meter⟩
    ∃ t, Runner.run 5 s = .stopped t ∧ t.pc = 5 ∧ t.gas = g ∧
      t.stack.val = (Memory.Allocation.loadWord copied destination.toNat).1 :: xs ∧
      t.tracker = { tracker with accountReads := Frame.BalanceAddress x :: Frame.BalanceAddress x :: tracker.accountReads } ∧
      t.warmAddresses = Frame.BalanceAddress x :: warm := by
  let a := Frame.BalanceAddress x
  let copied := Memory.Allocation.write (Memory.Allocation.expand mem destination.toNat length.toNat)
    destination.toNat (CallData.readRange code source.toNat length.toNat)
  let copyCost := 200 + 3 * ((length.toNat + 31) / 32) + Gas.rangeCost mem.words destination.toNat length.toNat
  let loadCost := 3 + Gas.rangeCost copied.words destination.toNat 32
  let s : Frame.State := ⟨program, 0, ⟨x :: x :: destination :: source :: length :: destination :: xs, by simp; omega⟩,
    3000 + 2 + copyCost + loadCost + g, mem, valid, context, returnData, tracker, warm, slots, static, meter⟩
  let s1 : Frame.State := { s with tracker := Frame.BalanceRead s a, warmAddresses := a :: warm, pc := 1, gas := 2 + copyCost + loadCost + g, stack := ⟨Frame.ExtCodeHashValue s a :: x :: destination :: source :: length :: destination :: xs, by simp; omega⟩ }
  let s2 : Frame.State := { s1 with pc := 2, gas := copyCost + loadCost + g, stack := ⟨x :: destination :: source :: length :: destination :: xs, by simp; omega⟩ }
  let copiedValid : Memory.Allocation.Valid copied := Memory.Allocation.write_valid_for_frame _ _ _ (Memory.Allocation.expand_valid_for_frame _ _ _ valid)
  let s3 : Frame.State := { s2 with tracker := Frame.BalanceRead s2 a, pc := 3, gas := loadCost + g, stack := ⟨destination :: xs, by simp; omega⟩, memory := copied, memoryValid := copiedValid }
  let s4 : Frame.State := { s3 with pc := 4, gas := g, stack := ⟨(Memory.Allocation.loadWord copied destination.toNat).1 :: xs, by simp; omega⟩, memory := (Memory.Allocation.loadWord copied destination.toNat).2, memoryValid := Memory.Allocation.expand_valid_for_frame _ _ _ copiedValid }
  let s5 : Frame.State := { s4 with pc := 5 }
  have r1 : Frame.Rule s (.continue s1) := by
    apply Frame.Rule.extCodeHash s s1 ⟨x :: destination :: source :: length :: destination :: xs, by simp; omega⟩ x
    · simp [Frame.At, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [Frame.BalanceCost, s, cold]; omega
    · simp [Frame.Advances, Frame.BalanceCost, Frame.BalanceWarm, s, s1, a, cold]; omega
  have r2 : Frame.Rule s1 (.continue s2) := by
    apply Frame.Rule.pop s1 s2 (Frame.ExtCodeHashValue s a) (x :: destination :: source :: length :: destination :: xs)
    · simp [Frame.At, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s1]; omega
    · simp [Frame.Advances, s1, s2]; omega
  have r3 : Frame.Rule s2 (.continue s3) := by
    apply Frame.Rule.extCodeCopy s2 s3 ⟨destination :: source :: length :: destination :: xs, by simp; omega⟩ ⟨source :: length :: destination :: xs, by simp; omega⟩ ⟨length :: destination :: xs, by simp; omega⟩ ⟨destination :: xs, by simp; omega⟩ x destination source length code
    · simp [Frame.At, s2, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · rfl
    · rfl
    · rfl
    · simp [Frame.ExtCodeCopyCost, Frame.ExtCodeSizeCost, Frame.BalanceCost, s2, s1, s, copyCost, a]; omega
    · exact present
    · simp [Frame.AdvancesMemory, Frame.ExtCodeCopyCost, Frame.ExtCodeSizeCost, Frame.BalanceCost,
        Frame.BalanceWarm, s3, s2, s1, s, copied, copyCost, a]; omega
  have r4 : Frame.Rule s3 (.continue s4) := by
    apply Frame.Rule.mload s3 s4 destination xs
    · simp [Frame.At, s3, s2, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s3, loadCost]
    · simp [Frame.AdvancesMemory, s4, s3, loadCost]
  have r5 : Frame.Rule s4 (.stop s5) := by
    apply Frame.Rule.stop
    simp [Frame.At, s4, s3, s2, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
  have trace : Runner.Terminates s 5 (.stopped s5) := .next r1 (.next r2 (.next r3 (.next r4 (.stop r5))))
  have result := Runner.run_of_terminates trace 0
  exact ⟨s5, by simpa [s] using result, rfl, rfl, rfl, rfl, rfl⟩

end EthLib.EVM.Runner.ExtCodeCopyProgram
