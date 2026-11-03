module

public import EthLib.EVM.Proofs.Runner
public import EthLib.EVM.Proofs.Frame.Memory

/-!
# Mixed input copy program

Cancun execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`,
`vm/instructions/environment.py`, `calldatacopy` and `returndatacopy`,
and `vm/instructions/memory.py`, `mload`.
-/

@[expose] public section
namespace EthLib.EVM.Runner.MixedCopy

/-- Copy calldata and return data, then load both destination words. -/
def program : ByteArray := ⟨#[0x37, 0x3e, 0x51, 0x90, 0x51]⟩

/-- The disjoint writes supply the words read by the two loads. -/
theorem copied_words (mem : Memory.Allocation.State) (a b : List UInt8)
    (ha : a.length = 32) (hb : b.length = 32) :
    let m1 := Memory.Allocation.write mem 0 a
    let m2 := Memory.Allocation.write m1 32 b
    let m3 := (Memory.Allocation.loadWord m2 0).2
    (Memory.Allocation.loadWord m2 0).1.toNat = EthLib.Execution.Precompiles.Modexp.bytesToNat a ∧
    (Memory.Allocation.loadWord m3 32).1.toNat = EthLib.Execution.Precompiles.Modexp.bytesToNat b := by
  dsimp only
  constructor
  · rw [Memory.Allocation.loadWord_numeric]
    change EthLib.Execution.Precompiles.Modexp.bytesToNat (Memory.readRange
      (Memory.writeRange (Memory.writeRange mem.store 0 a) 32 b) 0 32) = _
    rw [Memory.readRange_writeRange_disjoint _ 32 0 32 b (by omega)]
    rw [← ha, Memory.readRange_writeRange]
  · rw [Memory.Allocation.loadWord_numeric]
    change EthLib.Execution.Precompiles.Modexp.bytesToNat (Memory.readRange
      (Memory.writeRange (Memory.writeRange mem.store 0 a) 32 b) 32 32) = _
    rw [← hb, Memory.readRange_writeRange]

/-- Both destination ranges contain their source bytes and other bytes are preserved. -/
theorem copied_bytes (mem : Memory.Allocation.State) (a b : List UInt8)
    (ha : a.length = 32) (hb : b.length = 32) :
    let m := Memory.Allocation.write (Memory.Allocation.write mem 0 a) 32 b
    Memory.readRange m.store 0 32 = a ∧ Memory.readRange m.store 32 32 = b ∧
    (∀ i, 64 ≤ i → Memory.readByte m.store i = Memory.readByte mem.store i) := by
  dsimp only
  constructor
  · change Memory.readRange (Memory.writeRange (Memory.writeRange mem.store 0 a) 32 b) 0 32 = a
    rw [Memory.readRange_writeRange_disjoint _ 32 0 32 b (by omega), ← ha,
      Memory.readRange_writeRange]
  constructor
  · change Memory.readRange (Memory.writeRange (Memory.writeRange mem.store 0 a) 32 b) 32 32 = b
    rw [← hb, Memory.readRange_writeRange]
  · intro i hi
    change Memory.readByte (Memory.writeRange (Memory.writeRange mem.store 0 a) 32 b) i = _
    rw [Memory.writeRange_outside _ _ _ _ (by omega), Memory.writeRange_outside _ _ _ _ (by omega)]

/-- Execute both copies and loads from arbitrary valid initial memory. -/
theorem run_mixed (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State) (warmAddresses : List World.Address)
    (co ro : Word) (xs : List Word) (room : xs.length ≤ 1016)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem)
    (bounds : ro.toNat + 32 ≤ returnData.size) (g : Nat) :
    let a := CallData.readRange context.data co.toNat 32
    let b := (returnData.data.toList.drop ro.toNat).take 32
    let m1 := Memory.Allocation.write mem 0 a
    let m2 := Memory.Allocation.write m1 32 b
    let m3 := (Memory.Allocation.loadWord m2 0).2
    let m4 := (Memory.Allocation.loadWord m3 32).2
    let c1 := Gas.inputCopyCost mem.words 0 32
    let c2 := Gas.inputCopyCost m1.words 32 32
    let c3 := 3 + Gas.rangeCost m2.words 0 32
    let c4 := 3 + Gas.rangeCost m3.words 32 32
    ∃ t, run 5 ⟨program, 0, ⟨[0, co, 32, 32, ro, 32, 0, 32] ++ xs, by simp; omega⟩,
        c1 + c2 + c3 + 3 + c4 + g, mem, valid, context, returnData, tracker, warmAddresses⟩ = .exhausted t ∧
      t.stack.val = (Memory.Allocation.loadWord m3 32).1 :: (Memory.Allocation.loadWord m2 0).1 :: xs ∧
      t.pc = 5 ∧ t.gas = g ∧ t.memory = m4 ∧ t.memory.words = max mem.words 2 ∧ t.code = program ∧
      t.context = context ∧ t.returnData = returnData ∧
      (Memory.Allocation.loadWord m2 0).1.toNat = EthLib.Execution.Precompiles.Modexp.bytesToNat a ∧
      (Memory.Allocation.loadWord m3 32).1.toNat = EthLib.Execution.Precompiles.Modexp.bytesToNat b ∧
      Memory.readRange t.memory.store 0 32 = a ∧ Memory.readRange t.memory.store 32 32 = b ∧
      (∀ i, 64 ≤ i → Memory.readByte t.memory.store i = Memory.readByte mem.store i) := by
  dsimp only
  -- The two lists are the bytes written by the copy instructions.
  let a := CallData.readRange context.data co.toNat 32
  let b := (returnData.data.toList.drop ro.toNat).take 32
  let m1 := Memory.Allocation.write mem 0 a
  let m2 := Memory.Allocation.write m1 32 b
  let m3 := (Memory.Allocation.loadWord m2 0).2
  let m4 := (Memory.Allocation.loadWord m3 32).2
  let c1 := Gas.inputCopyCost mem.words 0 32
  let c2 := Gas.inputCopyCost m1.words 32 32
  let c3 := 3 + Gas.rangeCost m2.words 0 32
  let c4 := 3 + Gas.rangeCost m3.words 32 32
  let w1 := (Memory.Allocation.loadWord m2 0).1
  let w2 := (Memory.Allocation.loadWord m3 32).1
  let s : Frame.State := ⟨program, 0, ⟨[0, co, 32, 32, ro, 32, 0, 32] ++ xs, by simp; omega⟩, c1+c2+c3+3+c4+g, mem, valid, context, returnData, tracker, warmAddresses⟩
  let s1 : Frame.State := { s with pc := 1, gas := c2+c3+3+c4+g, stack := ⟨[32, ro, 32, 0, 32] ++ xs, by simp; omega⟩, memory := m1, memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ valid }
  let s2 : Frame.State := { s1 with pc := 2, gas := c3+3+c4+g, stack := ⟨[0, 32] ++ xs, by simp; omega⟩, memory := m2, memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ s1.memoryValid }
  let s3 : Frame.State := { s2 with pc := 3, gas := 3+c4+g, stack := ⟨w1 :: 32 :: xs, by simp; omega⟩, memory := m3, memoryValid := Memory.Allocation.expand_valid_for_frame _ _ _ s2.memoryValid }
  let s4 : Frame.State := { s3 with pc := 4, gas := c4+g, stack := ⟨32 :: w1 :: xs, by simp; omega⟩ }
  let s5 : Frame.State := { s4 with pc := 5, gas := g, stack := ⟨w2 :: w1 :: xs, by simp; omega⟩, memory := m4, memoryValid := Memory.Allocation.expand_valid_for_frame _ _ _ s4.memoryValid }
  -- Each intermediate frame follows from its corresponding instruction rule.
  have h1 : Frame.Rule s (.continue s1) := by
    apply Frame.Rule.inputCopy s s1 .calldata 0 co 32 ([32, ro, 32, 0, 32] ++ xs)
    · simp [Frame.At, Frame.InputSource.opcode, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s, c1]; omega
    · simp [Frame.AdvancesMemory, Frame.InputSource.bytes, s, s1, m1, a, c1]; omega
  have h2 : Frame.Rule s1 (.continue s2) := by
    apply Frame.Rule.returnDataCopy s1 s2 32 ro 32 ([0, 32] ++ xs)
    · simp [Frame.At, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s1, m1, c2]; omega
    · simpa [s1, s] using bounds
    · simp [Frame.AdvancesMemory, s1, s2, s, m1, m2, b, c2]; omega
  have h3 : Frame.Rule s2 (.continue s3) := by
    apply Frame.Rule.mload s2 s3 0 (32 :: xs)
    · simp [Frame.At, s2, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s2, m2, c3]; omega
    · simp [Frame.AdvancesMemory, s2, s3, m2, m3, w1, c3]; omega
  have h4 : Frame.Rule s3 (.continue s4) := by
    apply Frame.Rule.swap s3 s4 ⟨0, by decide⟩ (by simp [s3])
    · simp [Frame.At, s3, s2, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · simp [s3]; omega
    · simp [Frame.Advances, s3, s4]; omega
  have h5 : Frame.Rule s4 (.continue s5) := by
    apply Frame.Rule.mload s4 s5 32 (w1 :: xs)
    · simp [Frame.At, s4, s3, s2, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s4, s3, m3, c4]
    · simp [Frame.AdvancesMemory, s4, s5, s3, m3, m4, w2, c4]
  -- The trace determines the bounded runner result.
  have trace : Runner.Continues s 5 s5 := .next h1 (.next h2 (.next h3 (.next h4 (.next h5 (.nil s5)))))
  have result := (Runner.run_exhausted_iff 5 s s5).mpr trace
  -- The checked return-data range contains exactly 32 bytes.
  have read : ReturnData.read returnData ro.toNat 32 = .ok b := by
    simp [ReturnData.read, b, bounds]
  have lenA : a.length = 32 := by simp [a, Proofs.CallData.readRange_length]
  have lenB : b.length = 32 := ReturnData.read_ok_length _ _ _ _ read
  have words := copied_words mem a b lenA lenB
  have bytes := copied_bytes mem a b lenA lenB
  have allocation : s5.memory.words = max mem.words 2 := by
    simp [s5, m4, m3, m2, m1, Memory.Allocation.loadWord, Memory.Allocation.read,
      Memory.Allocation.write, Memory.Allocation.expand, Memory.Allocation.requiredWords,
      lenA, lenB, Nat.max_assoc]
  exact ⟨s5, by simpa [s, c1, c2, c3, c4, m1, m2, m3, a, b] using result,
    rfl, rfl, rfl, rfl, allocation, rfl, rfl, rfl, words.1, words.2, bytes.1, bytes.2.1, bytes.2.2⟩

end EthLib.EVM.Runner.MixedCopy
