module

public import EthLib.EVM.Proofs.Frame
public import EthLib.EVM.Proofs.Memory.WordAccess
public import EthLib.EVM.Proofs.CallData
public import EthLib.EVM.Proofs.ReturnData
import Aesop

/-!
# Memory instruction output contracts

Cancun execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`,
`vm/instructions/memory.py`, `mload`, `mstore`, and `mstore8`.
-/

@[expose] public section
namespace EthLib.EVM.Frame

open EthLib.EVM.Memory

/-- A successful load returns the selected bytes and the exact allocation and gas. -/
theorem mload_output (s t : State) (x : Word) (xs : List Word)
    (at_ : At s (some .mload)) (items : s.stack.val = x :: xs)
    (gas : 3 + Gas.rangeCost s.memory.words x.toNat 32 ≤ s.gas)
    (fields : AdvancesMemory s t (Memory.Allocation.loadWord s.memory x.toNat).2
      (s.pc + 1) (s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 32))
      ((Memory.Allocation.loadWord s.memory x.toNat).1 :: xs)) :
    step s = .continue t ∧ t.code = s.code ∧ t.pc = s.pc + 1 ∧
      t.gas = s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 32) ∧
      t.stack.val = (Memory.Allocation.loadWord s.memory x.toNat).1 :: xs ∧
      t.memory.store = s.memory.store ∧
      t.memory.words = max s.memory.words (Memory.Allocation.requiredWords x.toNat 32) ∧
      (Memory.Allocation.loadWord s.memory x.toNat).1.toNat =
        EthLib.Base.bytesToNat (readRange s.memory.store x.toNat 32) := by
  refine ⟨step_mload s t x xs at_ items gas fields, ?_⟩
  rcases fields with ⟨code, mem, pc, remaining, stack, context⟩
  refine ⟨code, pc, remaining, stack, ?_, ?_, Memory.Allocation.loadWord_numeric _ _⟩
  · rw [mem]; rfl
  · rw [mem]; rfl

/-- A successful word store changes only the selected 32 bytes. -/
theorem mstore_output (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .mstore)) (items : s.stack.val = x :: y :: xs)
    (gas : 3 + Gas.rangeCost s.memory.words x.toNat 32 ≤ s.gas)
    (fields : AdvancesMemory s t (Memory.Allocation.storeWord s.memory x.toNat y)
      (s.pc + 1) (s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 32)) xs) :
    step s = .continue t ∧ t.code = s.code ∧ t.pc = s.pc + 1 ∧
      t.gas = s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 32) ∧ t.stack.val = xs ∧
      t.memory.words = max s.memory.words (Memory.Allocation.requiredWords x.toNat 32) ∧
      (∀ a, ¬ (x.toNat ≤ a ∧ a < x.toNat + 32) →
        readByte t.memory.store a = readByte s.memory.store a) ∧
      (∀ i, i < 32 → readByte t.memory.store (x.toNat + i) =
        UInt8.ofNat ((y.toNat / 256 ^ (31 - i)) % 256)) := by
  refine ⟨step_mstore s t x y xs at_ items gas fields, ?_⟩
  rcases fields with ⟨code, mem, pc, remaining, stack, context⟩
  refine ⟨code, pc, remaining, stack, ?_, ?_, ?_⟩
  · rw [mem]; exact Memory.Allocation.storeWord_words _ _ _
  · intro a outside; rw [mem]; exact Memory.Allocation.storeWord_outside _ _ _ _ outside
  · intro i hi; rw [mem]; exact Memory.Allocation.storeWord_byte _ _ _ _ hi

/-- A successful byte store writes the low byte and leaves other addresses unchanged. -/
theorem mstore8_output (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .mstore8)) (items : s.stack.val = x :: y :: xs)
    (gas : 3 + Gas.rangeCost s.memory.words x.toNat 1 ≤ s.gas)
    (fields : AdvancesMemory s t (Memory.Allocation.storeByte s.memory x.toNat y)
      (s.pc + 1) (s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 1)) xs) :
    step s = .continue t ∧ t.code = s.code ∧ t.pc = s.pc + 1 ∧
      t.gas = s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 1) ∧ t.stack.val = xs ∧
      t.memory.words = max s.memory.words (Memory.Allocation.requiredWords x.toNat 1) ∧
      (readByte t.memory.store x.toNat).toNat = y.toNat % 256 ∧
      (∀ a, a ≠ x.toNat → readByte t.memory.store a = readByte s.memory.store a) := by
  refine ⟨step_mstore8 s t x y xs at_ items gas fields, ?_⟩
  rcases fields with ⟨code, mem, pc, remaining, stack, context⟩
  refine ⟨code, pc, remaining, stack, ?_, ?_, ?_⟩
  · rw [mem]; exact Memory.Allocation.storeByte_words _ _ _
  · rw [mem]; exact Memory.Allocation.storeByte_value _ _ _
  · intro a outside; rw [mem]; exact Memory.Allocation.storeByte_outside _ _ _ _ outside

/-- A continuing MLOAD determines gas and every updated field. -/
theorem mload_success_fields (s t : State) (x : Word) (xs : List Word)
    (at_ : At s (some .mload)) (items : s.stack.val = x :: xs)
    (run : step s = .continue t) :
    3 + Gas.rangeCost s.memory.words x.toNat 32 ≤ s.gas ∧
      AdvancesMemory s t (Memory.Allocation.loadWord s.memory x.toNat).2
        (s.pc + 1) (s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 32)) ((Memory.Allocation.loadWord s.memory x.toNat).1 :: xs) := by
  have gas : 3 + Gas.rangeCost s.memory.words x.toNat 32 ≤ s.gas := by
    by_contra low
    have failure := step_mload_gas s x xs at_ items (Nat.lt_of_not_ge low)
    rw [run] at failure
    cases failure
  let stack : Stack := ⟨((Memory.Allocation.loadWord s.memory x.toNat).1 :: xs), by
    have bound := s.stack.property
    rw [items] at bound
    simp at bound ⊢
    omega⟩
  let target : State := { s with stack, pc := s.pc + 1, gas := s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 32), memory := (Memory.Allocation.loadWord s.memory x.toNat).2, memoryValid := Memory.Allocation.expand_valid_for_frame _ _ _ s.memoryValid }
  have fields : AdvancesMemory s target (Memory.Allocation.loadWord s.memory x.toNat).2
      (s.pc + 1) (s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 32)) ((Memory.Allocation.loadWord s.memory x.toNat).1 :: xs) := by
    simp [AdvancesMemory, target, stack]
  have success := step_mload s target x xs at_ items gas fields
  rw [run] at success
  have eq : t = target := Outcome.continue.inj success
  subst t
  exact ⟨gas, fields⟩

/-- A continuing MSTORE determines gas and every updated field. -/
theorem mstore_success_fields (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .mstore)) (items : s.stack.val = x :: y :: xs)
    (run : step s = .continue t) :
    3 + Gas.rangeCost s.memory.words x.toNat 32 ≤ s.gas ∧
      AdvancesMemory s t (Memory.Allocation.storeWord s.memory x.toNat y)
        (s.pc + 1) (s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 32)) xs := by
  have gas : 3 + Gas.rangeCost s.memory.words x.toNat 32 ≤ s.gas := by
    by_contra low
    have failure := step_mstore_gas s x y xs at_ items (Nat.lt_of_not_ge low)
    rw [run] at failure
    cases failure
  let stack : Stack := ⟨xs, by
    have bound := s.stack.property
    rw [items] at bound
    simp at bound ⊢
    omega⟩
  let target : State := { s with stack, pc := s.pc + 1, gas := s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 32), memory := (Memory.Allocation.storeWord s.memory x.toNat y), memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid }
  have fields : AdvancesMemory s target (Memory.Allocation.storeWord s.memory x.toNat y)
      (s.pc + 1) (s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 32)) xs := by
    simp [AdvancesMemory, target, stack]
  have success := step_mstore s target x y xs at_ items gas fields
  rw [run] at success
  have eq : t = target := Outcome.continue.inj success
  subst t
  exact ⟨gas, fields⟩

/-- A continuing MSTORE8 determines gas and every updated field. -/
theorem mstore8_success_fields (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .mstore8)) (items : s.stack.val = x :: y :: xs)
    (run : step s = .continue t) :
    3 + Gas.rangeCost s.memory.words x.toNat 1 ≤ s.gas ∧
      AdvancesMemory s t (Memory.Allocation.storeByte s.memory x.toNat y)
        (s.pc + 1) (s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 1)) xs := by
  have gas : 3 + Gas.rangeCost s.memory.words x.toNat 1 ≤ s.gas := by
    by_contra low
    have failure := step_mstore8_gas s x y xs at_ items (Nat.lt_of_not_ge low)
    rw [run] at failure
    cases failure
  let stack : Stack := ⟨xs, by
    have bound := s.stack.property
    rw [items] at bound
    simp at bound ⊢
    omega⟩
  let target : State := { s with stack, pc := s.pc + 1, gas := s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 1), memory := (Memory.Allocation.storeByte s.memory x.toNat y), memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid }
  have fields : AdvancesMemory s target (Memory.Allocation.storeByte s.memory x.toNat y)
      (s.pc + 1) (s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 1)) xs := by
    simp [AdvancesMemory, target, stack]
  have success := step_mstore8 s target x y xs at_ items gas fields
  rw [run] at success
  have eq : t = target := Outcome.continue.inj success
  subst t
  exact ⟨gas, fields⟩

/-- An observed successful MLOAD determines its output observations. -/
theorem mload_success_output (s t : State) (x : Word) (xs : List Word)
    (at_ : At s (some .mload)) (items : s.stack.val = x :: xs)
    (run : step s = .continue t) :
    step s = .continue t ∧ t.code = s.code ∧ t.pc = s.pc + 1 ∧
      t.gas = s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 32) ∧
      t.stack.val = (Memory.Allocation.loadWord s.memory x.toNat).1 :: xs ∧
      t.memory.store = s.memory.store ∧
      t.memory.words = max s.memory.words (Memory.Allocation.requiredWords x.toNat 32) ∧
      (Memory.Allocation.loadWord s.memory x.toNat).1.toNat =
        EthLib.Base.bytesToNat (readRange s.memory.store x.toNat 32) := by
  obtain ⟨gas, fields⟩ := mload_success_fields s t x xs at_ items run
  exact mload_output s t x xs at_ items gas fields

/-- An observed successful MSTORE determines its output observations. -/
theorem mstore_success_output (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .mstore)) (items : s.stack.val = x :: y :: xs)
    (run : step s = .continue t) :
    step s = .continue t ∧ t.code = s.code ∧ t.pc = s.pc + 1 ∧
      t.gas = s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 32) ∧ t.stack.val = xs ∧
      t.memory.words = max s.memory.words (Memory.Allocation.requiredWords x.toNat 32) ∧
      (∀ a, ¬ (x.toNat ≤ a ∧ a < x.toNat + 32) →
        readByte t.memory.store a = readByte s.memory.store a) ∧
      (∀ i, i < 32 → readByte t.memory.store (x.toNat + i) =
        UInt8.ofNat ((y.toNat / 256 ^ (31 - i)) % 256)) := by
  obtain ⟨gas, fields⟩ := mstore_success_fields s t x y xs at_ items run
  exact mstore_output s t x y xs at_ items gas fields

/-- An observed successful MSTORE8 determines its output observations. -/
theorem mstore8_success_output (s t : State) (x y : Word) (xs : List Word)
    (at_ : At s (some .mstore8)) (items : s.stack.val = x :: y :: xs)
    (run : step s = .continue t) :
    step s = .continue t ∧ t.code = s.code ∧ t.pc = s.pc + 1 ∧
      t.gas = s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 1) ∧ t.stack.val = xs ∧
      t.memory.words = max s.memory.words (Memory.Allocation.requiredWords x.toNat 1) ∧
      (readByte t.memory.store x.toNat).toNat = y.toNat % 256 ∧
      (∀ a, a ≠ x.toNat → readByte t.memory.store a = readByte s.memory.store a) := by
  obtain ⟨gas, fields⟩ := mstore8_success_fields s t x y xs at_ items run
  exact mstore8_output s t x y xs at_ items gas fields

/-- A continuing return-data copy exposes every copied and untouched byte. -/
theorem returnDataCopy_helper_actual_output (s t : State) (x y z : Word) (xs : List Word)
    (items : s.stack.val = x :: y :: z :: xs)
    (run : returnDataCopy s = .continue t) :
    ∃ hbound : y.toNat + z.toNat ≤ s.returnData.size,
    Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas ∧
    t.code = s.code ∧ t.context = s.context ∧ t.returnData = s.returnData ∧
    t.pc = s.pc + 1 ∧ t.gas = s.gas - Gas.inputCopyCost s.memory.words x.toNat z.toNat ∧
    t.stack.val = xs ∧
    t.memory.words = max s.memory.words (Memory.Allocation.requiredWords x.toNat z.toNat) ∧
    (∀ i, (hi : i < z.toNat) → readByte t.memory.store (x.toNat + i) =
      s.returnData[y.toNat + i]'(by omega)) ∧
    (∀ a, ¬ (x.toNat ≤ a ∧ a < x.toNat + z.toNat) →
      readByte t.memory.store a = readByte s.memory.store a) := by
  obtain ⟨gas, bound, code, mem, pc, remaining, stack, context, ret, _tracker, _warm, _slots⟩ :=
    returnDataCopy_helper_actual s t x y z xs items run
  let bytes := (s.returnData.data.toList.drop y.toNat).take z.toNat
  have read : ReturnData.read s.returnData y.toNat z.toNat = .ok bytes := by
    simp [ReturnData.read, bound, bytes]
  have len : bytes.length = z.toNat := ReturnData.read_ok_length _ _ _ _ read
  change t.memory = Memory.Allocation.write s.memory x.toNat bytes at mem
  refine ⟨bound, gas, code, context, ret, pc, remaining, stack, ?_, ?_, ?_⟩
  · rw [mem]
    simp [Memory.Allocation.write, Memory.Allocation.expand, len]
  · intro i hi
    rw [mem, Memory.Allocation.write_observe]
    simp only [len]
    simp only [show x.toNat ≤ x.toNat + i ∧ x.toNat + i < x.toNat + z.toNat by omega,
      Nat.add_sub_cancel_left]
    exact ReturnData.read_ok_index _ _ _ _ read i hi
  · intro a outside
    rw [mem, Memory.Allocation.write_observe]
    simp [len, outside]

/-- A continuing return-data copy exposes every copied and untouched byte. -/
theorem returnDataCopy_actual_output (s t : State) (x y z : Word) (xs : List Word)
    (at_ : At s (some .returndatacopy)) (items : s.stack.val = x :: y :: z :: xs)
    (run : step s = .continue t) :
    ∃ hbound : y.toNat + z.toNat ≤ s.returnData.size,
    Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas ∧
    t.code = s.code ∧ t.context = s.context ∧ t.returnData = s.returnData ∧
    t.pc = s.pc + 1 ∧ t.gas = s.gas - Gas.inputCopyCost s.memory.words x.toNat z.toNat ∧
    t.stack.val = xs ∧
    t.memory.words = max s.memory.words (Memory.Allocation.requiredWords x.toNat z.toNat) ∧
    (∀ i, (hi : i < z.toNat) → readByte t.memory.store (x.toNat + i) =
      s.returnData[y.toNat + i]'(by omega)) ∧
    (∀ a, ¬ (x.toNat ≤ a ∧ a < x.toNat + z.toNat) →
      readByte t.memory.store a = readByte s.memory.store a) := by
  obtain ⟨gas, bound, code, mem, pc, remaining, stack, context, ret, _tracker, _warm, _slots⟩ :=
    returnDataCopy_actual s t x y z xs at_ items run
  let bytes := (s.returnData.data.toList.drop y.toNat).take z.toNat
  have read : ReturnData.read s.returnData y.toNat z.toNat = .ok bytes := by
    simp [ReturnData.read, bound, bytes]
  have len : bytes.length = z.toNat := ReturnData.read_ok_length _ _ _ _ read
  change t.memory = Memory.Allocation.write s.memory x.toNat bytes at mem
  refine ⟨bound, gas, code, context, ret, pc, remaining, stack, ?_, ?_, ?_⟩
  · rw [mem]
    simp [Memory.Allocation.write, Memory.Allocation.expand, len]
  · intro i hi
    rw [mem, Memory.Allocation.write_observe]
    simp only [len]
    simp only [show x.toNat ≤ x.toNat + i ∧ x.toNat + i < x.toNat + z.toNat by omega,
      Nat.add_sub_cancel_left]
    exact ReturnData.read_ok_index _ _ _ _ read i hi
  · intro a outside
    rw [mem, Memory.Allocation.write_observe]
    simp [len, outside]

/-- A successful input copy determines its gas and every updated field. -/
theorem inputCopy_helper_success_fields (s t : State) (data : ByteArray) (x y z : Word) (xs : List Word)
    (items : s.stack.val = x :: y :: z :: xs)
    (run : inputCopy s data = .continue t) :
    Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas ∧
      AdvancesMemory s t (Memory.Allocation.write s.memory x.toNat (CallData.readRange data y.toNat z.toNat))
        (s.pc + 1) (s.gas - Gas.inputCopyCost s.memory.words x.toNat z.toNat) xs := by
  have gas : Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas := by
    by_contra low
    have failure := inputCopy_helper_gas s data x y z xs items (Nat.lt_of_not_ge low)
    rw [run] at failure
    cases failure
  let stack : Stack := ⟨xs, by
    have bound := s.stack.property
    rw [items] at bound
    simp at bound ⊢
    omega⟩
  let target : State := { s with stack, pc := s.pc + 1, gas := s.gas - Gas.inputCopyCost s.memory.words x.toNat z.toNat, memory := Memory.Allocation.write s.memory x.toNat (CallData.readRange data y.toNat z.toNat), memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid }
  have fields : AdvancesMemory s target (Memory.Allocation.write s.memory x.toNat (CallData.readRange data y.toNat z.toNat))
      (s.pc + 1) (s.gas - Gas.inputCopyCost s.memory.words x.toNat z.toNat) xs := by
    simp [AdvancesMemory, target, stack]
  have success := inputCopy_helper_success s target data x y z xs items gas fields
  rw [run] at success
  have eq : t = target := Outcome.continue.inj success
  subst t
  exact ⟨gas, fields⟩

/-- A continuing input copy determines all fields and every destination byte. -/
theorem inputCopy_helper_success_output (s t : State) (data : ByteArray)
    (x y z : Word) (xs : List Word)
    (items : s.stack.val = x :: y :: z :: xs) (run : inputCopy s data = .continue t) :
    t.code = s.code ∧ t.context = s.context ∧ t.pc = s.pc + 1 ∧
    t.gas = s.gas - Gas.inputCopyCost s.memory.words x.toNat z.toNat ∧
    t.stack.val = xs ∧
    t.memory.words = max s.memory.words (Memory.Allocation.requiredWords x.toNat z.toNat) ∧
    (∀ i, i < z.toNat → readByte t.memory.store (x.toNat + i) =
      PushImmediate.byteAt data (y.toNat + i)) ∧
    (∀ a, ¬ (x.toNat ≤ a ∧ a < x.toNat + z.toNat) →
      readByte t.memory.store a = readByte s.memory.store a) := by
  obtain ⟨_, code, mem, pc, gas, stack, context⟩ :=
    inputCopy_helper_success_fields s t data x y z xs items run
  refine ⟨code, context.1, pc, gas, stack, ?_, ?_, ?_⟩
  · rw [mem]
    simp [Memory.Allocation.write, Memory.Allocation.expand, Proofs.CallData.readRange_length]
  · intro i hi
    rw [mem, Memory.Allocation.write_observe]
    simp [Proofs.CallData.readRange_length, hi, Proofs.CallData.readRange_get]
  · intro a outside
    rw [mem, Memory.Allocation.write_observe]
    simp [Proofs.CallData.readRange_length, outside]

/-- A successful input copy determines its gas and every updated field. -/
theorem inputCopy_success_fields (s t : State) (source : InputSource) (x y z : Word) (xs : List Word)
    (at_ : At s (some source.opcode)) (items : s.stack.val = x :: y :: z :: xs)
    (run : step s = .continue t) :
    Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas ∧
      AdvancesMemory s t (Memory.Allocation.write s.memory x.toNat (CallData.readRange (source.bytes s) y.toNat z.toNat))
        (s.pc + 1) (s.gas - Gas.inputCopyCost s.memory.words x.toNat z.toNat) xs := by
  rw [step_inputCopy_dispatch s source at_] at run
  exact inputCopy_helper_success_fields s t (source.bytes s) x y z xs items run

/-- A continuing input copy determines all fields and every destination byte. -/
theorem inputCopy_success_output (s t : State) (source : InputSource)
    (x y z : Word) (xs : List Word) (at_ : At s (some source.opcode))
    (items : s.stack.val = x :: y :: z :: xs) (run : step s = .continue t) :
    t.code = s.code ∧ t.context = s.context ∧ t.pc = s.pc + 1 ∧
    t.gas = s.gas - Gas.inputCopyCost s.memory.words x.toNat z.toNat ∧
    t.stack.val = xs ∧
    t.memory.words = max s.memory.words (Memory.Allocation.requiredWords x.toNat z.toNat) ∧
    (∀ i, i < z.toNat → readByte t.memory.store (x.toNat + i) =
      PushImmediate.byteAt (source.bytes s) (y.toNat + i)) ∧
    (∀ a, ¬ (x.toNat ≤ a ∧ a < x.toNat + z.toNat) →
      readByte t.memory.store a = readByte s.memory.store a) := by
  rw [step_inputCopy_dispatch s source at_] at run
  exact inputCopy_helper_success_output s t (source.bytes s) x y z xs items run

/-- A successful 32-byte copy followed by MLOAD exposes the source bytes. -/
theorem inputCopy_then_mload_actual (s t u : State) (source : InputSource)
    (x y : Word) (xs : List Word)
    (copyAt : At s (some source.opcode))
    (items : s.stack.val = x :: y :: (32 : Word) :: x :: xs)
    (copyRun : step s = .continue t) (loadAt : At t (some .mload))
    (loadRun : step t = .continue u) :
    ∃ w, u.stack.val = w :: xs ∧
      w.toNat = EthLib.Base.bytesToNat
        (CallData.readRange (source.bytes s) y.toNat 32) := by
  have copied := inputCopy_success_output s t source x y (32 : Word) (x :: xs)
    copyAt items copyRun
  have stack : t.stack.val = x :: xs := copied.2.2.2.2.1
  have loaded := mload_success_output t u x xs loadAt stack loadRun
  have bytes : readRange t.memory.store x.toNat 32 =
      CallData.readRange (source.bytes s) y.toNat 32 := by
    apply List.ext_getElem
    · simp [Memory.readRange_length, Proofs.CallData.readRange_length]
    · intro i hi hj
      have bound : i < 32 := by simpa [Memory.readRange_length] using hi
      rw [Memory.readRange_getElem _ _ _ _ bound,
        Proofs.CallData.readRange_get _ _ _ _ bound]
      exact copied.2.2.2.2.2.2.1 i (by simpa using bound)
  refine ⟨(Memory.Allocation.loadWord t.memory x.toNat).1, loaded.2.2.2.2.1, ?_⟩
  rw [loaded.2.2.2.2.2.2.2, bytes]

/-- A copy followed by MLOAD executes and exposes the selected 32 source bytes. -/
theorem inputCopy_then_mload_program (s : State) (source : InputSource)
    (x y : Word) (xs : List Word) (copyAt : At s (some source.opcode))
    (next : ∃ h : s.pc + 1 < s.code.size, Opcode.decode s.code[s.pc + 1] = some .mload)
    (items : s.stack.val = x :: y :: (32 : Word) :: x :: xs)
    (gas : Gas.inputCopyCost s.memory.words x.toNat 32 +
      (3 + Gas.rangeCost (max s.memory.words (Memory.Allocation.requiredWords x.toNat 32))
        x.toNat 32) ≤ s.gas) :
    ∃ t u w, step s = .continue t ∧ step t = .continue u ∧ u.stack.val = w :: xs ∧
      w.toNat = EthLib.Base.bytesToNat
        (CallData.readRange (source.bytes s) y.toNat 32) := by
  let stack : Stack := ⟨x :: xs, by
    have bound := s.stack.property
    rw [items] at bound
    simp at bound ⊢
    omega⟩
  let memory := Memory.Allocation.write s.memory x.toNat (CallData.readRange (source.bytes s) y.toNat 32)
  let t : State := { s with stack, pc := s.pc + 1, gas := s.gas - Gas.inputCopyCost s.memory.words x.toNat 32, memory, memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid }
  have copyGas : Gas.inputCopyCost s.memory.words x.toNat (32 : Word).toNat ≤ s.gas := by
    change Gas.inputCopyCost s.memory.words x.toNat 32 ≤ s.gas
    omega
  have copyFields : AdvancesMemory s t
      (Memory.Allocation.write s.memory x.toNat (CallData.readRange (source.bytes s) y.toNat (32 : Word).toNat))
      (s.pc + 1) (s.gas - Gas.inputCopyCost s.memory.words x.toNat (32 : Word).toNat) (x :: xs) := by
    simp [AdvancesMemory, t, stack, memory]
  have copyRun := step_inputCopy s t source x y 32 (x :: xs) copyAt items copyGas copyFields
  have loadAt : At t (some .mload) := by simpa [At, t] using next
  have loadItems : t.stack.val = x :: xs := rfl
  have loadGas : 3 + Gas.rangeCost t.memory.words x.toNat 32 ≤ t.gas := by
    simp [t, memory, Memory.Allocation.write, Memory.Allocation.expand,
      Proofs.CallData.readRange_length] at *
    omega
  let outStack : Stack := ⟨(Memory.Allocation.loadWord t.memory x.toNat).1 :: xs, by
    have bound := stack.property
    simp [stack] at bound ⊢
    omega⟩
  let u : State := { t with stack := outStack, pc := t.pc + 1, gas := t.gas - (3 + Gas.rangeCost t.memory.words x.toNat 32), memory := (Memory.Allocation.loadWord t.memory x.toNat).2, memoryValid := Memory.Allocation.expand_valid_for_frame _ _ _ t.memoryValid }
  have fields : AdvancesMemory t u (Memory.Allocation.loadWord t.memory x.toNat).2
      (t.pc + 1) (t.gas - (3 + Gas.rangeCost t.memory.words x.toNat 32))
      ((Memory.Allocation.loadWord t.memory x.toNat).1 :: xs) := by
    simp [AdvancesMemory, u, outStack]
  have loadRun := step_mload t u x xs loadAt loadItems loadGas fields
  obtain ⟨w, result⟩ := inputCopy_then_mload_actual s t u source x y xs copyAt items copyRun loadAt loadRun
  exact ⟨t, u, w, copyRun, loadRun, result⟩

/-- A valid return-data copy followed by MLOAD exposes the 32 source bytes. -/
theorem returnDataCopy_then_mload_actual (s t u : State) (x y : Word) (xs : List Word)
    (copyAt : At s (some .returndatacopy))
    (items : s.stack.val = x :: y :: (32 : Word) :: x :: xs)
    (copyRun : step s = .continue t) (loadAt : At t (some .mload))
    (loadRun : step t = .continue u) :
    ∃ w, u.stack.val = w :: xs ∧ w.toNat = EthLib.Base.bytesToNat
      ((s.returnData.data.toList.drop y.toNat).take 32) := by
  obtain ⟨_, bound, _, mem, _, _, stack, _, _⟩ :=
    returnDataCopy_actual s t x y 32 (x :: xs) copyAt items copyRun
  have loaded := mload_success_output t u x xs loadAt stack loadRun
  let bytes := (s.returnData.data.toList.drop y.toNat).take 32
  have read : ReturnData.read s.returnData y.toNat 32 = .ok bytes := by
    simp [ReturnData.read, bytes] at bound ⊢
    exact bound
  have len : bytes.length = 32 := ReturnData.read_ok_length _ _ _ _ read
  have memoryBytes : readRange t.memory.store x.toNat 32 = bytes := by
    rw [mem]
    change readRange (writeRange s.memory.store x.toNat bytes) x.toNat 32 = bytes
    rw [← len]
    exact readRange_writeRange _ _ _
  refine ⟨(Memory.Allocation.loadWord t.memory x.toNat).1, loaded.2.2.2.2.1, ?_⟩
  rw [loaded.2.2.2.2.2.2.2, memoryBytes]

/-- Sufficient gas and valid source bounds execute a return-data copy and MLOAD. -/
theorem returnDataCopy_then_mload_program (s : State) (x y : Word) (xs : List Word)
    (copyAt : At s (some .returndatacopy))
    (next : ∃ h : s.pc + 1 < s.code.size, Opcode.decode s.code[s.pc + 1] = some .mload)
    (items : s.stack.val = x :: y :: (32 : Word) :: x :: xs)
    (bound : y.toNat + 32 ≤ s.returnData.size)
    (gas : Gas.inputCopyCost s.memory.words x.toNat 32 +
      (3 + Gas.rangeCost (max s.memory.words (Memory.Allocation.requiredWords x.toNat 32)) x.toNat 32) ≤ s.gas) :
    ∃ t u w, step s = .continue t ∧ step t = .continue u ∧ u.stack.val = w :: xs ∧
      w.toNat = EthLib.Base.bytesToNat ((s.returnData.data.toList.drop y.toNat).take 32) := by
  let stack : Stack := ⟨x :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let bytes := (s.returnData.data.toList.drop y.toNat).take 32
  have read : ReturnData.read s.returnData y.toNat 32 = .ok bytes := by simp [ReturnData.read, bytes, bound]
  have len : bytes.length = 32 := ReturnData.read_ok_length _ _ _ _ read
  let memory := Memory.Allocation.write s.memory x.toNat bytes
  let t : State := { s with stack, pc := s.pc + 1, gas := s.gas - Gas.inputCopyCost s.memory.words x.toNat 32, memory, memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid }
  have copyGas : Gas.inputCopyCost s.memory.words x.toNat (32 : Word).toNat ≤ s.gas := by
    change Gas.inputCopyCost s.memory.words x.toNat 32 ≤ s.gas
    omega
  have copyBound : y.toNat + (32 : Word).toNat ≤ s.returnData.size := by simpa using bound
  have copyFields : AdvancesMemory s t (Memory.Allocation.write s.memory x.toNat
      ((s.returnData.data.toList.drop y.toNat).take (32 : Word).toNat))
      (s.pc + 1) (s.gas - Gas.inputCopyCost s.memory.words x.toNat (32 : Word).toNat) (x :: xs) := by
    simp [AdvancesMemory, t, stack, memory, bytes]
  have copyRun : step s = .continue t := rule_sound (.returnDataCopy s t x y 32 (x :: xs) copyAt items copyGas copyBound copyFields)
  have loadAt : At t (some .mload) := by simpa [At, t] using next
  have loadItems : t.stack.val = x :: xs := rfl
  have loadGas : 3 + Gas.rangeCost t.memory.words x.toNat 32 ≤ t.gas := by
    simp [t, memory, Memory.Allocation.write, Memory.Allocation.expand, len] at *
    omega
  let outStack : Stack := ⟨(Memory.Allocation.loadWord t.memory x.toNat).1 :: xs, by
    have b := stack.property; simp [stack] at b ⊢; omega⟩
  let u : State := { t with stack := outStack, pc := t.pc + 1, gas := t.gas - (3 + Gas.rangeCost t.memory.words x.toNat 32), memory := (Memory.Allocation.loadWord t.memory x.toNat).2, memoryValid := Memory.Allocation.expand_valid_for_frame _ _ _ t.memoryValid }
  have fields : AdvancesMemory t u (Memory.Allocation.loadWord t.memory x.toNat).2
      (t.pc + 1) (t.gas - (3 + Gas.rangeCost t.memory.words x.toNat 32))
      ((Memory.Allocation.loadWord t.memory x.toNat).1 :: xs) := by simp [AdvancesMemory, u, outStack]
  have loadRun := step_mload t u x xs loadAt loadItems loadGas fields
  obtain ⟨w, result⟩ := returnDataCopy_then_mload_actual s t u x y xs copyAt items copyRun loadAt loadRun
  exact ⟨t, u, w, copyRun, loadRun, result⟩

/-- A successful MCOPY determines its gas and every updated field. -/
theorem mcopy_success_fields (s t : State) (x y z : Word) (xs : List Word)
    (at_ : At s (some .mcopy)) (items : s.stack.val = x :: y :: z :: xs)
    (run : step s = .continue t) :
    Gas.mcopyCost s.memory.words x.toNat y.toNat z.toNat ≤ s.gas ∧
      AdvancesMemory s t (Memory.Allocation.copy s.memory x.toNat y.toNat z.toNat)
        (s.pc + 1) (s.gas - Gas.mcopyCost s.memory.words x.toNat y.toNat z.toNat) xs := by
  have gas : Gas.mcopyCost s.memory.words x.toNat y.toNat z.toNat ≤ s.gas := by
    by_contra low
    have failure := step_mcopy_gas s x y z xs at_ items (Nat.lt_of_not_ge low)
    rw [run] at failure
    cases failure
  let stack : Stack := ⟨xs, by
    have bound := s.stack.property
    rw [items] at bound
    simp at bound ⊢
    omega⟩
  let target : State := { s with stack, pc := s.pc + 1, gas := s.gas - Gas.mcopyCost s.memory.words x.toNat y.toNat z.toNat, memory := Memory.Allocation.copy s.memory x.toNat y.toNat z.toNat, memoryValid := Memory.Allocation.copy_valid_for_frame _ _ _ _ s.memoryValid }
  have fields : AdvancesMemory s target (Memory.Allocation.copy s.memory x.toNat y.toNat z.toNat)
      (s.pc + 1) (s.gas - Gas.mcopyCost s.memory.words x.toNat y.toNat z.toNat) xs := by
    simp [AdvancesMemory, target, stack]
  have success := step_mcopy s target x y z xs at_ items gas fields
  rw [run] at success
  have eq : t = target := Outcome.continue.inj success
  subst t
  exact ⟨gas, fields⟩

/-- A continuing MCOPY exposes the input snapshot at every destination byte. -/
theorem mcopy_success_output (s t : State) (x y z : Word) (xs : List Word)
    (at_ : At s (some .mcopy)) (items : s.stack.val = x :: y :: z :: xs)
    (run : step s = .continue t) :
    t.code = s.code ∧ t.pc = s.pc + 1 ∧
    t.gas = s.gas - Gas.mcopyCost s.memory.words x.toNat y.toNat z.toNat ∧
    t.stack.val = xs ∧
    t.memory.words = max (max s.memory.words (Memory.Allocation.requiredWords y.toNat z.toNat))
      (Memory.Allocation.requiredWords x.toNat z.toNat) ∧
    (∀ i, i < z.toNat → readByte t.memory.store (x.toNat + i) =
      readByte s.memory.store (y.toNat + i)) ∧
    (∀ a, ¬ (x.toNat ≤ a ∧ a < x.toNat + z.toNat) →
      readByte t.memory.store a = readByte s.memory.store a) := by
  obtain ⟨_, code, mem, pc, gas, stack, context⟩ := mcopy_success_fields s t x y z xs at_ items run
  refine ⟨code, pc, gas, stack, ?_, ?_, ?_⟩
  · rw [mem]; rfl
  · intro i hi
    rw [mem, Memory.Allocation.copy_observe]
    simp [show x.toNat ≤ x.toNat + i ∧ x.toNat + i < x.toNat + z.toNat by omega]
  · intro a outside
    rw [mem, Memory.Allocation.copy_observe]
    simp [outside]

/-- The forward rule yields the exact snapshot observations. -/
theorem mcopy_output (s t : State) (x y z : Word) (xs : List Word)
    (at_ : At s (some .mcopy)) (items : s.stack.val = x :: y :: z :: xs)
    (gas : Gas.mcopyCost s.memory.words x.toNat y.toNat z.toNat ≤ s.gas)
    (fields : AdvancesMemory s t (Memory.Allocation.copy s.memory x.toNat y.toNat z.toNat)
      (s.pc + 1) (s.gas - Gas.mcopyCost s.memory.words x.toNat y.toNat z.toNat) xs) :
    step s = .continue t ∧
    (∀ i, i < z.toNat → readByte t.memory.store (x.toNat + i) =
      readByte s.memory.store (y.toNat + i)) ∧
    (∀ a, ¬ (x.toNat ≤ a ∧ a < x.toNat + z.toNat) →
      readByte t.memory.store a = readByte s.memory.store a) := by
  have run := step_mcopy s t x y z xs at_ items gas fields
  exact ⟨run, (mcopy_success_output s t x y z xs at_ items run).2.2.2.2.2⟩

/-- Sufficient gas executes a copy of arbitrary snapshot contents. -/
theorem mcopy_program (s : State) (x y z : Word) (xs : List Word)
    (at_ : At s (some .mcopy)) (items : s.stack.val = x :: y :: z :: xs)
    (gas : Gas.mcopyCost s.memory.words x.toNat y.toNat z.toNat ≤ s.gas) :
    ∃ t, step s = .continue t ∧
      (∀ i, i < z.toNat → readByte t.memory.store (x.toNat + i) =
        readByte s.memory.store (y.toNat + i)) := by
  let stack : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  let t : State := { s with stack, pc := s.pc + 1, gas := s.gas - Gas.mcopyCost s.memory.words x.toNat y.toNat z.toNat, memory := Memory.Allocation.copy s.memory x.toNat y.toNat z.toNat, memoryValid := Memory.Allocation.copy_valid_for_frame _ _ _ _ s.memoryValid }
  have fields : AdvancesMemory s t (Memory.Allocation.copy s.memory x.toNat y.toNat z.toNat)
      (s.pc + 1) (s.gas - Gas.mcopyCost s.memory.words x.toNat y.toNat z.toNat) xs := by
    simp [AdvancesMemory, t, stack]
  have run := step_mcopy s t x y z xs at_ items gas fields
  exact ⟨t, run, (mcopy_success_output s t x y z xs at_ items run).2.2.2.2.2.1⟩

/-- Every continuing frame retains valid, aligned memory without shrinking it. -/
theorem continue_memory_invariants {s t : State} (run : step s = .continue t) :
    Memory.Allocation.Valid t.memory ∧ Memory.Allocation.byteSize t.memory % 32 = 0 ∧
      s.memory.words ≤ t.memory.words := by
  refine ⟨t.memoryValid, Memory.Allocation.byteSize_aligned _, ?_⟩
  have rule := (step_iff_rule s _).mp run
  cases rule <;> simp_all [Advances, AdvancesMemory, Memory.Allocation.loadWord,
    Memory.Allocation.read, Memory.Allocation.storeWord, Memory.Allocation.storeByte,
    Memory.Allocation.write, Memory.Allocation.expand, Memory.Allocation.copy,
    SstoreReady, SstoreReadFields, SstoreCreditFields, SstoreExecutionFields,
    SstoreChargeFields, SstoreMeterRetained, SstoreWriteFields]
  all_goals aesop

end EthLib.EVM.Frame
