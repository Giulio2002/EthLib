module

public import EthLib.EVM.Proofs.Frame
public import EthLib.EVM.Proofs.Memory.WordAccess

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
        EthLib.Precompiles.Modexp.bytesToNat (readRange s.memory.store x.toNat 32) := by
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
        EthLib.Precompiles.Modexp.bytesToNat (readRange s.memory.store x.toNat 32) := by
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
    Memory.Allocation.write, Memory.Allocation.expand, Memory.Allocation.copy]

end EthLib.EVM.Frame
