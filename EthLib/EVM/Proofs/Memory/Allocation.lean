module

public import EthLib.EVM.Memory.Allocation
public import EthLib.EVM.Proofs.Memory.Ranges

@[expose] public section

namespace EthLib.EVM.Memory.Allocation

open EthLib.EVM.Memory

/-- Empty ranges never require allocation. -/
theorem requiredWords_zero (offset : Nat) : requiredWords offset 0 = 0 := by
  simp [requiredWords]

/-- Nonempty ranges use the ceiling of their end address in words. -/
theorem requiredWords_nonzero (offset length : Nat) (h : length ≠ 0) :
    requiredWords offset length = (offset + length + 31) / 32 := by
  simp [requiredWords, h]

/-- The rounded size covers every nonempty range. -/
theorem requiredWords_covers (offset length : Nat) (h : length ≠ 0) :
    offset + length ≤ requiredWords offset length * 32 := by
  simp only [requiredWords_nonzero _ _ h]
  omega

/-- The rounded size is the least word multiple covering a nonempty range. -/
theorem requiredWords_least (offset length words : Nat) (h : length ≠ 0)
    (cover : offset + length ≤ words * 32) : requiredWords offset length ≤ words := by
  simp only [requiredWords_nonzero _ _ h]
  omega

/-- Every logical byte size is word aligned. -/
theorem byteSize_aligned (s : State) : byteSize s % 32 = 0 := by
  simp [byteSize]

/-- The empty state satisfies the zero-outside invariant. -/
theorem empty_valid : Valid empty := by
  intro a _
  rfl

/-- Expansion has exactly the requested size and leaves the store unchanged. -/
theorem expand_contract (s : State) (offset length : Nat) :
    (expand s offset length).store = s.store ∧
    (expand s offset length).words = max s.words (requiredWords offset length) := ⟨rfl, rfl⟩

/-- Empty expansion is the identity, even at large offsets. -/
theorem expand_zero (s : State) (offset : Nat) : expand s offset 0 = s := by
  cases s; simp [expand, requiredWords]

/-- Expansion cannot shrink memory. -/
theorem expand_monotone (s : State) (offset length : Nat) :
    s.words ≤ (expand s offset length).words := Nat.le_max_left _ _

/-- Repeating an expansion has no effect. -/
theorem expand_idempotent (s : State) (offset length : Nat) :
    expand (expand s offset length) offset length = expand s offset length := by
  cases s; simp [expand, Nat.max_assoc]

/-- Two expansions commute and take the maximum of both requirements. -/
theorem expand_pair (s : State) (a n b m : Nat) :
    expand (expand s a n) b m = expand (expand s b m) a n ∧
    (expand (expand s a n) b m).words =
      max s.words (max (requiredWords a n) (requiredWords b m)) := by
  constructor
  · cases s; simp [expand, Nat.max_assoc, Nat.max_comm, Nat.max_left_comm]
  · simp [expand, Nat.max_assoc]

/-- Expanding a valid state preserves its invariant. -/
theorem expand_valid (s : State) (offset length : Nat) (h : Valid s) :
    Valid (expand s offset length) := by
  intro a ha
  apply h a
  simp only [expand] at ha
  have := Nat.le_max_left s.words (requiredWords offset length)
  omega

/-- Every byte newly covered by an expansion was zero. -/
theorem expand_new_zero (s : State) (offset length a : Nat) (h : Valid s)
    (outside : byteSize s ≤ a) : readByte (expand s offset length).store a = 0 :=
  h a outside

/-- Read returns the original range and changes only the allocation. -/
theorem read_contract (s : State) (offset length : Nat) :
    (read s offset length).1 = readRange s.store offset length ∧
    (read s offset length).2.store = s.store ∧
    (read s offset length).2.words = max s.words (requiredWords offset length) :=
  ⟨rfl, rfl, rfl⟩

/-- A read preserves validity. -/
theorem read_valid (s : State) (offset length : Nat) (h : Valid s) :
    Valid (read s offset length).2 := expand_valid s offset length h

/-- A read returns each original byte in address order. -/
theorem read_observe (s : State) (offset length i : Nat) (h : i < length) :
    (read s offset length).1[i]'(by simpa [read, readRange_length] using h) =
      readByte s.store (offset + i) :=
  readRange_getElem s.store offset length i h

/-- Reading an empty range leaves the state unchanged. -/
theorem read_zero (s : State) (offset : Nat) : read s offset 0 = ([], s) := by
  simp [read, readRange, expand_zero]

/-- A write uses the range store and allocates exactly its payload. -/
theorem write_contract (s : State) (offset : Nat) (data : List UInt8) :
    (write s offset data).store = writeRange s.store offset data ∧
    (write s offset data).words = max s.words (requiredWords offset data.length) :=
  ⟨rfl, rfl⟩

/-- A write changes exactly the bytes covered by its payload. -/
theorem write_observe (s : State) (offset a : Nat) (data : List UInt8) :
    readByte (write s offset data).store a =
      if h : offset ≤ a ∧ a < offset + data.length then
        data[a - offset]'(by omega)
      else readByte s.store a :=
  writeRange_observe s.store offset a data

/-- A write preserves validity. -/
theorem write_valid (s : State) (offset : Nat) (data : List UInt8) (h : Valid s) :
    Valid (write s offset data) := by
  intro a ha
  change max s.words (requiredWords offset data.length) * 32 ≤ a at ha
  change readByte (writeRange s.store offset data) a = 0
  apply Eq.trans (writeRange_outside _ _ _ _ ?_) (h a (by
    have := Nat.le_max_left s.words (requiredWords offset data.length)
    omega))
  intro inside
  have len : data.length ≠ 0 := by omega
  have cover := requiredWords_covers offset data.length len
  have bound := Nat.le_max_right s.words (requiredWords offset data.length)
  omega

/-- Copy uses the original snapshot and allocates both ranges. -/
theorem copy_contract (s : State) (destination source length : Nat) :
    (copy s destination source length).store = copyRange s.store destination source length ∧
    (copy s destination source length).words =
      max s.words (max (requiredWords source length) (requiredWords destination length)) := by
  simp [copy, expand, Nat.max_assoc]

/-- Copy preserves validity, including when the ranges overlap. -/
theorem copy_valid (s : State) (destination source length : Nat) (h : Valid s) :
    Valid (copy s destination source length) := by
  intro a ha
  change max (max s.words (requiredWords source length))
    (requiredWords destination length) * 32 ≤ a at ha
  change readByte (copyRange s.store destination source length) a = 0
  apply Eq.trans (copyRange_outside _ _ _ _ _ ?_) (h a (by
    have h₁ := Nat.le_max_left s.words (requiredWords source length)
    have h₂ := Nat.le_max_left (max s.words (requiredWords source length))
      (requiredWords destination length)
    omega))
  intro inside
  have len : length ≠ 0 := by omega
  have cover := requiredWords_covers destination length len
  have bound := Nat.le_max_right (max s.words (requiredWords source length))
    (requiredWords destination length)
  omega

/-- Copy observations refine snapshot copying for every address. -/
theorem copy_observe (s : State) (destination source length a : Nat) :
    readByte (copy s destination source length).store a =
      if destination ≤ a ∧ a < destination + length then
        readByte s.store (source + (a - destination)) else readByte s.store a :=
  copyRange_observe _ _ _ _ _

/-- The destination observes the original source snapshot after a copy. -/
theorem copy_snapshot (s : State) (destination source length : Nat) :
    readRange (copy s destination source length).store destination length =
      readRange s.store source length :=
  copyRange_snapshot _ _ _ _

/-- Empty writes leave the state unchanged. -/
theorem write_nil (s : State) (offset : Nat) : write s offset [] = s := by
  cases s; simp [write, expand, requiredWords, writeRange]

/-- Empty copies leave the state unchanged. -/
theorem copy_zero (s : State) (destination source : Nat) : copy s destination source 0 = s := by
  cases s; simp [copy, expand, requiredWords, copyRange]

end EthLib.EVM.Memory.Allocation
