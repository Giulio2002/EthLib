module

public import EthLib.EVM.Memory.WordAccess

/-!
# Invariants needed to construct frame states

Cancun execution-specs `vm/instructions/memory.py`, `mload`, `mstore`, and
`mstore8`, expand memory before accessing it.
These lemmas justify the dependent validity field of a frame.

-/

@[expose] public section
namespace EthLib.EVM.Memory.Allocation

open EthLib.EVM.Memory

private theorem range_outside (s : Store) (offset q : Nat) (data : List UInt8)
    (h : offset + data.length ≤ q) :
    readByte (writeRange s offset data) q = readByte s q := by
  induction data generalizing offset with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons] at h
    simp only [writeRange, writeByte, readByte]
    have ne : offset ≠ q := by omega
    simp only [ne, ↓reduceIte]
    apply ih
    omega

/-- Expansion preserves the zero-outside invariant. -/
theorem expand_valid_for_frame (s : State) (offset length : Nat) (h : Valid s) :
    Valid (expand s offset length) := by
  intro a ha
  apply h a
  change max s.words (requiredWords offset length) * 32 ≤ a at ha
  have := Nat.le_max_left s.words (requiredWords offset length)
  omega

/-- A finite write preserves the zero-outside invariant. -/
theorem write_valid_for_frame (s : State) (offset : Nat) (data : List UInt8) (h : Valid s) :
    Valid (write s offset data) := by
  intro a ha
  change max s.words (requiredWords offset data.length) * 32 ≤ a at ha
  change readByte (writeRange s.store offset data) a = 0
  have old : s.words * 32 ≤ a := by
    have := Nat.le_max_left s.words (requiredWords offset data.length)
    omega
  by_cases empty : data.length = 0
  · have : data = [] := List.length_eq_zero_iff.mp empty
    subst data
    exact h a old
  · have cover : offset + data.length ≤ requiredWords offset data.length * 32 := by
      simp only [requiredWords, ite_eq_right empty]
      omega
    have bound := Nat.le_max_right s.words (requiredWords offset data.length)
    rw [range_outside _ _ _ _ (by omega)]
    exact h a old

/-- Snapshot copying preserves the zero-outside invariant. -/
theorem copy_valid_for_frame (s : State) (destination source length : Nat) (h : Valid s) :
    Valid (copy s destination source length) := by
  cases length with
  | zero => simpa [copy, copyRange, expand, requiredWords] using h
  | succ n =>
    intro a ha
    change max (max s.words (requiredWords source (n + 1)))
      (requiredWords destination (n + 1)) * 32 ≤ a at ha
    change readByte (writeRange s.store destination (readRange s.store source (n + 1))) a = 0
    have len : (readRange s.store source (n + 1)).length = n + 1 := by
      have lengths (offset count : Nat) : (readRange s.store offset count).length = count := by
        induction count generalizing offset with
        | zero => rfl
        | succ k ih => simp [readRange, ih]
      exact lengths source (n + 1)
    have cover : destination + (n + 1) ≤ requiredWords destination (n + 1) * 32 := by
      simp only [requiredWords, Nat.succ_ne_zero, ite_false]
      omega
    have bound := Nat.le_max_right (max s.words (requiredWords source (n + 1)))
      (requiredWords destination (n + 1))
    rw [range_outside _ _ _ _ (by rw [len]; omega)]
    apply h
    have := Nat.le_max_left s.words (requiredWords source (n + 1))
    have := Nat.le_max_left (max s.words (requiredWords source (n + 1)))
      (requiredWords destination (n + 1))
    omega

end EthLib.EVM.Memory.Allocation
