module

public import EthLib.EVM.Memory.Ranges
public import EthLib.EVM.Proofs.Memory

/-!
# Range content laws

The proofs relate range operations to every observation of a sparse store.
The snapshot equation holds even when the source and destination overlap.
Equal observations do not imply equal finite write histories.
The execution specification expands memory before its slice operations.
These results do not establish allocation, gas, or instruction execution.
-/

@[expose] public section

namespace EthLib.EVM.Memory

/-- Reading a range produces the requested number of bytes. -/
theorem readRange_length (s : Store) (offset n : Nat) :
    (readRange s offset n).length = n := by
  induction n generalizing offset with
  | zero => rfl
  | succ n ih => simp [readRange, ih]

/-- A range read observes each address in order. -/
theorem readRange_getElem (s : Store) (offset n i : Nat) (h : i < n) :
    (readRange s offset n)[i]'(by simpa [readRange_length] using h) =
      readByte s (offset + i) := by
  induction n generalizing offset i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [readRange]
    | succ i =>
      simp only [readRange, List.getElem_cons_succ]
      rw [ih (offset + 1) i (by omega)]
      congr 1 <;> omega

/-- Reading zero bytes returns an empty list. -/
theorem readRange_zero (s : Store) (offset : Nat) : readRange s offset 0 = [] := rfl

/-- Writing an empty list leaves the history unchanged. -/
theorem writeRange_nil (s : Store) (offset : Nat) : writeRange s offset [] = s := rfl

/-- Copying zero bytes leaves the history unchanged. -/
theorem copyRange_zero (s : Store) (destination source : Nat) :
    copyRange s destination source 0 = s := rfl

/-- A write changes precisely the addresses covered by its data. -/
theorem writeRange_observe (s : Store) (offset q : Nat) (data : List UInt8) :
    readByte (writeRange s offset data) q =
      if h : offset ≤ q ∧ q < offset + data.length then
        data[q - offset]'(by omega)
      else readByte s q := by
  induction data generalizing offset with
  | nil =>
    simp only [writeRange, List.length_nil, Nat.add_zero]
    split
    · omega
    · rfl
  | cons b bs ih =>
    -- The head write covers the first address; the tail covers the rest.
    by_cases eq : offset = q
    · subst q
      simp [writeRange, readByte, writeByte]
    · by_cases inside : offset + 1 ≤ q ∧ q < offset + 1 + bs.length
      · have all : offset ≤ q ∧ q < offset + (b :: bs).length := by simp; omega
        have idx : q - offset = (q - (offset + 1)) + 1 := by omega
        simp only [writeRange, readByte, writeByte, ite_eq_right eq, ih, dite_eq_left inside, dite_eq_left all]
        simp [idx]
      · have out : ¬ (offset ≤ q ∧ q < offset + (b :: bs).length) := by simp; omega
        simp only [writeRange, readByte, writeByte, ite_eq_right eq, ih,
          dite_eq_right inside, dite_eq_right out]

/-- Reading back a written range recovers the data. -/
theorem readRange_writeRange (s : Store) (offset : Nat) (data : List UInt8) :
    readRange (writeRange s offset data) offset data.length = data := by
  apply List.ext_getElem
  · simp [readRange_length]
  · intro i h₁ h₂
    rw [readRange_getElem _ _ _ _ h₂, writeRange_observe]
    have h : offset ≤ offset + i ∧ offset + i < offset + data.length := by omega
    simp only [dite_eq_left h, Nat.add_sub_cancel_left]

/-- Writes outside an interval preserve the observed byte. -/
theorem writeRange_outside (s : Store) (offset q : Nat) (data : List UInt8)
    (h : ¬ (offset ≤ q ∧ q < offset + data.length)) :
    readByte (writeRange s offset data) q = readByte s q := by
  rw [writeRange_observe, dite_eq_right h]

/-- A disjoint read is unaffected by a write. -/
theorem readRange_writeRange_disjoint (s : Store) (offset start n : Nat)
    (data : List UInt8)
    (h : start + n ≤ offset ∨ offset + data.length ≤ start) :
    readRange (writeRange s offset data) start n = readRange s start n := by
  apply List.ext_getElem
  · simp [readRange_length]
  · intro i h₁ h₂
    have hi : i < n := by simpa [readRange_length] using h₁
    rw [readRange_getElem _ _ _ _ hi, readRange_getElem _ _ _ _ hi]
    apply writeRange_outside
    omega

/-- Disjoint writes commute as byte observations. -/
theorem writeRange_commute (s : Store) (a b : Nat) (xs ys : List UInt8)
    (h : a + xs.length ≤ b ∨ b + ys.length ≤ a) :
    contents (writeRange (writeRange s a xs) b ys) =
      contents (writeRange (writeRange s b ys) a xs) := by
  funext q
  simp only [contents, writeRange_observe]
  by_cases ha : a ≤ q ∧ q < a + xs.length
  · have hb : ¬ (b ≤ q ∧ q < b + ys.length) := by omega
    simp [ha, hb]
  · by_cases hb : b ≤ q ∧ q < b + ys.length <;> simp [ha, hb]

/-- Copying observes the original source throughout the destination interval. -/
theorem copyRange_observe (s : Store) (destination source n q : Nat) :
    readByte (copyRange s destination source n) q =
      if destination ≤ q ∧ q < destination + n then
        readByte s (source + (q - destination))
      else readByte s q := by
  cases n with
  | zero => simp only [copyRange, Nat.add_zero]; split <;> (first | omega | rfl)
  | succ n =>
    -- Substitute the indexed source observation into the pointwise write law.
    simp only [copyRange, writeRange_observe, readRange_length]
    split
    · rename_i h
      rw [readRange_getElem s source (n + 1) (q - destination) (by omega)]
    · rfl

/-- Copying a range onto itself preserves every byte observation. -/
theorem copyRange_self (s : Store) (address n : Nat) :
    contents (copyRange s address address n) = contents s := by
  funext q
  simp only [contents, copyRange_observe]
  split
  · rename_i h
    congr 1
    omega
  · rfl

/-- Copying leaves every address outside the destination interval unchanged. -/
theorem copyRange_outside (s : Store) (destination source n q : Nat)
    (h : ¬ (destination ≤ q ∧ q < destination + n)) :
    readByte (copyRange s destination source n) q = readByte s q := by
  rw [copyRange_observe, ite_eq_right h]

/-- Reading the destination after a copy returns the source snapshot. -/
theorem copyRange_snapshot (s : Store) (destination source n : Nat) :
    readRange (copyRange s destination source n) destination n = readRange s source n := by
  apply List.ext_getElem
  · simp [readRange_length]
  · intro i h₁ h₂
    have hi : i < n := by simpa [readRange_length] using h₁
    rw [readRange_getElem _ _ _ _ hi, readRange_getElem _ _ _ _ hi, copyRange_observe]
    have h : destination ≤ destination + i ∧ destination + i < destination + n := by omega
    simp [h]

/-- A later write of the same length replaces the earlier observed range. -/
theorem writeRange_overwrite (s : Store) (offset : Nat) (first second : List UInt8)
    (h : first.length = second.length) :
    contents (writeRange (writeRange s offset first) offset second) =
      contents (writeRange s offset second) := by
  funext q
  simp only [contents, writeRange_observe]
  split
  · rfl
  · rename_i outside
    have outside' : ¬ (offset ≤ q ∧ q < offset + first.length) := by simpa [h] using outside
    simp [outside']

/-- Every nonzero byte in the result has finite-history support. -/
theorem copyRange_finite_support (s : Store) (destination source n q : Nat)
    (h : readByte (copyRange s destination source n) q ≠ 0) :
    q ∈ support (copyRange s destination source n) :=
  nonzero_mem_support _ _ h

end EthLib.EVM.Memory
