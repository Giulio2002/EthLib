module

public import EthLib.EVM.Memory

@[expose] public section

namespace EthLib.EVM.Memory

/-- Reading is exactly observation through the abstraction. -/
theorem read_refines (s : Store) (a : Nat) : readByte s a = contents s a := rfl

/-- An empty store reads as zero at every address. -/
theorem empty_read (a : Nat) : readByte empty a = 0 := rfl

/-- A write changes exactly its selected address. -/
theorem write_refines (s : Store) (a q : Nat) (v : UInt8) :
    contents (writeByte s a v) q = if a = q then v else contents s q := rfl

/-- Reading the address just written returns its value. -/
theorem read_write_same (s : Store) (a : Nat) (v : UInt8) :
    readByte (writeByte s a v) a = v := by simp [writeByte, readByte]

/-- A write leaves any distinct address unchanged. -/
theorem read_write_other (s : Store) (a q : Nat) (v : UInt8) (h : a ≠ q) :
    readByte (writeByte s a v) q = readByte s q := by simp [writeByte, readByte, h]

/-- The last of two writes at one address determines the observed contents. -/
theorem overwrite (s : Store) (a : Nat) (v w : UInt8) :
    contents (writeByte (writeByte s a v) a w) = contents (writeByte s a w) := by
  funext q
  by_cases h : a = q <;> simp [contents, writeByte, readByte, h]

/-- Writing back an observed byte leaves all observations unchanged. -/
theorem write_back (s : Store) (a : Nat) :
    contents (writeByte s a (readByte s a)) = contents s := by
  funext q
  by_cases h : a = q
  · subst q; simp [contents, writeByte, readByte]
  · simp [contents, writeByte, readByte, h]

/-- Writes at distinct addresses commute as observations. -/
theorem write_commute (s : Store) (a b : Nat) (v w : UInt8) (h : a ≠ b) :
    contents (writeByte (writeByte s a v) b w) =
      contents (writeByte (writeByte s b w) a v) := by
  funext q
  by_cases ha : a = q <;> by_cases hb : b = q <;>
    simp [contents, writeByte, readByte, ha, hb] at *

/-- A nonzero observation must occur in the finite address list. -/
theorem nonzero_mem_support (s : Store) (a : Nat) (h : readByte s a ≠ 0) :
    a ∈ support s := by
  induction s with
  | nil => simp [readByte] at h
  | cons p rest ih =>
    rcases p with ⟨b, v⟩
    by_cases eq : b = a
    · simp [support, eq]
    · have hr : readByte rest a ≠ 0 := by simpa [readByte, eq] using h
      simpa [support] using Or.inr (ih hr) (a := a = b)

/-- A write extends the finite address list by exactly one address. -/
theorem support_write (s : Store) (a : Nat) (v : UInt8) :
    support (writeByte s a v) = a :: support s := rfl

/-- Empty history has no stored addresses. -/
theorem support_empty : support empty = [] := rfl

end EthLib.EVM.Memory
