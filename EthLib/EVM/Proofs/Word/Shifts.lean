module

public import EthLib.EVM.Word.Shifts
public import EthLib.EVM.Proofs.Word.SignedDivMod
public import EthLib.EVM.Proofs.Word

/-! # Shift result contracts -/

@[expose] public section

namespace EthLib.EVM.Proofs.Word.Shifts

open EthLib.EVM

/-- Left shift is modular multiplication for a count below 256. -/
theorem shl_small (count value : Word) (h : count.toNat < 256) :
    (Word.shl count value).toNat = (value.toNat * 2 ^ count.toNat) % (2 ^ 256) := by
  simp [Word.shl, h, BitVec.toNat_ofNat]

/-- Right shift is natural division for a count below 256. -/
theorem shr_small (count value : Word) (h : count.toNat < 256) :
    (Word.shr count value).toNat = value.toNat / 2 ^ count.toNat := by
  simp only [Word.shr, h, ite_true, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) value.isLt

/-- Left shift vanishes at and above the word width. -/
theorem shl_large (count value : Word) (h : 256 ≤ count.toNat) :
    Word.shl count value = 0 := by simp [Word.shl, Nat.not_lt.mpr h]

/-- Logical right shift vanishes at and above the word width. -/
theorem shr_large (count value : Word) (h : 256 ≤ count.toNat) :
    Word.shr count value = 0 := by simp [Word.shr, Nat.not_lt.mpr h]

/-- Arithmetic right shift fills with the sign at and above the word width. -/
theorem sar_large (count value : Word) (h : 256 ≤ count.toNat) :
    Word.sar count value = if Word.signed value < 0 then Word.ofSigned (-1) else 0 := by
  simp [Word.sar, Nat.not_lt.mpr h]

/-- The signed small-count result is encoded floor division. -/
theorem sar_small_word (count value : Word) (h : count.toNat < 256) :
    Word.sar count value = Word.ofSigned (Word.signed value / (2 ^ count.toNat : Int)) := by
  simp [Word.sar, h]

/-- Floor division by a positive power remains in the signed word range. -/
theorem quotient_range (count value : Word) :
    -(2 ^ 255 : Int) ≤ Word.signed value / (2 ^ count.toNat : Int) ∧
    Word.signed value / (2 ^ count.toNat : Int) < 2 ^ 255 := by
  have hp : (0 : Int) < 2 ^ count.toNat := by exact Int.pow_pos (by decide)
  have hv := SignedDivMod.signed_range value
  by_cases hs : 0 ≤ Word.signed value
  · have hq := Int.ediv_nonneg hs (Int.le_of_lt hp)
    have hu := Int.ediv_le_self (2 ^ count.toNat) hs
    omega
  · have hs' : Word.signed value ≤ 0 := by omega
    have hl := Int.self_le_ediv_of_nonpos_of_nonneg hs' (Int.le_of_lt hp)
    have hu := Int.ediv_neg_of_neg_of_pos (by omega : Word.signed value < 0) hp
    omega

/-- Small arithmetic shifts have exactly the signed floor quotient. -/
theorem sar_small (count value : Word) (h : count.toNat < 256) :
    Word.signed (Word.sar count value) = Word.signed value / (2 ^ count.toNat : Int) := by
  rw [sar_small_word count value h]
  let q : SignedDivMod.Value := ⟨_, quotient_range count value⟩
  exact congrArg Subtype.val (SignedDivMod.decode_encode q)

/-- The unsigned left result refines the complete piecewise rule. -/
theorem shl_refines (count value : Word) :
    (Word.shl count value).toNat =
      if count.toNat < 256 then (value.toNat * 2 ^ count.toNat) % (2 ^ 256) else 0 := by
  by_cases h : count.toNat < 256
  · simp [h, shl_small count value h]
  · simp [h, shl_large count value (Nat.le_of_not_gt h)]

/-- The unsigned right result refines the complete piecewise rule. -/
theorem shr_refines (count value : Word) :
    (Word.shr count value).toNat =
      if count.toNat < 256 then value.toNat / 2 ^ count.toNat else 0 := by
  by_cases h : count.toNat < 256
  · simp [h, shr_small count value h]
  · simp [h, shr_large count value (Nat.le_of_not_gt h)]

/-- The signed result refines the complete floor-division rule. -/
theorem sar_refines (count value : Word) :
    Word.signed (Word.sar count value) =
      if count.toNat < 256 then Word.signed value / (2 ^ count.toNat : Int)
      else if Word.signed value < 0 then -1 else 0 := by
  by_cases h : count.toNat < 256
  · simp [h, sar_small count value h]
  · rw [sar_large count value (Nat.le_of_not_gt h)]
    by_cases hs : Word.signed value < 0 <;> simp only [h, hs, ite_false, ite_true]
    · decide
    · rfl

/-- A negative input remains negative after an arithmetic shift. -/
theorem sar_negative (count value : Word) (h : Word.signed value < 0) :
    Word.signed (Word.sar count value) < 0 := by
  rw [sar_refines]
  split
  · exact Int.ediv_neg_of_neg_of_pos h (Int.pow_pos (by decide))
  · simp

/-- A nonnegative input stays nonnegative after an arithmetic shift. -/
theorem sar_nonnegative (count value : Word) (h : 0 ≤ Word.signed value) :
    0 ≤ Word.signed (Word.sar count value) := by
  rw [sar_refines]
  split
  · exact Int.ediv_nonneg h (Int.le_of_lt (Int.pow_pos (by decide)))
  · simp [Int.not_lt.mpr h]

/-- All shift results have the word bound. -/
theorem ranges (count value : Word) :
    (Word.shl count value).toNat < 2 ^ 256 ∧
    (Word.shr count value).toNat < 2 ^ 256 ∧
    (Word.sar count value).toNat < 2 ^ 256 :=
  ⟨(Word.shl count value).isLt, (Word.shr count value).isLt, (Word.sar count value).isLt⟩

/-- Zero left shift preserves the word. -/
theorem shl_zero (value : Word) : Word.shl 0 value = value := by
  apply BitVec.eq_of_toNat_eq
  simp [Word.shl]

/-- Zero logical right shift preserves the word. -/
theorem shr_zero (value : Word) : Word.shr 0 value = value := by
  apply BitVec.eq_of_toNat_eq
  simp [Word.shr]

/-- Zero arithmetic right shift preserves the word. -/
theorem sar_zero (value : Word) : Word.sar 0 value = value := by
  simpa [Word.sar, SignedDivMod.encode, SignedDivMod.decode] using SignedDivMod.encode_decode value

/-- A negative odd value rounds down. -/
theorem example_negative_odd : Word.sar 1 (Word.ofSigned (-3)) = Word.ofSigned (-2) := by decide

/-- Shift counts one, 255 and 256 pin the edges of a single set bit. -/
theorem examples_boundaries :
    Word.shl 1 1 = 2 ∧ Word.shl 255 1 = BitVec.ofNat 256 (2 ^ 255) ∧
    Word.shl 256 1 = 0 ∧ Word.shr 255 (BitVec.ofNat 256 (2 ^ 255)) = 1 ∧
    Word.shr 256 1 = 0 ∧ Word.sar 256 (Word.ofSigned (-3)) = Word.ofSigned (-1) := by
  decide

/-- The largest possible count takes the large-count branches. -/
theorem examples_max_count :
    Word.shl (-1) 1 = 0 ∧ Word.shr (-1) 1 = 0 ∧
    Word.sar (-1) (Word.ofSigned (-3)) = Word.ofSigned (-1) ∧
    Word.sar (-1) 1 = 0 := by decide

end EthLib.EVM.Proofs.Word.Shifts
