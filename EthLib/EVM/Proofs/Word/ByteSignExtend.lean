module

public import EthLib.EVM.Word.ByteSignExtend

/-!
# BYTE and SIGNEXTEND result contracts

The equations use natural arithmetic on unsigned word observations.
The correspondence with the cited sources is a human reading.
-/

@[expose] public section

namespace EthLib.EVM.Proofs.Word.ByteSignExtend

open EthLib.EVM
open EthLib.EVM.Word

/-- A BYTE index outside the word returns zero. -/
theorem byte_out_of_range (i v : Word) (h : 32 ≤ i.toNat) : byte i v = 0 := by
  simp [byte, Nat.not_lt.mpr h]

/-- BYTE extracts the selected big-endian byte for every in-range index. -/
theorem byte_in_range (i v : Word) (h : i.toNat < 32) :
    (byte i v).toNat = v.toNat / 2 ^ (8 * (31 - i.toNat)) % 256 := by
  simp only [byte, h, ↓reduceIte, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have := Nat.mod_lt (v.toNat / 2 ^ (8 * (31 - i.toNat))) (by decide : 0 < 256)
  exact Nat.lt_trans this (by decide)

/-- Every BYTE result fits in one byte. -/
theorem byte_lt (i v : Word) : (byte i v).toNat < 256 := by
  by_cases h : i.toNat < 32
  · rw [byte_in_range i v h]
    exact Nat.mod_lt _ (by decide)
  · rw [byte_out_of_range i v (Nat.le_of_not_gt h)]
    decide

/-- An index above 31 leaves the word unchanged. -/
theorem signextend_out_of_range (i v : Word) (h : 32 ≤ i.toNat) :
    signextend i v = v := by
  simp [signextend, Nat.not_lt.mpr h]

/-- The selected width never exceeds the word width. -/
theorem width_le (n : Nat) (h : n < 32) : 8 * (n + 1) ≤ 256 := by omega

/-- The selected low value and its high-fill form both fit in a word. -/
theorem filled_lt (n x : Nat) (h : n < 32) :
    2 ^ 256 - 2 ^ (8 * (n + 1)) + x % 2 ^ (8 * (n + 1)) < 2 ^ 256 := by
  have hp : 2 ^ (8 * (n + 1)) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) (width_le n h)
  have hl := Nat.mod_lt x (Nat.two_pow_pos (8 * (n + 1)))
  omega

/-- The selected low value fits in a word. -/
theorem low_lt (n x : Nat) (h : n < 32) : x % 2 ^ (8 * (n + 1)) < 2 ^ 256 := by
  have hp : 2 ^ (8 * (n + 1)) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) (width_le n h)
  exact Nat.lt_of_lt_of_le (Nat.mod_lt x (Nat.two_pow_pos _)) hp

/-- The unsigned result follows the low-byte and sign-bit arithmetic. -/
theorem signextend_equation (i v : Word) :
    (signextend i v).toNat =
      if i.toNat < 32 then
        let width := 8 * (i.toNat + 1)
        let low := v.toNat % 2 ^ width
        if low < 2 ^ (width - 1) then low else 2 ^ 256 - 2 ^ width + low
      else v.toNat := by
  simp only [signextend]
  split
  · rename_i h
    split
    · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (low_lt _ _ h)]
    · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (filled_lt _ _ h)]
  · rfl

/-- The arithmetic result agrees with truncation followed by sign extension. -/
theorem signextend_bitvec (i v : Word) (h : i.toNat < 32) :
    signextend i v = (v.setWidth (8 * (i.toNat + 1))).signExtend 256 := by
  apply BitVec.eq_of_toNat_eq
  rw [signextend_equation]
  simp only [h, ↓reduceIte]
  simp only [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.msb_eq_decide]
  rw [Nat.mod_eq_of_lt (low_lt _ _ h)]
  split <;> simp_all <;> omega

/-- Every selected low bit is preserved. -/
theorem signextend_low_bit (i v : Word) (h : i.toNat < 32) (k : Nat)
    (hk : k < 8 * (i.toNat + 1)) :
    (signextend i v).getLsbD k = v.getLsbD k := by
  rw [signextend_bitvec i v h]
  have hw := width_le i.toNat h
  rw [BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth]
  simp [hk, show k < 256 by omega]

/-- Every upper bit is a copy of the selected sign bit. -/
theorem signextend_upper_bit (i v : Word) (h : i.toNat < 32) (k : Nat)
    (hk : 8 * (i.toNat + 1) ≤ k) (hk256 : k < 256) :
    (signextend i v).getLsbD k = v.getLsbD (8 * (i.toNat + 1) - 1) := by
  rw [signextend_bitvec i v h]
  rw [BitVec.getLsbD_signExtend, BitVec.msb_setWidth]
  simp [hk256,
    show ¬ k < 8 * (i.toNat + 1) by omega,
    show 0 < 8 * (i.toNat + 1) by omega]

/-- The signed result is the signed interpretation of the selected low bytes. -/
theorem signextend_toInt (i v : Word) (h : i.toNat < 32) :
    (signextend i v).toInt = (v.setWidth (8 * (i.toNat + 1))).toInt := by
  rw [signextend_bitvec i v h]
  exact BitVec.toInt_signExtend_of_le (width_le _ h)

/-- Selecting all 32 bytes leaves the word unchanged. -/
theorem signextend_31 (v : Word) : signextend 31 v = v := by
  rw [signextend_bitvec 31 v (by decide)]
  simp

/-- Extending the same selected bytes twice has no further effect. -/
theorem signextend_idempotent (i v : Word) :
    signextend i (signextend i v) = signextend i v := by
  by_cases h : i.toNat < 32
  · apply BitVec.eq_of_getLsbD_eq
    intro k hk256
    by_cases hk : k < 8 * (i.toNat + 1)
    · rw [signextend_low_bit i _ h k hk]
    · rw [signextend_upper_bit i _ h k (by omega) hk256,
        signextend_upper_bit i v h k (by omega) hk256,
        signextend_low_bit i v h _ (by omega)]
  · rw [signextend_out_of_range i _ (Nat.le_of_not_gt h)]

/-! The reference functions take naturals and contain no BitVec operations. -/
namespace Reference

/-- Big-endian extraction from an unsigned word. -/
def byte (index value : Nat) : Nat :=
  if index < 32 then value / 2 ^ (8 * (31 - index)) % 256 else 0

/-- Interpret selected low bytes as a signed value represented in 256 bits. -/
def signextend (index value : Nat) : Nat :=
  if index < 32 then
    let width := 8 * (index + 1)
    let low := value % 2 ^ width
    if low < 2 ^ (width - 1) then low else 2 ^ 256 - 2 ^ width + low
  else value

end Reference

/-- BYTE refines the natural reference for every word pair. -/
theorem byte_refines (i v : Word) : (byte i v).toNat = Reference.byte i.toNat v.toNat := by
  by_cases h : i.toNat < 32
  · simp [Reference.byte, h, byte_in_range i v h]
  · simp [Reference.byte, h, byte_out_of_range i v (Nat.le_of_not_gt h)]

/-- SIGNEXTEND refines the natural reference for every word pair. -/
theorem signextend_refines (i v : Word) :
    (signextend i v).toNat = Reference.signextend i.toNat v.toNat := by
  exact signextend_equation i v

/-- The first byte is the most significant one, even with nonzero lower bytes. -/
theorem byte_first : byte 0 (BitVec.ofNat 256 (2 ^ 248 + 42)) = 1 := by decide

/-- The penultimate byte is selected at index 30. -/
theorem byte_30 : byte 30 (BitVec.ofNat 256 (2 ^ 248 + 0xabcd)) = 0xab := by decide

/-- The last byte is selected at index 31. -/
theorem byte_31 : byte 31 (BitVec.ofNat 256 0xabcd) = 0xcd := by decide

/-- Index 32 is outside the word. -/
theorem byte_32 : byte 32 (BitVec.ofNat 256 (2 ^ 248 + 42)) = 0 := by decide

/-- The largest word index is outside the word. -/
theorem byte_max : byte (BitVec.ofNat 256 (2 ^ 256 - 1)) 42 = 0 := by decide

/-- A clear sign bit discards nonzero high bytes. -/
theorem signextend_zero_positive : signextend 0 0x127f = 0x7f := by decide

/-- A set sign bit fills all high bytes. -/
theorem signextend_zero_negative :
    signextend 0 0x1280 = BitVec.ofNat 256 (2 ^ 256 - 128) := by decide

/-- Index 30 extends the sign at bit 247. -/
theorem signextend_30 :
    signextend 30 (BitVec.ofNat 256 (2 ^ 247)) =
      BitVec.ofNat 256 (2 ^ 256 - 2 ^ 247) := by decide

/-- Index 32 preserves a value with nonzero high bytes. -/
theorem signextend_32 : signextend 32 (BitVec.ofNat 256 (2 ^ 255 + 128)) =
    BitVec.ofNat 256 (2 ^ 255 + 128) := by decide

/-- The largest word index preserves the value. -/
theorem signextend_max : signextend (BitVec.ofNat 256 (2 ^ 256 - 1)) 128 = 128 := by decide

end EthLib.EVM.Proofs.Word.ByteSignExtend
