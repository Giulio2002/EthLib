module

public import EthLib.EVM.Memory.WordAccess
public import EthLib.EVM.Proofs.Memory.Allocation
public import EthLib.EVM.Proofs.Word

@[expose] public section

namespace EthLib.EVM.Memory.Allocation

open EthLib.EVM EthLib.EVM.Memory
open EthLib.EVM.Proofs.Word
open EthLib.Base

/-- Word loads preserve the store and allocate the requested 32 bytes. -/
theorem loadWord_state (s : State) (offset : Nat) :
    (loadWord s offset).2.store = s.store ∧
    (loadWord s offset).2.words = max s.words (requiredWords offset 32) := ⟨rfl, rfl⟩

/-- Word loads preserve validity. -/
theorem loadWord_valid (s : State) (offset : Nat) (h : Valid s) :
    Valid (loadWord s offset).2 := expand_valid s offset 32 h

/-- Word stores allocate the requested 32 bytes. -/
theorem storeWord_words (s : State) (offset : Nat) (value : Word) :
    (storeWord s offset value).words = max s.words (requiredWords offset 32) := by
  simp [storeWord, write, expand, toBytesBE_size]

/-- Word stores preserve validity. -/
theorem storeWord_valid (s : State) (offset : Nat) (value : Word) (h : Valid s) :
    Valid (storeWord s offset value) := write_valid s offset _ h

/-- Byte stores allocate the requested byte. -/
theorem storeByte_words (s : State) (offset : Nat) (value : Word) :
    (storeByte s offset value).words = max s.words (requiredWords offset 1) := rfl

/-- Byte stores preserve validity. -/
theorem storeByte_valid (s : State) (offset : Nat) (value : Word) (h : Valid s) :
    Valid (storeByte s offset value) := write_valid s offset _ h

/-- Loading a stored word returns the original word. -/
theorem loadWord_storeWord (s : State) (offset : Nat) (value : Word) :
    (loadWord (storeWord s offset value) offset).1 = value := by
  have hlen : value.toBytesBE.data.toList.length = 32 := by
    simpa using toBytesBE_size value
  simp only [loadWord, storeWord, read, write, expand]
  rw [← hlen, readRange_writeRange]
  have hc := ofBytesBE_toBytesBE value
  simp only [Word.ofBytesBE, toBytesBE_size, ↓reduceIte, Except.ok.injEq] at hc
  exact hc

/-- A word load is the big-endian numeric fold of the 32 observed bytes. -/
theorem loadWord_numeric (s : State) (offset : Nat) :
    (loadWord s offset).1.toNat = bytesToNat (readRange s.store offset 32) := by
  have h : bytesToNat (readRange s.store offset 32) < 2 ^ 256 := by
    have h := bytesToNat_lt (readRange s.store offset 32)
    rw [readRange_length] at h
    convert h using 1
  simp only [loadWord, read, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The stored word leaves all bytes outside its 32-byte range unchanged. -/
theorem storeWord_outside (s : State) (offset a : Nat) (value : Word)
    (h : ¬ (offset ≤ a ∧ a < offset + 32)) :
    readByte (storeWord s offset value).store a = readByte s.store a := by
  apply writeRange_outside
  simpa [toBytesBE_size] using h

/-- The stored byte leaves every other address unchanged. -/
theorem storeByte_outside (s : State) (offset a : Nat) (value : Word)
    (h : a ≠ offset) : readByte (storeByte s offset value).store a = readByte s.store a := by
  apply writeRange_outside
  simp only [List.length_singleton]
  omega

/-- The stored byte is the low base-256 digit. -/
theorem storeByte_value (s : State) (offset : Nat) (value : Word) :
    (readByte (storeByte s offset value).store offset).toNat = value.toNat % 256 := by
  simp [storeByte, write, writeRange, readByte, writeByte]

/-- Copying 32 bytes then loading observes the original source word. -/
theorem loadWord_copy (s : State) (destination source : Nat) :
    (loadWord (copy s destination source 32) destination).1 = (loadWord s source).1 := by
  simp only [loadWord, read, copy_snapshot]

/-- Every stored word byte is the corresponding big-endian digit. -/
theorem storeWord_byte (s : State) (offset i : Nat) (value : Word) (h : i < 32) :
    readByte (storeWord s offset value).store (offset + i) =
      UInt8.ofNat ((value.toNat / 256 ^ (31 - i)) % 256) := by
  have hlen : value.toBytesBE.data.toList.length = 32 := by
    simpa using toBytesBE_size value
  have hin : offset ≤ offset + i ∧ offset + i < offset + value.toBytesBE.data.toList.length := by
    rw [hlen]
    omega
  simp only [storeWord, write]
  rw [writeRange_observe, dite_eq_left hin]
  simpa [Nat.add_sub_cancel_left] using toBytesBE_get value i h

/-- A disjoint read is unaffected by a word store. -/
theorem storeWord_disjoint (s : State) (offset start n : Nat) (value : Word)
    (h : start + n ≤ offset ∨ offset + 32 ≤ start) :
    readRange (storeWord s offset value).store start n = readRange s.store start n := by
  apply readRange_writeRange_disjoint
  simpa [toBytesBE_size] using h

/-- Bytes beyond a valid state's allocation are zero on a load. -/
theorem loadWord_zero_byte (s : State) (offset i : Nat) (h : Valid s)
    (hi : i < 32) (outside : byteSize s ≤ offset + i) :
    (readRange s.store offset 32)[i]'(by simpa [readRange_length] using hi) = 0 := by
  rw [readRange_getElem s.store offset 32 i hi]
  exact h _ outside

/-- The total load agrees with the checked word decoder on its exact-length input. -/
theorem loadWord_codec (s : State) (offset : Nat) :
    Word.ofBytesBE ⟨(readRange s.store offset 32).toArray⟩ =
      .ok (loadWord s offset).1 := by
  apply (ofBytesBE_ok_iff _ _).2
  constructor
  · change (readRange s.store offset 32).toArray.size = 32
    simp [readRange_length]
  · simpa using loadWord_numeric s offset

/-- A disjoint read is unaffected by a single-byte store. -/
theorem storeByte_disjoint (s : State) (offset start n : Nat) (value : Word)
    (h : start + n ≤ offset ∨ offset + 1 ≤ start) :
    readRange (storeByte s offset value).store start n = readRange s.store start n := by
  apply readRange_writeRange_disjoint
  simpa using h

/-- A disjoint word store does not change the value loaded. -/
theorem loadWord_storeWord_disjoint (s : State) (offset start : Nat) (value : Word)
    (h : start + 32 ≤ offset ∨ offset + 32 ≤ start) :
    (loadWord (storeWord s offset value) start).1 = (loadWord s start).1 := by
  simp only [loadWord, read]
  rw [storeWord_disjoint s offset start 32 value h]

/-- A disjoint byte store does not change the value loaded. -/
theorem loadWord_storeByte_disjoint (s : State) (offset start : Nat) (value : Word)
    (h : start + 32 ≤ offset ∨ offset + 1 ≤ start) :
    (loadWord (storeByte s offset value) start).1 = (loadWord s start).1 := by
  simp only [loadWord, read]
  rw [storeByte_disjoint s offset start 32 value h]

/-- Disjoint range stores commute as observations and allocation sizes. -/
theorem write_disjoint_commute (s : State) (a b : Nat) (xs ys : List UInt8)
    (h : a + xs.length ≤ b ∨ b + ys.length ≤ a) :
    contents (write (write s a xs) b ys).store =
      contents (write (write s b ys) a xs).store ∧
    (write (write s a xs) b ys).words = (write (write s b ys) a xs).words := by
  constructor
  · exact writeRange_commute s.store a b xs ys h
  · simp [write, expand, Nat.max_assoc, Nat.max_comm, Nat.max_left_comm]

/-- Disjoint word stores commute in observations and allocated words. -/
theorem storeWord_commute (s : State) (a b : Nat) (x y : Word)
    (h : a + 32 ≤ b ∨ b + 32 ≤ a) :
    contents (storeWord (storeWord s a x) b y).store =
      contents (storeWord (storeWord s b y) a x).store ∧
    (storeWord (storeWord s a x) b y).words = (storeWord (storeWord s b y) a x).words := by
  apply write_disjoint_commute
  simpa [toBytesBE_size] using h

/-- A disjoint word store and byte store commute in observations and allocated words. -/
theorem storeWord_storeByte_commute (s : State) (a b : Nat) (x y : Word)
    (h : a + 32 ≤ b ∨ b + 1 ≤ a) :
    contents (storeByte (storeWord s a x) b y).store =
      contents (storeWord (storeByte s b y) a x).store ∧
    (storeByte (storeWord s a x) b y).words = (storeWord (storeByte s b y) a x).words := by
  apply write_disjoint_commute
  simpa [toBytesBE_size] using h

/-- Distinct byte stores commute in observations and allocated words. -/
theorem storeByte_commute (s : State) (a b : Nat) (x y : Word) (h : a ≠ b) :
    contents (storeByte (storeByte s a x) b y).store =
      contents (storeByte (storeByte s b y) a x).store ∧
    (storeByte (storeByte s a x) b y).words = (storeByte (storeByte s b y) a x).words := by
  apply write_disjoint_commute
  simp only [List.length_singleton]
  omega

/-- A read whose suffix is beyond allocation contains the original prefix and zeros. -/
theorem readRange_right_zeros (s : State) (offset k : Nat) (h : Valid s)
    (hk : k ≤ 32) (outside : byteSize s ≤ offset + k) :
    readRange s.store offset 32 = readRange s.store offset k ++ List.replicate (32 - k) 0 := by
  apply List.ext_getElem
  · simp [readRange_length, hk]
  · intro i hi hj
    have hi32 : i < 32 := by simpa [readRange_length] using hi
    rw [readRange_getElem _ _ _ _ hi32]
    by_cases hik : i < k
    · rw [List.getElem_append_left (by simpa [readRange_length] using hik)]
      exact (readRange_getElem _ _ _ _ hik).symm
    · have hle : (readRange s.store offset k).length ≤ i := by simpa [readRange_length] using Nat.le_of_not_gt hik
      rw [List.getElem_append_right hle]
      simp only [List.getElem_replicate]
      apply h
      change s.words * 32 ≤ offset + k at outside
      omega

/-- Zero bytes contribute zero to the big-endian fold. -/
theorem bytesToNat_replicate_zero (n : Nat) : bytesToNat (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [List.replicate_succ, bytesToNat, List.foldl_cons,
      UInt8.toNat_zero, Nat.zero_mul, Nat.zero_add] using ih

/-- A load preserves the available prefix and shifts it over its zero suffix. -/
theorem loadWord_right_zero_padding (s : State) (offset k : Nat) (h : Valid s)
    (hk : k ≤ 32) (outside : byteSize s ≤ offset + k) :
    (loadWord s offset).1.toNat = bytesToNat (readRange s.store offset k) * 256 ^ (32 - k) := by
  rw [loadWord_numeric, readRange_right_zeros s offset k h hk outside, bytesToNat_append]
  simp [bytesToNat_replicate_zero]

/-- A load entirely beyond allocation returns the zero word. -/
theorem loadWord_outside_zero (s : State) (offset : Nat) (h : Valid s)
    (outside : byteSize s ≤ offset) : (loadWord s offset).1 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simpa [readRange, bytesToNat] using loadWord_right_zero_padding s offset 0 h (by omega) (by simpa using outside)

end EthLib.EVM.Memory.Allocation
