module

public import EthLib.EVM.PushImmediate
import Mathlib.Tactic

/-! Kernel-checked properties of PUSH immediate data. -/

@[expose] public section

namespace EthLib.EVM.Proofs.PushImmediate

open EthLib.EVM.PushImmediate

/-- Reading an in-range byte returns the byte from the code. -/
theorem byteAt_in_range (code : ByteArray) (offset : Nat) (h : offset < code.size) :
    byteAt code offset = code[offset] := by
  simp [byteAt, h]

/-- Reading beyond the code returns zero. -/
theorem byteAt_out_of_range (code : ByteArray) (offset : Nat) (h : code.size ≤ offset) :
    byteAt code offset = 0 := by
  simp [byteAt, Nat.not_lt.mpr h]

/-- The padded result has exactly the requested number of bytes. -/
theorem bytes_length (code : ByteArray) (pc : Nat) (length : Length) :
    (bytes code pc length).length = length.val := by
  simp [bytes]

/-- PUSH0 has an empty immediate. -/
theorem bytes_zero (code : ByteArray) (pc : Nat) :
    bytes code pc ⟨0, by decide⟩ = [] := by
  rfl

/-- PUSH0 yields zero. -/
theorem value_zero (code : ByteArray) (pc : Nat) :
    value code pc ⟨0, by decide⟩ = 0 := by
  rfl

/-- A big-endian fold over bytes stays below its width bound. -/
theorem fold_bound (xs : List UInt8) (a : Nat) :
    xs.foldl (fun n b => 256 * n + b.toNat) a < (a + 1) * 256 ^ xs.length := by
  induction xs generalizing a with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons, List.length_cons, Nat.pow_succ]
    -- A byte contributes less than one base-256 digit.
    have hb := UInt8.toNat_lt b
    have hp : 0 < 256 ^ bs.length := by positivity
    have hi := ih (256 * a + b.toNat)
    nlinarith

/-- Every PUSH immediate fits in a 256-bit word. -/
theorem value_bound (code : ByteArray) (pc : Nat) (length : Length) :
    (bytes code pc length).foldl (fun n b => 256 * n + b.toNat) 0 < 2 ^ 256 := by
  have h := fold_bound (bytes code pc length) 0
  simp only [Nat.zero_add, Nat.one_mul, show (bytes code pc length).length = length.val by simp [bytes]] at h
  -- At most 32 base-256 digits fit in 256 bits.
  have hl : length.val ≤ 32 := by have := length.isLt; omega
  have hp : 256 ^ length.val ≤ 2 ^ 256 := by
    calc
      256 ^ length.val = 2 ^ (8 * length.val) := by norm_num [Nat.pow_mul]
      _ ≤ 2 ^ 256 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- The word has exactly the big-endian numeric value of its bytes. -/
theorem value_numeric (code : ByteArray) (pc : Nat) (length : Length) :
    (value code pc length).toNat =
      (bytes code pc length).foldl (fun n b => 256 * n + b.toNat) 0 := by
  rw [value, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (value_bound code pc length)]

/-- Each immediate byte comes from its corresponding code offset. -/
theorem bytes_get (code : ByteArray) (pc : Nat) (length : Length) (i : Nat)
    (h : i < length.val) :
    (bytes code pc length)[i]'(by simp [bytes, h]) = byteAt code (pc + 1 + i) := by
  simp [bytes]

/-- Every requested byte beyond the code is zero. -/
theorem bytes_pad (code : ByteArray) (pc : Nat) (length : Length) (i : Nat)
    (h : i < length.val) (ho : code.size ≤ pc + 1 + i) :
    (bytes code pc length)[i]'(by simp [bytes, h]) = 0 := by
  rw [bytes_get code pc length i h]
  simp [byteAt, Nat.not_lt.mpr ho]

/-- An immediate entirely beyond the code is all zeros. -/
theorem bytes_all_pad (code : ByteArray) (pc : Nat) (length : Length)
    (h : code.size ≤ pc + 1) : bytes code pc length = List.replicate length.val 0 := by
  apply List.ext_getElem
  · simp [bytes]
  · intro i h1 h2
    have hi : i < length.val := by simpa [bytes] using h1
    rw [bytes_pad code pc length i hi (by omega)]
    simp

/-- A sequence of zero bytes has numeric value zero. -/
theorem fold_zeroes (n : Nat) :
    (List.replicate n (0 : UInt8)).foldl (fun n b => 256 * n + b.toNat) 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ] using ih

/-- An immediate entirely beyond the code has value zero. -/
theorem value_all_pad (code : ByteArray) (pc : Nat) (length : Length)
    (h : code.size ≤ pc + 1) : value code pc length = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [value_numeric, bytes_all_pad code pc length h, fold_zeroes]
  rfl

/-- A PUSH uses its encoded length for all three decoded fields. -/
theorem decode_push (code : ByteArray) (pc : Nat) (length : Length) :
    decode (.push length) code pc =
      some ⟨bytes code pc length, value code pc length, pc + 1 + length.val⟩ := by
  rfl

/-- Non-PUSH opcodes do not have immediate data. -/
theorem decode_non_push (op : EthLib.EVM.Opcode) (code : ByteArray) (pc : Nat)
    (h : ∀ length, op ≠ .push length) : decode op code pc = none := by
  cases op <;> simp_all [decode]

/-- Appending zero bytes shifts a big-endian value left by eight bits per byte. -/
theorem fold_pad (n a : Nat) :
    (List.replicate n (0 : UInt8)).foldl (fun n b => 256 * n + b.toNat) a = a * 256 ^ n := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    change (List.replicate n (0 : UInt8)).foldl (fun n b => 256 * n + b.toNat) (256 * a) = _
    rw [ih, Nat.pow_succ]
    ac_rfl

/-- Right padding contributes only the corresponding power of 256. -/
theorem value_padded (code : ByteArray) (pc : Nat) (length : Length)
    (front : List UInt8) (n : Nat)
    (h : bytes code pc length = front ++ List.replicate n 0) :
    (value code pc length).toNat =
      front.foldl (fun n b => 256 * n + b.toNat) 0 * 256 ^ n := by
  rw [value_numeric, h, List.foldl_append, fold_pad]

/-- A suffix past the code is exactly the missing number of zero bytes. -/
theorem bytes_split_pad (code : ByteArray) (pc : Nat) (length : Length) (k : Nat)
    (hk : k ≤ length.val) (ho : code.size ≤ pc + 1 + k) :
    bytes code pc length = (bytes code pc length).take k ++ List.replicate (length.val - k) 0 := by
  -- Split the immediate at the first position known to lie beyond the code.
  conv_lhs => rw [← List.take_append_drop k (bytes code pc length)]
  congr 1
  apply List.ext_getElem
  · simp [bytes]
  · intro i h1 h2
    have hh : i < length.val - k := by simpa [bytes] using h1
    have hi : k + i < length.val := by omega
    simp only [List.getElem_drop, List.getElem_replicate]
    exact bytes_pad code pc length (k + i) hi (by omega)

/-- A truncated immediate shifts its available prefix by its missing byte count. -/
theorem value_split_pad (code : ByteArray) (pc : Nat) (length : Length) (k : Nat)
    (hk : k ≤ length.val) (ho : code.size ≤ pc + 1 + k) :
    (value code pc length).toNat =
      ((bytes code pc length).take k).foldl (fun n b => 256 * n + b.toNat) 0 *
        256 ^ (length.val - k) := by
  exact value_padded code pc length _ _ (bytes_split_pad code pc length k hk ho)

end EthLib.EVM.Proofs.PushImmediate
