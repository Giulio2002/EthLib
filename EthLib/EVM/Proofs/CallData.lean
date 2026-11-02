module

public import EthLib.EVM.CallData
public import EthLib.EVM.Proofs.PushImmediate
import Mathlib.Tactic

/-! Kernel-checked call-data byte and numeric contracts. -/

@[expose] public section
namespace EthLib.EVM.Proofs.CallData

open EthLib.EVM.CallData

/-- Every read contains exactly 32 bytes. -/
theorem bytes_length (ctx : Context) (offset : Word) :
    (bytes ctx offset).length = 32 := by
  simp [bytes]

/-- Each byte uses natural addition after converting the full offset. -/
theorem bytes_get (ctx : Context) (offset : Word) (i : Nat) (h : i < 32) :
    (bytes ctx offset)[i]'(by simp [bytes, h]) =
      PushImmediate.byteAt ctx.data (offset.toNat + i) := by
  simp [bytes]

/-- An index beyond the input is zero. -/
theorem bytes_pad (ctx : Context) (offset : Word) (i : Nat) (h : i < 32)
    (outside : ctx.data.size ≤ offset.toNat + i) :
    (bytes ctx offset)[i]'(by simp [bytes, h]) = 0 := by
  rw [bytes_get ctx offset i h]
  exact PushImmediate.byteAt_out_of_range _ _ outside

/-- An index inside the input returns the corresponding byte. -/
theorem bytes_in_range (ctx : Context) (offset : Word) (i : Nat) (h : i < 32)
    (inside : offset.toNat + i < ctx.data.size) :
    (bytes ctx offset)[i]'(by simp [bytes, h]) = ctx.data[offset.toNat + i] := by
  rw [bytes_get ctx offset i h]
  exact PushImmediate.byteAt_in_range _ _ inside

/-- A read starting beyond the input consists entirely of zero bytes. -/
theorem bytes_all_pad (ctx : Context) (offset : Word) (outside : ctx.data.size ≤ offset.toNat) :
    bytes ctx offset = List.replicate 32 0 := by
  apply List.ext_getElem
  · simp [bytes]
  · intro i h1 h2
    have hi : i < 32 := by simpa [bytes] using h1
    rw [bytes_pad ctx offset i hi (by omega)]
    simp only [List.getElem_replicate]

/-- A read starting beyond the input produces the zero word. -/
theorem load_all_pad (ctx : Context) (offset : Word) (outside : ctx.data.size ≤ offset.toNat) :
    load ctx offset = 0 := by
  rw [load, bytes_all_pad ctx offset outside, PushImmediate.fold_zeroes]
  rfl

/-- The loaded word is the exact big-endian value of its 32 bytes. -/
theorem load_numeric (ctx : Context) (offset : Word) :
    (load ctx offset).toNat =
      (bytes ctx offset).foldl (fun n b => 256 * n + b.toNat) 0 := by
  have h := PushImmediate.fold_bound (bytes ctx offset) 0
  simp only [Nat.zero_add, Nat.one_mul, bytes_length] at h
  have bound : (bytes ctx offset).foldl (fun n b => 256 * n + b.toNat) 0 < 2 ^ 256 := by
    have eq : 256 ^ 32 = 2 ^ 256 := by norm_num
    omega
  rw [load, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]

end EthLib.EVM.Proofs.CallData
