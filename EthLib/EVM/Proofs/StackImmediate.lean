module

public import EthLib.EVM.StackImmediate
public import EthLib.EVM.Proofs.JumpDest
import Mathlib.Tactic

/-! Contracts for the Amsterdam stack instruction immediates. -/

@[expose] public section

namespace EthLib.EVM.Proofs.StackImmediate

open EthLib.EVM

/-- The source single-index equation holds for every accepted byte. -/
theorem single_source_iff (x : UInt8) (n : Nat) :
    StackImmediate.decodeSingle x = some n ↔
      (x.toNat ≤ 90 ∨ 128 ≤ x.toNat) ∧ n = (x.toNat + 145) % 256 := by
  simp [StackImmediate.decodeSingle, eq_comm]

/-- The source pair-index equations hold for every accepted byte. -/
theorem pair_source_iff (x : UInt8) (n m : Nat) :
    StackImmediate.decodePair x = some (n, m) ↔
      (x.toNat ≤ 81 ∨ 128 ≤ x.toNat) ∧
      let k := Nat.xor x.toNat 143
      let q := k / 16
      let r := k % 16
      (n, m) = if q < r then (q + 1, r + 1) else (r + 1, 29 - q) := by
  by_cases valid : x.toNat ≤ 81 ∨ 128 ≤ x.toNat
  · simp only [StackImmediate.decodePair, valid, ite_true, true_and]
    split <;> simp [eq_comm]
  · simp [StackImmediate.decodePair, valid]

/-- DUPN and SWAPN reject exactly the source's forbidden range. -/
theorem single_none (x : UInt8) :
    StackImmediate.decodeSingle x = none ↔ 90 < x.toNat ∧ x.toNat < 128 := by
  simp [StackImmediate.decodeSingle]

/-- EXCHANGE rejects exactly the source's forbidden range. -/
theorem pair_none (x : UInt8) :
    StackImmediate.decodePair x = none ↔ 81 < x.toNat ∧ x.toNat < 128 := by
  simp [StackImmediate.decodePair]
  split <;> simp_all

/-- Every accepted single index is in the source range. -/
theorem single_range (x : UInt8) (n : Nat) (h : StackImmediate.decodeSingle x = some n) :
    17 ≤ n ∧ n ≤ 235 := by
  have check (i : Fin 256) : ∀ n, StackImmediate.decodeSingle (UInt8.ofNat i.val) = some n →
      17 ≤ n ∧ n ≤ 235 := by
    fin_cases i <;> simp [StackImmediate.decodeSingle]
  have hx : UInt8.ofNat x.toNat = x := UInt8.ofNat_toNat
  rw [← hx] at h
  exact check ⟨x.toNat, UInt8.toNat_lt x⟩ n h

/-- Every accepted pair is in the source range. -/
theorem pair_range (x : UInt8) (n m : Nat)
    (h : StackImmediate.decodePair x = some (n, m)) :
    1 ≤ n ∧ n ≤ 14 ∧ n < m ∧ n + m ≤ 30 := by
  have check (i : Fin 256) : ∀ n m,
      StackImmediate.decodePair (UInt8.ofNat i.val) = some (n, m) →
      1 ≤ n ∧ n ≤ 14 ∧ n < m ∧ n + m ≤ 30 := by
    fin_cases i <;> simp [StackImmediate.decodePair]
  have hx : UInt8.ofNat x.toNat = x := UInt8.ofNat_toNat
  rw [← hx] at h
  exact check ⟨x.toNat, UInt8.toNat_lt x⟩ n m h

/-- Accepted immediates are neither JUMPDEST nor PUSH1 through PUSH32. -/
theorem single_scanner_safe (x : UInt8) (n : Nat)
    (h : StackImmediate.decodeSingle x = some n) :
    x.toNat ≠ 0x5b ∧ ¬ (0x60 ≤ x.toNat ∧ x.toNat ≤ 0x7f) := by
  simp only [StackImmediate.decodeSingle] at h
  split at h
  · omega
  · simp_all

/-- EXCHANGE's accepted immediates are also safe for PUSH-only scanning. -/
theorem pair_scanner_safe (x : UInt8) (n m : Nat)
    (h : StackImmediate.decodePair x = some (n, m)) :
    x.toNat ≠ 0x5b ∧ ¬ (0x60 ≤ x.toNat ∧ x.toNat ≤ 0x7f) := by
  simp only [StackImmediate.decodePair] at h
  split at h
  · omega
  · simp_all

/-- Missing immediate data reads as zero for every natural program counter. -/
theorem byte_missing (code : ByteArray) (pc : Nat) (h : code.size ≤ pc + 1) :
    StackImmediate.byte code pc = 0 := by
  simp [StackImmediate.byte, PushImmediate.byteAt, Nat.not_lt.mpr h]

end EthLib.EVM.Proofs.StackImmediate
