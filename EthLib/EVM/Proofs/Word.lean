module

public import EthLib.EVM.Word

/-!
# EVM word addition laws

These statements concern unsigned values and arithmetic results only.
The boundary examples pin arithmetic identities, not external execution test vectors.
-/

@[expose] public section

namespace EthLib.EVM.Proofs.Word

open EthLib.EVM
open EthLib.EVM.Word

/-- Every word's unsigned value lies below the arithmetic modulus. -/
theorem toNat_lt (a : Word) : a.toNat < modulus := a.isLt

/-- The constructor preserves every in-range natural number exactly. -/
theorem ofNat_ok (n : Nat) (h : n < modulus) :
    ofNat n = .ok (BitVec.ofNatLT n h) := by
  simp only [ofNat, dite_eq_left h]

/-- The constructor rejects every out-of-range natural number. -/
theorem ofNat_error (n : Nat) (h : modulus ≤ n) :
    ofNat n = .error .outOfRange := by
  simp only [ofNat, dite_eq_right (Nat.not_lt.mpr h)]

/-- The unsigned result is exactly the Yellow Paper's modular sum. -/
theorem toNat_add (a b : Word) :
    (add a b).toNat = (a.toNat + b.toNat) % modulus := by
  exact BitVec.toNat_ofNat _ _

/-- Addition preserves the word range, including when the integer sum overflows. -/
theorem add_lt (a b : Word) : (add a b).toNat < modulus := toNat_lt _

/-- A sum below the modulus has no wraparound. -/
theorem add_no_wrap (a b : Word) (h : a.toNat + b.toNat < modulus) :
    (add a b).toNat = a.toNat + b.toNat := by
  rw [toNat_add, Nat.mod_eq_of_lt h]

/-- A sum at least the modulus wraps by subtracting it once.

Two word values sum to less than twice the modulus.
-/
theorem add_wrap (a b : Word) (h : modulus ≤ a.toNat + b.toNat) :
    (add a b).toNat = a.toNat + b.toNat - modulus := by
  have ha := toNat_lt a
  have hb := toNat_lt b
  rw [toNat_add]
  -- The range bounds exclude a second wrap.
  simp only [modulus] at *
  omega

/-- The order of the operands does not change the result. -/
theorem add_comm (a b : Word) : add a b = add b a := by
  apply BitVec.eq_of_toNat_eq
  simp only [toNat_add, Nat.add_comm]

/-- Grouping three additions does not change the result. -/
theorem add_assoc (a b c : Word) : add (add a b) c = add a (add b c) := by
  apply BitVec.eq_of_toNat_eq
  -- Each intermediate remainder differs from its sum by a multiple of the modulus.
  simp only [toNat_add, modulus]
  omega

/-- Zero is a right identity. -/
theorem add_zero (a : Word) : add a 0 = a := by
  apply BitVec.eq_of_toNat_eq
  -- Zero contributes no value, and the remaining operand is already in range.
  change (a.toNat + 0) % modulus = a.toNat
  simpa only [Nat.add_zero] using Nat.mod_eq_of_lt (toNat_lt a)

/-- Zero is a left identity. -/
theorem zero_add (a : Word) : add 0 a = a := by
  rw [add_comm, add_zero]

/-- The largest in-range input is accepted unchanged. -/
theorem ofNat_max : ofNat (modulus - 1) =
    .ok (BitVec.ofNatLT (modulus - 1) (by decide)) := by
  apply ofNat_ok

/-- The first out-of-range input is rejected. -/
theorem ofNat_modulus : ofNat modulus = .error .outOfRange :=
  ofNat_error _ (Nat.le_refl _)

/-- One plus one pins an ordinary sum, with no wraparound. -/
theorem one_add_one : add 1 1 = (2 : Word) := by decide

/-- The largest word plus one wraps exactly to zero. -/
theorem max_add_one : add (BitVec.ofNatLT (modulus - 1) (by decide)) 1 = 0 := by
  decide

/-- Two largest words wrap to the second-largest word. -/
theorem max_add_max :
    add (BitVec.ofNatLT (modulus - 1) (by decide))
      (BitVec.ofNatLT (modulus - 1) (by decide)) =
    BitVec.ofNatLT (modulus - 2) (by decide) := by
  decide

end EthLib.EVM.Proofs.Word
