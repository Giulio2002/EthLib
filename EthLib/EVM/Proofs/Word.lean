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

/-- The reference modulus is positive, so modular reduction preserves its bound. -/
theorem modulus_pos : 0 < modulus := by decide

/-- Unsigned observation distinguishes every pair of words. -/
theorem toNat_injective (a b : Word) : a.toNat = b.toNat ↔ a = b := by
  constructor
  · exact BitVec.eq_of_toNat_eq
  · exact congrArg BitVec.toNat

/-- Success characterizes both the accepted range and the exact returned value. -/
theorem ofNat_ok_iff (n : Nat) (w : Word) :
    ofNat n = .ok w ↔ n < modulus ∧ w.toNat = n := by
  by_cases h : n < modulus
  · rw [ofNat_ok n h]
    -- The successful branch contains the bounded input without reduction.
    simp only [Except.ok.injEq, h, true_and]
    constructor
    · intro hw
      rw [← hw]
      rfl
    · intro hw
      apply BitVec.eq_of_toNat_eq
      exact hw.symm
  · rw [ofNat_error n (Nat.le_of_not_gt h)]
    simp [h]

/-- Some output exists exactly when the input is in range. -/
theorem ofNat_success_iff (n : Nat) :
    (∃ w, ofNat n = .ok w) ↔ n < modulus := by
  constructor
  · rintro ⟨w, hw⟩
    exact ((ofNat_ok_iff n w).mp hw).1
  · intro h
    exact ⟨_, ofNat_ok n h⟩

/-- The sole error occurs exactly for out-of-range input. -/
theorem ofNat_error_iff (n : Nat) :
    ofNat n = .error .outOfRange ↔ modulus ≤ n := by
  by_cases h : n < modulus
  · rw [ofNat_ok n h]
    simp [Nat.not_le.mpr h]
  · rw [ofNat_error n (Nat.le_of_not_gt h)]
    simp [Nat.le_of_not_gt h]

/-- Observing and checking any word returns that same word. -/
theorem ofNat_toNat (w : Word) : ofNat w.toNat = .ok w := by
  exact (ofNat_ok_iff _ _).mpr ⟨toNat_lt w, rfl⟩

/-! A mathematical model independent of BitVec and the executable operations.

The bound follows Yellow Paper section 9.1.
Addition follows Appendix H.2's arithmetic preamble and ADD result equation.
The checked constructor expresses the library boundary policy.
-/
namespace Reference

/-- The model represents a word by a bounded natural number. -/
abbrev Value := { n : Nat // n < 2 ^ 256 }

/-- Mathematical addition on bounded naturals, with modular reduction. -/
def add (a b : Value) : Value :=
  ⟨(a.val + b.val) % (2 ^ 256), Nat.mod_lt _ (by decide)⟩

/-- The model accepts precisely the bounded naturals. -/
def ofNat (n : Nat) : Except InputError Value :=
  if h : n < 2 ^ 256 then .ok ⟨n, h⟩ else .error .outOfRange

end Reference

/-- Interpret a concrete word as a bounded natural number. -/
def decode (w : Word) : Reference.Value := ⟨w.toNat, toNat_lt w⟩

/-- Represent a bounded natural number without modular reduction. -/
def encode (n : Reference.Value) : Word := BitVec.ofNatLT n.val n.property

/-- Every mathematical value survives representation and observation. -/
theorem decode_encode (n : Reference.Value) : decode (encode n) = n := by
  apply Subtype.ext
  rfl

/-- Every concrete word survives observation and representation. -/
theorem encode_decode (w : Word) : encode (decode w) = w := by
  apply BitVec.eq_of_toNat_eq
  rfl

/-- The interpretation identifies no distinct concrete words. -/
theorem decode_injective : Function.Injective decode := by
  intro a b h
  exact BitVec.eq_of_toNat_eq (congrArg Subtype.val h)

/-- Every bounded natural has a concrete representation. -/
theorem decode_surjective : Function.Surjective decode := by
  intro n
  exact ⟨encode n, decode_encode n⟩

/-- Checked construction refines the independent model on every natural input.

Mapping the success value preserves the exact error as well.
-/
theorem ofNat_refines (n : Nat) :
    (ofNat n).map decode = Reference.ofNat n := by
  by_cases h : n < modulus
  · rw [ofNat_ok n h]
    simp only [Reference.ofNat, show n < 2 ^ 256 from h, dite_true]
    rfl
  · rw [ofNat_error n (Nat.le_of_not_gt h)]
    simp only [Reference.ofNat, show ¬ n < 2 ^ 256 from h, dite_false]
    rfl

/-- Addition refines bounded natural modular arithmetic for every operand pair.

The existing toNat_add theorem supplies the arithmetic fact for all carries.
-/
theorem add_refines (a b : Word) :
    decode (add a b) = Reference.add (decode a) (decode b) := by
  apply Subtype.ext
  exact toNat_add a b

end EthLib.EVM.Proofs.Word
