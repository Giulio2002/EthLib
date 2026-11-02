module

public import EthLib.EVM.Word
import Mathlib.Tactic
import Mathlib.Data.Nat.Log

/-! Mathematical contracts for the Osaka CLZ result. -/

@[expose] public section
namespace EthLib.EVM.Word

/-- The logarithm of a nonzero word is below the word width. -/
theorem log2_toNat_lt_width (x : Word) (nonzero : x.toNat ≠ 0) :
    Nat.log2 x.toNat < 256 := by
  exact (Nat.log2_lt nonzero).2 x.isLt

/-- The result word holds the natural count exactly. -/
theorem countLeadingZeros_toNat (x : Word) :
    (countLeadingZeros x).toNat =
      if x.toNat = 0 then 256 else 255 - Nat.log2 x.toNat := by
  simp only [countLeadingZeros, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  split <;> omega

/-- Zero has all 256 bits clear. -/
theorem countLeadingZeros_zero (x : Word) (h : x.toNat = 0) :
    (countLeadingZeros x).toNat = 256 := by
  simp [countLeadingZeros_toNat, h]

/-- Every result is at most the word width. -/
theorem countLeadingZeros_bound (x : Word) : (countLeadingZeros x).toNat ≤ 256 := by
  rw [countLeadingZeros_toNat]
  split <;> omega

/-- For nonzero input the count plus its mathematical bit length is 256. -/
theorem countLeadingZeros_bitLength (x : Word) (h : x.toNat ≠ 0) :
    (countLeadingZeros x).toNat + (Nat.log2 x.toNat + 1) = 256 := by
  rw [countLeadingZeros_toNat, ite_eq_right h]
  have bound := log2_toNat_lt_width x h
  omega

/-- The count identifies the unique power-of-two interval containing the input. -/
theorem countLeadingZeros_interval (x : Word) (h : x.toNat ≠ 0) :
    2 ^ (255 - (countLeadingZeros x).toNat) ≤ x.toNat ∧
      x.toNat < 2 ^ (256 - (countLeadingZeros x).toNat) := by
  have bound := log2_toNat_lt_width x h
  have value := countLeadingZeros_bitLength x h
  have a : 255 - (countLeadingZeros x).toNat = Nat.log2 x.toNat := by omega
  have b : 256 - (countLeadingZeros x).toNat = Nat.log2 x.toNat + 1 := by omega
  rw [a, b]
  exact ⟨Nat.log2_self_le h, Nat.lt_log2_self⟩

/-- For a nonzero input, an interval determines the count in both directions. -/
theorem countLeadingZeros_interval_iff (x : Word) (h : x.toNat ≠ 0) (k : Nat)
    (hk : k < 256) :
    (countLeadingZeros x).toNat = k ↔
      2 ^ (255 - k) ≤ x.toNat ∧ x.toNat < 2 ^ (256 - k) := by
  constructor
  · intro eq
    simpa [eq] using countLeadingZeros_interval x h
  · rintro ⟨lower, upper⟩
    have l : 255 - k ≤ Nat.log2 x.toNat := (Nat.le_log2 h).2 lower
    have u : Nat.log2 x.toNat < 256 - k := (Nat.log2_lt h).2 upper
    have value := countLeadingZeros_bitLength x h
    omega

/-- The full-width count occurs exactly for zero. -/
theorem countLeadingZeros_full_iff (x : Word) :
    (countLeadingZeros x).toNat = 256 ↔ x.toNat = 0 := by
  constructor
  · intro result
    by_contra h
    have value := countLeadingZeros_bitLength x h
    omega
  · exact countLeadingZeros_zero x

/-- An independent interval specification of a CLZ result word. -/
def CountLeadingZerosSpec (x result : Word) : Prop :=
  (x.toNat = 0 ∧ result.toNat = 256) ∨
    (x.toNat ≠ 0 ∧ result.toNat < 256 ∧
      2 ^ (255 - result.toNat) ≤ x.toNat ∧
      x.toNat < 2 ^ (256 - result.toNat))

/-- The executable result is the unique word satisfying the interval specification. -/
theorem countLeadingZeros_spec (x result : Word) :
    CountLeadingZerosSpec x result ↔ result = countLeadingZeros x := by
  constructor
  · intro spec
    apply BitVec.eq_of_toNat_eq
    rcases spec with ⟨zero, eq⟩ | ⟨nonzero, bound, lower, upper⟩
    · rw [countLeadingZeros_zero x zero]; exact eq
    · exact ((countLeadingZeros_interval_iff x nonzero result.toNat bound).2 ⟨lower, upper⟩).symm
  · intro eq
    subst result
    by_cases zero : x.toNat = 0
    · exact Or.inl ⟨zero, countLeadingZeros_zero x zero⟩
    · have bound := countLeadingZeros_bound x
      have notFull : (countLeadingZeros x).toNat ≠ 256 := by
        intro full
        exact zero ((countLeadingZeros_full_iff x).1 full)
      have interval := countLeadingZeros_interval x zero
      exact Or.inr ⟨zero, by omega, interval⟩

end EthLib.EVM.Word
