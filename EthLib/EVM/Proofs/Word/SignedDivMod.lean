module

public import EthLib.EVM.Word.SignedDivMod

/-!
# Signed word arithmetic contracts

The integer model uses natural magnitudes and explicit signs.
It is independent of the concrete bit-vector operations.
-/

@[expose] public section

namespace EthLib.EVM.Proofs.Word.SignedDivMod

open EthLib.EVM

/-- The range of signed 256-bit words. -/
abbrev Value := { n : Int // -(2 ^ 255) ≤ n ∧ n < 2 ^ 255 }

/-- Observe a word as a bounded signed integer. -/
def decode (w : Word) : Value :=
  ⟨Word.signed w, by exact ⟨BitVec.le_toInt w, BitVec.toInt_lt⟩⟩

/-- Represent a bounded signed integer. -/
def encode (n : Value) : Word := Word.ofSigned n.val

/-- Encoding any integer wraps it to the signed two's-complement range. -/
theorem signed_ofSigned (n : Int) :
    Word.signed (Word.ofSigned n) = n.bmod (2 ^ 256) := by
  exact BitVec.toInt_ofInt n

/-- Every bounded integer survives encoding and decoding. -/
theorem decode_encode (n : Value) : decode (encode n) = n := by
  apply Subtype.ext
  exact BitVec.toInt_ofInt_eq_self (by decide) n.property.1 n.property.2

/-- Every word survives decoding and encoding. -/
theorem encode_decode (w : Word) : encode (decode w) = w := by
  exact BitVec.ofInt_toInt

/-- Signed observation is injective. -/
theorem signed_injective : Function.Injective Word.signed := by
  intro a b h
  exact BitVec.eq_of_toInt_eq h

namespace Reference

/-- Truncated quotient, formed from natural magnitudes. -/
def quotient (a b : Int) : Int :=
  let q : Int := (a.natAbs / b.natAbs : Nat)
  if (a < 0) != (b < 0) then -q else q

/-- Signed remainder, formed from natural magnitudes. -/
def remainder (a b : Int) : Int :=
  if b = 0 then 0 else
    let r : Int := (a.natAbs % b.natAbs : Nat)
    if a < 0 then -r else r

end Reference

/-- Truncated division has the reference magnitude and sign. -/
theorem quotient_eq_tdiv (a b : Int) : Reference.quotient a b = a.tdiv b := by
  rcases Int.eq_nat_or_neg a with ⟨a, ha | ha⟩ <;>
    rcases Int.eq_nat_or_neg b with ⟨b, hb | hb⟩ <;>
    subst_vars <;> by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    simp_all [Reference.quotient] <;> omega

/-- Truncated remainder has the reference magnitude and sign for nonzero divisors. -/
theorem remainder_eq_tmod (a b : Int) (h : b ≠ 0) :
    Reference.remainder a b = a.tmod b := by
  rcases Int.eq_nat_or_neg a with ⟨a, ha | ha⟩ <;>
    rcases Int.eq_nat_or_neg b with ⟨b, hb | hb⟩ <;>
    subst_vars <;> by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    simp_all [Reference.remainder, ← Int.ofNat_tmod] <;> omega

/-- SDIV refines the integer quotient, reduced to signed word range. -/
theorem sdiv_refines (a b : Word) :
    Word.signed (Word.sdiv a b) = (Reference.quotient (Word.signed a) (Word.signed b)).bmod (2 ^ 256) := by
  rw [quotient_eq_tdiv]
  exact BitVec.toInt_sdiv a b

/-- SMOD refines the integer remainder, including a zero divisor. -/
theorem smod_refines (a b : Word) :
    Word.signed (Word.smod a b) = Reference.remainder (Word.signed a) (Word.signed b) := by
  by_cases h : b = 0
  · subst b
    simp [Word.smod, Word.signed, Reference.remainder]
  · have hb : Word.signed b ≠ 0 := by
      intro hb
      apply h
      apply BitVec.eq_of_toInt_eq
      simpa [Word.signed] using hb
    rw [remainder_eq_tmod _ _ hb]
    change BitVec.toInt (if b = (0 : Word) then 0 else BitVec.srem a b) = _
    rw [ite_eq_right h, BitVec.toInt_srem]
    rfl

/-- Two's-complement interpretation subtracts the modulus when the sign bit is set. -/
theorem signed_equation (a : Word) : Word.signed a =
    if 2 * a.toNat < 2 ^ 256 then (a.toNat : Int)
    else (a.toNat : Int) - (2 ^ 256 : Nat) := by
  exact BitVec.toInt_eq_toNat_cond a

/-- The signed interpretation is bounded on both sides. -/
theorem signed_range (a : Word) : -(2 ^ 255 : Int) ≤ Word.signed a ∧
    Word.signed a < 2 ^ 255 := (decode a).property

/-- SDIV is the encoded reference quotient for every pair of words. -/
theorem sdiv_word_refines (a b : Word) : Word.sdiv a b =
    Word.ofSigned (Reference.quotient (Word.signed a) (Word.signed b)) := by
  apply signed_injective
  rw [sdiv_refines]
  exact (BitVec.toInt_ofInt _).symm

/-- SMOD is the encoded reference remainder for every pair of words. -/
theorem smod_word_refines (a b : Word) : Word.smod a b =
    Word.ofSigned (Reference.remainder (Word.signed a) (Word.signed b)) := by
  apply signed_injective
  rw [smod_refines]
  have h := signed_range (Word.smod a b)
  rw [smod_refines] at h
  exact (BitVec.toInt_ofInt_eq_self (by decide) h.1 h.2).symm

/-- Away from signed overflow, SDIV is exactly truncated integer division. -/
theorem signed_sdiv (a b : Word)
    (h : a ≠ BitVec.intMin 256 ∨ b ≠ (-1 : Word)) :
    Word.signed (Word.sdiv a b) = (Word.signed a).tdiv (Word.signed b) := by
  exact BitVec.toInt_sdiv_of_ne_or_ne a b h

/-- A nonzero divisor gives exactly the signed truncated remainder. -/
theorem signed_smod (a b : Word) (h : b ≠ 0) :
    Word.signed (Word.smod a b) = (Word.signed a).tmod (Word.signed b) := by
  have hz : Word.signed b ≠ 0 := by
    intro hz
    apply h
    apply signed_injective
    simpa [Word.signed] using hz
  rw [smod_refines, remainder_eq_tmod _ _ hz]

/-- The non-overflow quotient magnitude is the quotient of operand magnitudes. -/
theorem sdiv_magnitude (a b : Word)
    (h : a ≠ BitVec.intMin 256 ∨ b ≠ (-1 : Word)) :
    (Word.signed (Word.sdiv a b)).natAbs =
      (Word.signed a).natAbs / (Word.signed b).natAbs := by
  rw [signed_sdiv a b h, Int.natAbs_tdiv]
  rfl

/-- Equal operand signs give a nonnegative quotient outside overflow. -/
theorem sdiv_nonneg (a b : Word)
    (h : a ≠ BitVec.intMin 256 ∨ b ≠ (-1 : Word))
    (hs : (0 ≤ Word.signed a ∧ 0 ≤ Word.signed b) ∨
      (Word.signed a ≤ 0 ∧ Word.signed b ≤ 0)) :
    0 ≤ Word.signed (Word.sdiv a b) := by
  rw [signed_sdiv a b h]
  rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Int.tdiv_nonneg ha hb
  · exact Int.tdiv_nonneg_of_nonpos_of_nonpos ha hb

/-- Opposite operand signs give a nonpositive quotient outside overflow. -/
theorem sdiv_nonpos (a b : Word)
    (h : a ≠ BitVec.intMin 256 ∨ b ≠ (-1 : Word))
    (hs : (0 ≤ Word.signed a ∧ Word.signed b ≤ 0) ∨
      (Word.signed a ≤ 0 ∧ 0 ≤ Word.signed b)) :
    Word.signed (Word.sdiv a b) ≤ 0 := by
  rw [signed_sdiv a b h]
  rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Int.tdiv_nonpos_of_nonneg_of_nonpos ha hb
  · have hn : 0 ≤ (-Word.signed a).tdiv (Word.signed b) :=
      Int.tdiv_nonneg (by omega) hb
    rw [Int.neg_tdiv] at hn
    omega

/-- The remainder magnitude is the natural remainder of operand magnitudes. -/
theorem smod_magnitude_eq (a b : Word) (h : b ≠ 0) :
    (Word.signed (Word.smod a b)).natAbs =
      (Word.signed a).natAbs % (Word.signed b).natAbs := by
  rw [signed_smod a b h, Int.natAbs_tmod]

/-- A zero divisor produces zero for SDIV. -/
theorem sdiv_zero (a : Word) : Word.sdiv a 0 = 0 := by
  apply signed_injective
  rw [sdiv_refines, quotient_eq_tdiv]
  simp [Word.signed]

/-- A zero divisor produces zero for SMOD. -/
theorem smod_zero (a : Word) : Word.smod a 0 = 0 := by
  simp [Word.smod]

/-- The only signed quotient overflow wraps to the signed minimum word. -/
theorem sdiv_min_neg_one : Word.sdiv (BitVec.intMin 256) (-1) = BitVec.intMin 256 := by
  exact BitVec.intMin_sdiv_neg_one

/-- The overflow result represents the signed minimum. -/
theorem signed_sdiv_min_neg_one :
    Word.signed (Word.sdiv (BitVec.intMin 256) (-1)) = -(2 ^ 255 : Int) := by
  rw [sdiv_min_neg_one]
  exact BitVec.toInt_intMin_of_pos (by decide)

/-- For a nonzero divisor, the remainder magnitude is strictly less than the divisor magnitude. -/
theorem smod_magnitude (a b : Word) (h : b ≠ 0) :
    (Word.signed (Word.smod a b)).natAbs < (Word.signed b).natAbs := by
  have hb : Word.signed b ≠ 0 := by
    intro hz
    apply h
    apply signed_injective
    simpa [Word.signed] using hz
  rw [smod_refines, remainder_eq_tmod _ _ hb, Int.natAbs_tmod]
  exact Nat.mod_lt _ (Int.natAbs_pos.mpr hb)

/-- A nonnegative numerator has a nonnegative signed remainder. -/
theorem smod_nonneg (a b : Word) (ha : 0 ≤ Word.signed a) :
    0 ≤ Word.signed (Word.smod a b) := by
  by_cases hb : b = 0
  · subst b
    rw [smod_zero]
    simp [Word.signed]
  · have h : Word.signed b ≠ 0 := by
      intro hz
      apply hb
      apply signed_injective
      simpa [Word.signed] using hz
    rw [smod_refines, remainder_eq_tmod _ _ h]
    exact Int.tmod_nonneg _ ha

/-- A nonpositive numerator has a nonpositive signed remainder. -/
theorem smod_nonpos (a b : Word) (ha : Word.signed a ≤ 0) :
    Word.signed (Word.smod a b) ≤ 0 := by
  by_cases hb : b = 0
  · subst b
    rw [smod_zero]
    simp [Word.signed]
  · have h : Word.signed b ≠ 0 := by
      intro hz
      apply hb
      apply signed_injective
      simpa [Word.signed] using hz
    rw [smod_refines, remainder_eq_tmod _ _ h]
    have hn : 0 ≤ (-Word.signed a).tmod (Word.signed b) := Int.tmod_nonneg _ (by omega)
    rw [Int.neg_tmod] at hn
    omega

/-- Outside the overflow case, quotient and remainder reconstruct the numerator. -/
theorem quotient_remainder (a b : Word) (hb : b ≠ 0)
    (hover : a ≠ BitVec.intMin 256 ∨ b ≠ (-1 : Word)) :
    Word.signed (Word.smod a b) + Word.signed b * Word.signed (Word.sdiv a b) =
      Word.signed a := by
  have hz : Word.signed b ≠ 0 := by
    intro hz
    apply hb
    apply signed_injective
    simpa [Word.signed] using hz
  rw [smod_refines, remainder_eq_tmod _ _ hz]
  change (BitVec.toInt a).tmod (BitVec.toInt b) +
    BitVec.toInt b * BitVec.toInt (BitVec.sdiv a b) = BitVec.toInt a
  rw [BitVec.toInt_sdiv_of_ne_or_ne a b hover]
  exact Int.tmod_add_mul_tdiv _ _

/-- A negative numerator and positive divisor truncate toward zero. -/
theorem example_neg_seven_div_three : Word.sdiv (Word.ofSigned (-7)) (Word.ofSigned 3) =
    Word.ofSigned (-2) := by decide

/-- A positive numerator and negative divisor truncate toward zero. -/
theorem example_seven_div_neg_three : Word.sdiv (Word.ofSigned 7) (Word.ofSigned (-3)) =
    Word.ofSigned (-2) := by decide

/-- A negative numerator produces a negative nonzero remainder. -/
theorem example_neg_seven_mod_three : Word.smod (Word.ofSigned (-7)) (Word.ofSigned 3) =
    Word.ofSigned (-1) := by decide

end EthLib.EVM.Proofs.Word.SignedDivMod
