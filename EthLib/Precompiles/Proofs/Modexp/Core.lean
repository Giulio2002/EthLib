import EthLib.Precompiles.Proofs.Modexp.Bytes
import EthLib.Precompiles.Proofs.Modexp.PowMod
import EthLib.Precompiles.Modexp.Core

/-!
# Proofs: `Core`

The precompile does what EIP-198 says.

- The output is `base ^ exponent mod modulus`, or `0` when the modulus is `0`.
- The output has exactly `len_mod` bytes.
- A short input is read as if padded with zeros, and excess data is ignored.
- A length above 1024 fails before gas is charged.
  Otherwise the call fails exactly when the gas given is below the price.
-/

namespace EthLib.Precompiles.Modexp

open EthLib.Precompiles.Modexp.Constants

/-- The big-endian integer held by the output bytes. -/
def outputNat (bytes : ByteArray) : Nat :=
  bytesToNat bytes.data.toList

/-- The bytes `compute` returns are the bytes `natToBytes` writes. -/
theorem compute_data (data : ByteArray) (l : Lengths) :
    (compute data l).data.toList
      = natToBytes l.modulus
          (if readNat data l.modulusStart l.modulus = 0 then 0
           else powMod (readNat data BASE_OFFSET l.base) (readNat data l.exponentStart l.exponent)
                  (readNat data l.modulusStart l.modulus)) := by
  simp [compute]

/-- The output has exactly `len_mod` bytes.

EIP-198: "returns an output ... as a byte array with the same length as the modulus". -/
theorem compute_size (data : ByteArray) (l : Lengths) : (compute data l).size = l.modulus := by
  have h := congrArg List.length (compute_data data l)
  rw [natToBytes_length, Array.length_toList] at h
  exact h

/-- The output is the mathematical `base ^ exponent mod modulus`.

EIP-198: "returns an output `(BASE**EXPONENT) % MODULUS`".
The case of a zero modulus is not in EIP-198.
It is the `modulus == 0` branch of `modexp` in the execution-specs module. -/
theorem compute_eq_pow_mod (data : ByteArray) (l : Lengths) :
    outputNat (compute data l)
      = if readNat data l.modulusStart l.modulus = 0 then 0
        else readNat data BASE_OFFSET l.base ^ readNat data l.exponentStart l.exponent
              % readNat data l.modulusStart l.modulus := by
  unfold outputNat
  rw [compute_data]
  split
  · -- A zero modulus gives the number 0 (written as zero bytes).
    rw [bytesToNat_natToBytes, Nat.zero_mod]
  · next h =>
    -- No truncation: the remainder is below the modulus, which fits in `len_mod` bytes.
    rw [bytesToNat_natToBytes_of_lt, powMod_eq]
    rw [powMod_eq]
    exact Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero h)) (readNat_lt _ _ _)

/-- A zero modulus gives `len_mod` zero bytes. -/
theorem compute_modulus_zero (data : ByteArray) (l : Lengths)
    (h : readNat data l.modulusStart l.modulus = 0) :
    (compute data l).data = Array.replicate l.modulus 0 := by
  have h1 : natToBytes l.modulus 0 = List.replicate l.modulus 0 := by
    generalize l.modulus = len
    induction len with
    | zero => rfl
    | succ len ih => simp [natToBytes, ih, List.replicate_succ']
  have := compute_data data l
  rw [if_pos h, h1] at this
  exact Array.toList_inj.mp (by simpa using this)

/-- An empty modulus gives an empty output, even with an empty base.

This covers the early return when both `base_length` and `modulus_length` are zero. -/
theorem compute_modulus_len_zero (data : ByteArray) (l : Lengths) (h : l.modulus = 0) :
    (compute data l).size = 0 := by
  rw [compute_size, h]

/-! ## Padding and excess -/

/-- Padding the call data with zeros changes the lengths read. -/
theorem parseLengths_append_zeros (data : ByteArray) (n : Nat) :
    parseLengths (data ++ ByteArray.mk (Array.replicate n 0)) = parseLengths data := by
  simp [parseLengths, readNat_append_zeros]

/-- Padding the call data with zeros does not change the gas. -/
theorem requiredGas_append_zeros (data : ByteArray) (n : Nat) (l : Lengths) :
    requiredGas (data ++ ByteArray.mk (Array.replicate n 0)) l = requiredGas data l := by
  simp [requiredGas, exponentHead, readNat_append_zeros]

/-- Padding the call data with zeros does not change the output. -/
theorem compute_append_zeros (data : ByteArray) (n : Nat) (l : Lengths) :
    compute (data ++ ByteArray.mk (Array.replicate n 0)) l = compute data l := by
  simp [compute, readNat_append_zeros]

/-- Padding the call data with zeros does not change the result of the precompile.

EIP-198: "Call data is assumed to be infinitely right-padded with zero bytes". -/
theorem modexp_append_zeros (data : ByteArray) (n gas : Nat) :
    modexp (data ++ ByteArray.mk (Array.replicate n 0)) gas = modexp data gas := by
  simp [modexp, parseLengths_append_zeros, requiredGas_append_zeros, compute_append_zeros]

/-- Two inputs that agree on the bytes the lengths describe give the same result.

The bytes described are the three headers, `BASE`, `EXPONENT` and `MODULUS`.
A byte past the end counts as zero.
This covers excess data, which EIP-198 says "is ignored", and short input. -/
theorem modexp_congr {d₁ d₂ : ByteArray} (gas : Nat)
    (h : ∀ i, i < BASE_OFFSET + (parseLengths d₁).base + (parseLengths d₁).exponent
                + (parseLengths d₁).modulus → byteAt d₁ i = byteAt d₂ i) :
    modexp d₁ gas = modexp d₂ gas := by
  -- The lengths come from the first 96 bytes, which lie inside the covered range.
  have hl : parseLengths d₁ = parseLengths d₂ := by
    have hh : ∀ i, i < 96 → byteAt d₁ i = byteAt d₂ i := fun i hi => h i (by
      unfold BASE_OFFSET LENGTH_HEADER_BYTES; omega)
    simp only [parseLengths, LENGTH_HEADER_BYTES]
    have e : ∀ s, s + 32 ≤ 96 → readNat d₁ s 32 = readNat d₂ s 32 := fun s hs =>
      readNat_congr fun i h1 h2 => hh i (by omega)
    simp [e 0 (by omega), e 32 (by omega), e 64 (by omega)]
  -- Compare each window the output depends on.
  have hb : readNat d₁ BASE_OFFSET (parseLengths d₁).base
      = readNat d₂ BASE_OFFSET (parseLengths d₁).base :=
    readNat_congr fun i h1 h2 => h i (by unfold BASE_OFFSET LENGTH_HEADER_BYTES at *; omega)
  have he : readNat d₁ (parseLengths d₁).exponentStart (parseLengths d₁).exponent
      = readNat d₂ (parseLengths d₁).exponentStart (parseLengths d₁).exponent :=
    readNat_congr fun i h1 h2 => h i (by
      unfold Lengths.exponentStart BASE_OFFSET LENGTH_HEADER_BYTES at *; omega)
  have hm : readNat d₁ (parseLengths d₁).modulusStart (parseLengths d₁).modulus
      = readNat d₂ (parseLengths d₁).modulusStart (parseLengths d₁).modulus :=
    readNat_congr fun i h1 h2 => h i (by
      unfold Lengths.modulusStart Lengths.exponentStart BASE_OFFSET LENGTH_HEADER_BYTES at *; omega)
  have hx : exponentHead d₁ (parseLengths d₁) = exponentHead d₂ (parseLengths d₁) :=
    readNat_congr fun i h1 h2 => h i (by
      unfold Lengths.exponentStart BASE_OFFSET LENGTH_HEADER_BYTES EXPONENT_HEAD_BYTES at *
      omega)
  have hg : requiredGas d₁ (parseLengths d₁) = requiredGas d₂ (parseLengths d₁) := by
    simp [requiredGas, hx]
  have hc : compute d₁ (parseLengths d₁) = compute d₂ (parseLengths d₁) := by
    simp [compute, hb, he, hm]
  unfold modexp
  dsimp only
  rw [← hl, hg, hc]

/-- Data after the last byte the lengths describe is ignored.

EIP-198: "excess data is ignored". -/
theorem modexp_append_excess (data extra : ByteArray) (gas : Nat)
    (h : BASE_OFFSET + (parseLengths data).base + (parseLengths data).exponent
          + (parseLengths data).modulus ≤ data.size) :
    modexp (data ++ extra) gas = modexp data gas := by
  symm
  apply modexp_congr
  intro i hi
  have hi' : i < data.size := Nat.lt_of_lt_of_le hi h
  simp [byteAt, ByteArray.data_append, Array.getD_eq_getD_getElem?,
    Array.getElem?_append_left (by simpa using hi')]

/-! ## Bounds and gas -/

/-- A base length above 1024 fails before gas is charged, whatever the gas.

EIP-7823: "If any of these inputs are larger than the limit, the precompile execution stops,
returns an error, and consumes all gas". -/
theorem modexp_base_too_large (data : ByteArray) (gas : Nat)
    (h : MAX_LENGTH_BYTES < (parseLengths data).base) :
    modexp data gas = .error (.lengthTooLarge .base (parseLengths data).base) := by
  simp [modexp, checkLengths, h]

/-- An exponent length above 1024 fails before gas is charged, whatever the gas,
when the base length is in bounds. -/
theorem modexp_exponent_too_large (data : ByteArray) (gas : Nat)
    (hb : (parseLengths data).base ≤ MAX_LENGTH_BYTES)
    (h : MAX_LENGTH_BYTES < (parseLengths data).exponent) :
    modexp data gas = .error (.lengthTooLarge .exponent (parseLengths data).exponent) := by
  simp [modexp, checkLengths, Nat.not_lt.mpr hb, h]

/-- A modulus length above 1024 fails before gas is charged, whatever the gas,
when the base and exponent lengths are in bounds. -/
theorem modexp_modulus_too_large (data : ByteArray) (gas : Nat)
    (hb : (parseLengths data).base ≤ MAX_LENGTH_BYTES)
    (he : (parseLengths data).exponent ≤ MAX_LENGTH_BYTES)
    (h : MAX_LENGTH_BYTES < (parseLengths data).modulus) :
    modexp data gas = .error (.lengthTooLarge .modulus (parseLengths data).modulus) := by
  simp [modexp, checkLengths, Nat.not_lt.mpr hb, Nat.not_lt.mpr he, h]

/-- With every length in bounds, the call fails exactly when the gas is below the price. -/
theorem modexp_out_of_gas (data : ByteArray) (gas : Nat)
    (hb : (parseLengths data).base ≤ MAX_LENGTH_BYTES)
    (he : (parseLengths data).exponent ≤ MAX_LENGTH_BYTES)
    (hm : (parseLengths data).modulus ≤ MAX_LENGTH_BYTES)
    (hg : gas < requiredGas data (parseLengths data)) :
    modexp data gas = .error (.outOfGas (requiredGas data (parseLengths data)) gas) := by
  simp [modexp, checkLengths, Nat.not_lt.mpr hb, Nat.not_lt.mpr he, Nat.not_lt.mpr hm, hg]

/-- With every length in bounds and enough gas, the call returns the computed output. -/
theorem modexp_ok (data : ByteArray) (gas : Nat)
    (hb : (parseLengths data).base ≤ MAX_LENGTH_BYTES)
    (he : (parseLengths data).exponent ≤ MAX_LENGTH_BYTES)
    (hm : (parseLengths data).modulus ≤ MAX_LENGTH_BYTES)
    (hg : requiredGas data (parseLengths data) ≤ gas) :
    modexp data gas = .ok (compute data (parseLengths data)) := by
  simp [modexp, checkLengths, Nat.not_lt.mpr hb, Nat.not_lt.mpr he, Nat.not_lt.mpr hm,
    Nat.not_lt.mpr hg]

/-- A successful call returns exactly `len_mod` bytes. -/
theorem modexp_ok_size {data : ByteArray} {gas : Nat} {out : ByteArray}
    (h : modexp data gas = .ok out) : out.size = (parseLengths data).modulus := by
  unfold modexp at h
  dsimp only at h
  -- The only success path returns `compute`.
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      exact compute_size _ _

end EthLib.Precompiles.Modexp
