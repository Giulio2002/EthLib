import EthLib.Cryptography.Proofs.Xmss.KeyGenKatSupport
import Mathlib.Tactic.IntervalCases

/-!
# Proofs: the one-time signature at epoch 7

The reference signature reveals each chain of the epoch-7 one-time key at the height its digit names.

Each theorem below grows one chain from the seed and lands on the revealed value.

So the signature's chain values come from the seed, and the verifier's recovery then gives the leaf.
-/

namespace EthLib.Cryptography.Xmss
open Constants

-- With asynchronous elaboration, memory grows with every theorem: 7.6 GB for the 42 chains at epoch 6.
-- Checked one after another, the whole file peaks at 2.4 GB, as a file with one chain does.
set_option Elab.async false

/-- The one-time signature at epoch 7 over the reference message digits. -/
local notation "sig7" =>
  otsReveal examplePublicKey.publicParam 7 (otsSecretKey examplePublicKey.publicParam exampleSeed 7)
    katDigits

theorem katReveal7_0 : sig7[0] = exampleSignature.chainElements[0] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_1 : sig7[1] = exampleSignature.chainElements[1] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_2 : sig7[2] = exampleSignature.chainElements[2] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_3 : sig7[3] = exampleSignature.chainElements[3] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_4 : sig7[4] = exampleSignature.chainElements[4] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_5 : sig7[5] = exampleSignature.chainElements[5] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_6 : sig7[6] = exampleSignature.chainElements[6] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_7 : sig7[7] = exampleSignature.chainElements[7] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_8 : sig7[8] = exampleSignature.chainElements[8] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_9 : sig7[9] = exampleSignature.chainElements[9] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_10 : sig7[10] = exampleSignature.chainElements[10] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_11 : sig7[11] = exampleSignature.chainElements[11] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_12 : sig7[12] = exampleSignature.chainElements[12] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_13 : sig7[13] = exampleSignature.chainElements[13] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_14 : sig7[14] = exampleSignature.chainElements[14] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_15 : sig7[15] = exampleSignature.chainElements[15] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_16 : sig7[16] = exampleSignature.chainElements[16] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_17 : sig7[17] = exampleSignature.chainElements[17] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_18 : sig7[18] = exampleSignature.chainElements[18] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_19 : sig7[19] = exampleSignature.chainElements[19] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_20 : sig7[20] = exampleSignature.chainElements[20] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_21 : sig7[21] = exampleSignature.chainElements[21] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_22 : sig7[22] = exampleSignature.chainElements[22] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_23 : sig7[23] = exampleSignature.chainElements[23] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_24 : sig7[24] = exampleSignature.chainElements[24] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_25 : sig7[25] = exampleSignature.chainElements[25] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_26 : sig7[26] = exampleSignature.chainElements[26] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_27 : sig7[27] = exampleSignature.chainElements[27] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_28 : sig7[28] = exampleSignature.chainElements[28] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_29 : sig7[29] = exampleSignature.chainElements[29] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_30 : sig7[30] = exampleSignature.chainElements[30] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_31 : sig7[31] = exampleSignature.chainElements[31] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_32 : sig7[32] = exampleSignature.chainElements[32] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_33 : sig7[33] = exampleSignature.chainElements[33] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_34 : sig7[34] = exampleSignature.chainElements[34] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_35 : sig7[35] = exampleSignature.chainElements[35] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_36 : sig7[36] = exampleSignature.chainElements[36] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_37 : sig7[37] = exampleSignature.chainElements[37] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_38 : sig7[38] = exampleSignature.chainElements[38] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_39 : sig7[39] = exampleSignature.chainElements[39] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_40 : sig7[40] = exampleSignature.chainElements[40] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel
theorem katReveal7_41 : sig7[41] = exampleSignature.chainElements[41] := by
  rw [otsReveal_getElem_eq_fast]; decide +kernel

/-- The whole one-time signature, chain by chain. -/
theorem katReveal7 : sig7 = exampleSignature.chainElements := by
  apply Vector.ext
  intro i hi
  change i < 42 at hi
  interval_cases i
  exacts [katReveal7_0, katReveal7_1, katReveal7_2, katReveal7_3, katReveal7_4, katReveal7_5, katReveal7_6, katReveal7_7, katReveal7_8, katReveal7_9, katReveal7_10, katReveal7_11, katReveal7_12, katReveal7_13, katReveal7_14, katReveal7_15, katReveal7_16, katReveal7_17, katReveal7_18, katReveal7_19, katReveal7_20, katReveal7_21, katReveal7_22, katReveal7_23, katReveal7_24, katReveal7_25, katReveal7_26, katReveal7_27, katReveal7_28, katReveal7_29, katReveal7_30, katReveal7_31, katReveal7_32, katReveal7_33, katReveal7_34, katReveal7_35, katReveal7_36, katReveal7_37, katReveal7_38, katReveal7_39, katReveal7_40, katReveal7_41]

/-- The leaf at epoch 7 is the leaf the verifier recovers from the reference signature. -/
theorem katLeaf7_eq : exampleSk.leaves 7 = katLeaf := by
  unfold SecretKey.leaves
  rw [katPublicParam]
  change otsLeaf examplePublicKey.publicParam 7
    (otsPublicKey examplePublicKey.publicParam 7
      (otsSecretKey examplePublicKey.publicParam exampleSeed 7)) = katLeaf
  -- Finishing each revealed chain gives the public key, so recovery gives the same leaf.
  rw [← otsRecover_otsReveal examplePublicKey.publicParam 7
    (otsSecretKey examplePublicKey.publicParam exampleSeed 7) katDigits,
    katReveal7, katRecover, katLeaf_eq]

end EthLib.Cryptography.Xmss
