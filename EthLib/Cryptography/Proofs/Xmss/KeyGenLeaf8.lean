import EthLib.Cryptography.Proofs.Xmss.KeyGenKatSupport
import Mathlib.Tactic.IntervalCases

/-!
# Proofs: the one-time public key at epoch 8

The leaf at epoch 8 is the hash of the 42 chain ends of its one-time public key.

Each chain end is seven hashes from a secret value, itself one hash of the seed.

The chain ends below are intermediate values of key generation, computed by the code itself.

They are not checks on their own.

They split one large kernel evaluation into one evaluation per chain.

The check is that the root they lead to is the reference public key.
-/

namespace EthLib.Cryptography.Xmss
open Constants

-- With asynchronous elaboration, memory grows with every theorem: 7.6 GB for the 42 chains at epoch 6.
-- Checked one after another, the whole file peaks at 2.4 GB, as a file with one chain does.
set_option Elab.async false

/-- The one-time public key at epoch 8. -/
local notation "pk8" =>
  otsPublicKey examplePublicKey.publicParam 8 (otsSecretKey examplePublicKey.publicParam exampleSeed 8)

/-- The 42 chain ends at epoch 8. -/
def katPublic8 : Vector Digest V := #v[
  #v[156, 120, 193, 150, 204, 221, 171, 63, 73, 168, 127, 2, 112, 144, 153, 182],
  #v[32, 121, 48, 122, 242, 115, 209, 15, 136, 155, 122, 13, 137, 213, 228, 127],
  #v[20, 49, 121, 54, 243, 243, 14, 147, 18, 23, 60, 231, 96, 95, 103, 70],
  #v[162, 135, 212, 19, 162, 144, 238, 200, 126, 176, 97, 78, 68, 29, 38, 130],
  #v[177, 241, 165, 88, 35, 224, 59, 199, 217, 80, 19, 181, 52, 133, 188, 225],
  #v[28, 251, 34, 233, 247, 252, 13, 104, 136, 35, 99, 28, 172, 6, 123, 49],
  #v[154, 152, 9, 153, 115, 129, 152, 165, 119, 189, 198, 59, 90, 63, 230, 117],
  #v[92, 186, 78, 96, 66, 117, 51, 125, 220, 158, 88, 247, 151, 215, 81, 41],
  #v[72, 59, 246, 83, 66, 63, 37, 64, 1, 210, 247, 233, 246, 112, 215, 166],
  #v[67, 139, 255, 225, 38, 224, 79, 120, 194, 242, 161, 158, 178, 23, 231, 120],
  #v[109, 204, 84, 116, 200, 3, 80, 243, 250, 113, 119, 89, 135, 156, 108, 172],
  #v[136, 102, 197, 151, 224, 82, 86, 167, 75, 252, 240, 198, 38, 71, 177, 135],
  #v[218, 22, 85, 52, 133, 242, 7, 228, 64, 102, 131, 128, 211, 207, 213, 195],
  #v[229, 178, 228, 19, 213, 157, 35, 245, 166, 68, 241, 137, 191, 145, 129, 141],
  #v[177, 131, 243, 218, 69, 10, 221, 249, 2, 113, 59, 70, 99, 12, 226, 58],
  #v[227, 122, 84, 254, 117, 22, 247, 124, 114, 165, 137, 167, 11, 196, 86, 70],
  #v[88, 131, 112, 192, 82, 222, 187, 203, 145, 141, 112, 99, 34, 229, 52, 12],
  #v[200, 205, 255, 16, 177, 181, 176, 13, 164, 145, 223, 162, 167, 144, 94, 85],
  #v[121, 249, 228, 225, 135, 224, 134, 49, 133, 4, 83, 218, 98, 215, 22, 250],
  #v[143, 48, 103, 59, 68, 56, 82, 64, 198, 0, 30, 107, 212, 133, 126, 187],
  #v[182, 82, 104, 149, 30, 251, 167, 228, 7, 207, 172, 57, 86, 57, 83, 63],
  #v[185, 107, 68, 128, 141, 83, 175, 160, 20, 241, 114, 181, 122, 172, 40, 138],
  #v[147, 114, 99, 108, 235, 68, 79, 83, 215, 226, 254, 123, 5, 230, 64, 47],
  #v[192, 52, 239, 133, 19, 177, 197, 171, 47, 243, 150, 207, 242, 20, 203, 126],
  #v[188, 13, 173, 79, 151, 176, 5, 183, 212, 88, 215, 119, 222, 132, 226, 30],
  #v[49, 120, 79, 94, 249, 229, 186, 192, 1, 202, 230, 237, 72, 212, 138, 154],
  #v[22, 51, 49, 175, 169, 86, 239, 179, 13, 182, 175, 40, 199, 247, 236, 107],
  #v[95, 104, 237, 43, 180, 188, 78, 61, 85, 160, 154, 232, 89, 58, 139, 244],
  #v[6, 102, 228, 21, 56, 231, 21, 70, 199, 187, 203, 68, 71, 95, 78, 223],
  #v[70, 2, 56, 90, 12, 95, 37, 190, 171, 199, 122, 61, 31, 12, 77, 46],
  #v[210, 94, 215, 224, 54, 39, 54, 166, 56, 88, 163, 198, 111, 136, 244, 24],
  #v[228, 230, 7, 211, 5, 179, 218, 121, 78, 135, 9, 173, 172, 124, 212, 243],
  #v[33, 223, 198, 142, 175, 33, 70, 19, 82, 53, 43, 179, 141, 16, 156, 185],
  #v[82, 154, 57, 183, 191, 247, 37, 70, 83, 74, 252, 210, 164, 232, 101, 222],
  #v[77, 251, 125, 199, 115, 55, 141, 207, 171, 157, 189, 152, 201, 249, 184, 128],
  #v[232, 6, 203, 212, 236, 214, 238, 43, 209, 21, 152, 125, 54, 175, 58, 202],
  #v[175, 177, 195, 189, 219, 132, 128, 10, 232, 38, 231, 85, 227, 45, 185, 218],
  #v[95, 153, 73, 254, 176, 178, 143, 174, 171, 65, 222, 37, 89, 6, 143, 244],
  #v[93, 178, 119, 229, 72, 119, 208, 12, 211, 114, 115, 65, 184, 3, 93, 244],
  #v[163, 132, 90, 88, 221, 187, 1, 112, 14, 175, 103, 70, 225, 110, 14, 107],
  #v[227, 180, 224, 25, 208, 60, 222, 133, 42, 252, 118, 198, 169, 157, 20, 3],
  #v[39, 203, 99, 163, 83, 8, 239, 47, 3, 214, 235, 202, 170, 28, 22, 233]]

theorem katPublic8_0 : pk8[0] = katPublic8[0] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_1 : pk8[1] = katPublic8[1] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_2 : pk8[2] = katPublic8[2] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_3 : pk8[3] = katPublic8[3] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_4 : pk8[4] = katPublic8[4] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_5 : pk8[5] = katPublic8[5] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_6 : pk8[6] = katPublic8[6] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_7 : pk8[7] = katPublic8[7] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_8 : pk8[8] = katPublic8[8] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_9 : pk8[9] = katPublic8[9] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_10 : pk8[10] = katPublic8[10] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_11 : pk8[11] = katPublic8[11] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_12 : pk8[12] = katPublic8[12] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_13 : pk8[13] = katPublic8[13] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_14 : pk8[14] = katPublic8[14] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_15 : pk8[15] = katPublic8[15] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_16 : pk8[16] = katPublic8[16] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_17 : pk8[17] = katPublic8[17] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_18 : pk8[18] = katPublic8[18] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_19 : pk8[19] = katPublic8[19] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_20 : pk8[20] = katPublic8[20] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_21 : pk8[21] = katPublic8[21] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_22 : pk8[22] = katPublic8[22] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_23 : pk8[23] = katPublic8[23] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_24 : pk8[24] = katPublic8[24] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_25 : pk8[25] = katPublic8[25] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_26 : pk8[26] = katPublic8[26] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_27 : pk8[27] = katPublic8[27] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_28 : pk8[28] = katPublic8[28] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_29 : pk8[29] = katPublic8[29] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_30 : pk8[30] = katPublic8[30] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_31 : pk8[31] = katPublic8[31] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_32 : pk8[32] = katPublic8[32] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_33 : pk8[33] = katPublic8[33] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_34 : pk8[34] = katPublic8[34] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_35 : pk8[35] = katPublic8[35] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_36 : pk8[36] = katPublic8[36] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_37 : pk8[37] = katPublic8[37] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_38 : pk8[38] = katPublic8[38] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_39 : pk8[39] = katPublic8[39] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_40 : pk8[40] = katPublic8[40] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic8_41 : pk8[41] = katPublic8[41] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel

/-- The whole one-time public key, chain by chain. -/
theorem katPublicKey8 : pk8 = katPublic8 := by
  apply Vector.ext
  intro i hi
  change i < 42 at hi
  interval_cases i
  exacts [katPublic8_0, katPublic8_1, katPublic8_2, katPublic8_3, katPublic8_4, katPublic8_5, katPublic8_6, katPublic8_7, katPublic8_8, katPublic8_9, katPublic8_10, katPublic8_11, katPublic8_12, katPublic8_13, katPublic8_14, katPublic8_15, katPublic8_16, katPublic8_17, katPublic8_18, katPublic8_19, katPublic8_20, katPublic8_21, katPublic8_22, katPublic8_23, katPublic8_24, katPublic8_25, katPublic8_26, katPublic8_27, katPublic8_28, katPublic8_29, katPublic8_30, katPublic8_31, katPublic8_32, katPublic8_33, katPublic8_34, katPublic8_35, katPublic8_36, katPublic8_37, katPublic8_38, katPublic8_39, katPublic8_40, katPublic8_41]

/-- The leaf at epoch 8 is the hash of these chain ends. -/
theorem katLeaf8_eq :
    exampleSk.leaves 8 = otsLeaf examplePublicKey.publicParam 8 katPublic8 := by
  unfold SecretKey.leaves
  rw [katPublicParam]
  change otsLeaf examplePublicKey.publicParam 8 pk8 = _
  rw [katPublicKey8]

end EthLib.Cryptography.Xmss
