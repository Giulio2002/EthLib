import EthLib.Cryptography.Proofs.Xmss.KeyGenKatSupport
import Mathlib.Tactic.IntervalCases

/-!
# Proofs: the one-time public key at epoch 6

The leaf at epoch 6 is the hash of the 42 chain ends of its one-time public key.

Each chain end is seven hashes from a secret value, itself one hash of the seed.

The chain ends below are intermediate values of key generation, computed by the code itself.

They are not checks on their own.

They split one large kernel evaluation into one evaluation per chain.

The check is that they hash to the first sibling in the reference signature's Merkle path.
-/

namespace EthLib.Cryptography.Xmss
open Constants

-- With asynchronous elaboration, memory grows with every theorem: 7.6 GB for the 42 chains at epoch 6.
-- Checked one after another, the whole file peaks at 2.4 GB, as a file with one chain does.
set_option Elab.async false

/-- The one-time public key at epoch 6. -/
local notation "pk6" =>
  otsPublicKey examplePublicKey.publicParam 6 (otsSecretKey examplePublicKey.publicParam exampleSeed 6)

/-- The 42 chain ends at epoch 6. -/
def katPublic6 : Vector Digest V := #v[
  #v[155, 221, 125, 84, 52, 119, 28, 103, 114, 95, 183, 92, 39, 130, 108, 188],
  #v[100, 20, 59, 110, 114, 85, 169, 236, 26, 68, 191, 24, 29, 198, 18, 193],
  #v[92, 62, 126, 85, 187, 206, 140, 230, 158, 106, 24, 185, 79, 99, 105, 95],
  #v[106, 113, 69, 48, 192, 243, 174, 116, 111, 107, 49, 114, 5, 155, 133, 156],
  #v[213, 213, 99, 120, 248, 105, 243, 48, 163, 64, 219, 62, 202, 193, 141, 41],
  #v[242, 13, 248, 142, 129, 33, 6, 255, 222, 13, 53, 23, 42, 218, 97, 58],
  #v[128, 247, 201, 251, 180, 254, 196, 239, 113, 109, 218, 41, 190, 89, 90, 242],
  #v[249, 19, 158, 186, 19, 43, 201, 177, 127, 125, 83, 194, 249, 182, 2, 61],
  #v[91, 101, 131, 16, 155, 194, 200, 37, 98, 131, 6, 163, 201, 48, 207, 127],
  #v[185, 117, 235, 21, 204, 255, 195, 235, 35, 240, 10, 225, 147, 133, 198, 0],
  #v[11, 251, 165, 151, 184, 9, 244, 189, 142, 182, 77, 168, 150, 97, 229, 166],
  #v[22, 179, 155, 71, 58, 154, 156, 33, 67, 183, 164, 100, 248, 2, 83, 111],
  #v[100, 128, 57, 90, 12, 33, 129, 192, 68, 49, 193, 116, 61, 100, 19, 149],
  #v[80, 194, 60, 98, 62, 157, 22, 152, 92, 221, 250, 252, 190, 202, 13, 243],
  #v[193, 233, 17, 119, 175, 187, 94, 220, 220, 85, 35, 245, 52, 192, 18, 3],
  #v[246, 75, 217, 71, 108, 16, 197, 220, 146, 162, 195, 2, 0, 45, 139, 79],
  #v[65, 121, 101, 3, 33, 52, 43, 207, 132, 111, 129, 172, 16, 249, 14, 50],
  #v[50, 255, 94, 224, 116, 58, 29, 120, 137, 40, 148, 147, 179, 214, 71, 44],
  #v[142, 132, 205, 246, 11, 129, 140, 93, 233, 215, 74, 20, 82, 149, 212, 6],
  #v[144, 184, 211, 153, 4, 245, 21, 39, 99, 34, 209, 101, 6, 92, 162, 50],
  #v[93, 97, 164, 89, 2, 190, 101, 43, 34, 107, 171, 57, 3, 36, 103, 238],
  #v[228, 148, 101, 248, 177, 118, 175, 251, 19, 236, 173, 69, 78, 127, 171, 250],
  #v[131, 239, 1, 116, 252, 149, 1, 230, 54, 188, 74, 29, 18, 91, 66, 28],
  #v[94, 102, 1, 214, 198, 228, 82, 97, 129, 197, 98, 20, 75, 83, 226, 180],
  #v[97, 43, 39, 240, 118, 120, 146, 9, 232, 107, 199, 199, 240, 250, 230, 253],
  #v[50, 186, 132, 178, 40, 104, 240, 221, 18, 235, 42, 193, 81, 78, 112, 122],
  #v[106, 148, 29, 147, 16, 159, 206, 89, 112, 40, 18, 33, 77, 241, 214, 128],
  #v[87, 32, 20, 59, 21, 224, 172, 158, 167, 248, 9, 254, 243, 253, 249, 233],
  #v[195, 159, 17, 80, 236, 210, 4, 249, 214, 46, 64, 246, 103, 234, 93, 207],
  #v[125, 154, 169, 192, 41, 153, 182, 86, 215, 230, 59, 53, 142, 53, 65, 73],
  #v[65, 85, 132, 182, 175, 93, 54, 11, 112, 110, 241, 215, 191, 55, 168, 132],
  #v[141, 214, 234, 11, 71, 21, 108, 252, 145, 167, 175, 60, 221, 12, 189, 17],
  #v[232, 26, 34, 175, 160, 21, 212, 122, 84, 137, 164, 67, 137, 10, 99, 157],
  #v[40, 93, 50, 62, 245, 238, 17, 242, 227, 85, 54, 215, 47, 60, 46, 185],
  #v[194, 134, 221, 105, 139, 175, 193, 57, 165, 38, 78, 251, 230, 129, 136, 154],
  #v[72, 166, 6, 50, 204, 181, 177, 239, 63, 167, 127, 163, 245, 35, 95, 111],
  #v[127, 56, 51, 208, 166, 224, 87, 6, 138, 112, 179, 40, 189, 96, 154, 246],
  #v[0, 62, 16, 119, 235, 138, 110, 52, 165, 1, 217, 141, 244, 37, 202, 241],
  #v[18, 104, 27, 82, 62, 160, 185, 183, 117, 80, 69, 92, 128, 6, 4, 255],
  #v[164, 229, 130, 67, 205, 104, 172, 202, 221, 59, 142, 253, 116, 18, 233, 14],
  #v[52, 234, 114, 115, 217, 8, 207, 204, 148, 112, 62, 243, 152, 217, 36, 142],
  #v[142, 181, 105, 30, 170, 1, 5, 148, 160, 169, 235, 215, 93, 224, 3, 17]]

theorem katPublic6_0 : pk6[0] = katPublic6[0] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_1 : pk6[1] = katPublic6[1] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_2 : pk6[2] = katPublic6[2] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_3 : pk6[3] = katPublic6[3] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_4 : pk6[4] = katPublic6[4] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_5 : pk6[5] = katPublic6[5] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_6 : pk6[6] = katPublic6[6] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_7 : pk6[7] = katPublic6[7] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_8 : pk6[8] = katPublic6[8] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_9 : pk6[9] = katPublic6[9] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_10 : pk6[10] = katPublic6[10] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_11 : pk6[11] = katPublic6[11] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_12 : pk6[12] = katPublic6[12] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_13 : pk6[13] = katPublic6[13] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_14 : pk6[14] = katPublic6[14] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_15 : pk6[15] = katPublic6[15] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_16 : pk6[16] = katPublic6[16] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_17 : pk6[17] = katPublic6[17] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_18 : pk6[18] = katPublic6[18] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_19 : pk6[19] = katPublic6[19] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_20 : pk6[20] = katPublic6[20] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_21 : pk6[21] = katPublic6[21] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_22 : pk6[22] = katPublic6[22] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_23 : pk6[23] = katPublic6[23] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_24 : pk6[24] = katPublic6[24] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_25 : pk6[25] = katPublic6[25] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_26 : pk6[26] = katPublic6[26] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_27 : pk6[27] = katPublic6[27] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_28 : pk6[28] = katPublic6[28] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_29 : pk6[29] = katPublic6[29] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_30 : pk6[30] = katPublic6[30] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_31 : pk6[31] = katPublic6[31] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_32 : pk6[32] = katPublic6[32] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_33 : pk6[33] = katPublic6[33] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_34 : pk6[34] = katPublic6[34] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_35 : pk6[35] = katPublic6[35] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_36 : pk6[36] = katPublic6[36] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_37 : pk6[37] = katPublic6[37] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_38 : pk6[38] = katPublic6[38] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_39 : pk6[39] = katPublic6[39] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_40 : pk6[40] = katPublic6[40] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel
theorem katPublic6_41 : pk6[41] = katPublic6[41] := by
  rw [otsPublicKey_getElem_eq_fast]; decide +kernel

/-- The whole one-time public key, chain by chain. -/
theorem katPublicKey6 : pk6 = katPublic6 := by
  apply Vector.ext
  intro i hi
  change i < 42 at hi
  interval_cases i
  exacts [katPublic6_0, katPublic6_1, katPublic6_2, katPublic6_3, katPublic6_4, katPublic6_5, katPublic6_6, katPublic6_7, katPublic6_8, katPublic6_9, katPublic6_10, katPublic6_11, katPublic6_12, katPublic6_13, katPublic6_14, katPublic6_15, katPublic6_16, katPublic6_17, katPublic6_18, katPublic6_19, katPublic6_20, katPublic6_21, katPublic6_22, katPublic6_23, katPublic6_24, katPublic6_25, katPublic6_26, katPublic6_27, katPublic6_28, katPublic6_29, katPublic6_30, katPublic6_31, katPublic6_32, katPublic6_33, katPublic6_34, katPublic6_35, katPublic6_36, katPublic6_37, katPublic6_38, katPublic6_39, katPublic6_40, katPublic6_41]

/-- The chain ends hash to the leaf at epoch 6, the first sibling of the reference path. -/
theorem katLeaf6_eq : exampleSk.leaves 6 = exampleSignature.merklePath[0] := by
  unfold SecretKey.leaves
  rw [katPublicParam]
  change otsLeaf examplePublicKey.publicParam 6 pk6 = _
  rw [katPublicKey6, otsLeaf_eq_fast]
  decide +kernel

end EthLib.Cryptography.Xmss
