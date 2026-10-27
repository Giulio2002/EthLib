import EthLib.Cryptography.Proofs.Xmss.KernelKatSupport

/-!
# Proofs: the Merkle climb, level by level

Theorem `k` pins the node reached after `k` levels of the 32-level climb from the leaf.

Each level hashes one more sibling from the signature path.

The values are intermediate states of verifying the reference signature at epoch 7.

They are computed by the verifier itself, so they are not checks on their own.

They split one large kernel evaluation into small steps.

The check is the final known answer: the reference signature verifies.
-/

namespace EthLib.Cryptography.Xmss
open Constants

theorem katRoot0 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 0 (by decide) katLeaf = #v[117, 143, 179, 141, 222, 231, 67, 10, 141, 38, 142, 200, 182, 166, 92, 58] := by
  rfl
theorem katRoot1 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 1 (by decide) katLeaf = #v[230, 128, 0, 224, 178, 179, 91, 38, 47, 91, 28, 228, 63, 50, 211, 2] := by
  rw [Internal.climbUpto, katRoot0]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot2 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 2 (by decide) katLeaf = #v[207, 246, 73, 155, 173, 89, 54, 22, 253, 107, 145, 122, 9, 63, 246, 102] := by
  rw [Internal.climbUpto, katRoot1]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot3 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 3 (by decide) katLeaf = #v[102, 103, 48, 12, 176, 155, 237, 65, 59, 150, 190, 210, 229, 109, 26, 107] := by
  rw [Internal.climbUpto, katRoot2]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot4 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 4 (by decide) katLeaf = #v[155, 118, 254, 119, 241, 174, 177, 180, 63, 222, 17, 191, 182, 221, 56, 91] := by
  rw [Internal.climbUpto, katRoot3]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot5 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 5 (by decide) katLeaf = #v[136, 1, 206, 206, 0, 123, 57, 216, 134, 225, 74, 96, 67, 192, 99, 128] := by
  rw [Internal.climbUpto, katRoot4]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot6 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 6 (by decide) katLeaf = #v[30, 30, 155, 170, 223, 16, 20, 185, 115, 120, 185, 52, 75, 73, 7, 122] := by
  rw [Internal.climbUpto, katRoot5]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot7 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 7 (by decide) katLeaf = #v[6, 108, 215, 68, 164, 202, 103, 123, 58, 60, 6, 47, 8, 150, 198, 182] := by
  rw [Internal.climbUpto, katRoot6]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot8 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 8 (by decide) katLeaf = #v[209, 237, 206, 108, 19, 67, 195, 56, 62, 157, 3, 116, 155, 157, 90, 57] := by
  rw [Internal.climbUpto, katRoot7]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot9 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 9 (by decide) katLeaf = #v[141, 177, 24, 48, 46, 15, 60, 185, 157, 76, 74, 98, 232, 26, 49, 228] := by
  rw [Internal.climbUpto, katRoot8]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot10 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 10 (by decide) katLeaf = #v[250, 185, 199, 19, 4, 216, 100, 134, 50, 69, 77, 237, 242, 115, 214, 228] := by
  rw [Internal.climbUpto, katRoot9]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot11 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 11 (by decide) katLeaf = #v[154, 192, 76, 247, 32, 233, 124, 107, 189, 204, 255, 248, 7, 45, 125, 241] := by
  rw [Internal.climbUpto, katRoot10]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot12 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 12 (by decide) katLeaf = #v[65, 238, 176, 204, 203, 51, 18, 27, 122, 129, 82, 225, 93, 92, 177, 0] := by
  rw [Internal.climbUpto, katRoot11]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot13 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 13 (by decide) katLeaf = #v[159, 162, 91, 77, 149, 156, 71, 120, 236, 52, 253, 28, 211, 130, 196, 63] := by
  rw [Internal.climbUpto, katRoot12]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot14 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 14 (by decide) katLeaf = #v[173, 172, 55, 251, 161, 133, 32, 75, 60, 116, 224, 161, 38, 105, 137, 86] := by
  rw [Internal.climbUpto, katRoot13]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot15 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 15 (by decide) katLeaf = #v[46, 180, 254, 174, 51, 255, 102, 250, 50, 149, 39, 74, 129, 25, 93, 147] := by
  rw [Internal.climbUpto, katRoot14]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot16 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 16 (by decide) katLeaf = #v[22, 30, 22, 51, 74, 119, 46, 240, 137, 49, 164, 43, 99, 49, 106, 15] := by
  rw [Internal.climbUpto, katRoot15]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot17 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 17 (by decide) katLeaf = #v[111, 157, 189, 227, 148, 2, 174, 200, 86, 102, 227, 230, 16, 8, 54, 165] := by
  rw [Internal.climbUpto, katRoot16]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot18 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 18 (by decide) katLeaf = #v[254, 1, 7, 151, 150, 73, 213, 123, 228, 146, 123, 59, 165, 195, 28, 190] := by
  rw [Internal.climbUpto, katRoot17]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot19 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 19 (by decide) katLeaf = #v[248, 247, 147, 208, 15, 43, 47, 226, 208, 122, 145, 238, 104, 186, 225, 174] := by
  rw [Internal.climbUpto, katRoot18]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot20 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 20 (by decide) katLeaf = #v[104, 232, 178, 103, 94, 49, 163, 73, 225, 103, 56, 175, 252, 228, 96, 110] := by
  rw [Internal.climbUpto, katRoot19]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot21 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 21 (by decide) katLeaf = #v[171, 109, 208, 171, 64, 131, 220, 236, 29, 154, 60, 214, 57, 96, 107, 205] := by
  rw [Internal.climbUpto, katRoot20]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot22 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 22 (by decide) katLeaf = #v[54, 149, 179, 1, 241, 140, 120, 116, 161, 72, 44, 84, 110, 220, 151, 118] := by
  rw [Internal.climbUpto, katRoot21]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot23 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 23 (by decide) katLeaf = #v[136, 89, 44, 194, 223, 35, 157, 124, 174, 156, 198, 125, 167, 109, 119, 69] := by
  rw [Internal.climbUpto, katRoot22]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot24 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 24 (by decide) katLeaf = #v[121, 171, 20, 167, 190, 195, 146, 33, 167, 255, 9, 75, 4, 41, 100, 98] := by
  rw [Internal.climbUpto, katRoot23]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot25 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 25 (by decide) katLeaf = #v[226, 2, 22, 45, 227, 207, 65, 147, 194, 117, 186, 237, 205, 87, 169, 229] := by
  rw [Internal.climbUpto, katRoot24]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot26 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 26 (by decide) katLeaf = #v[121, 192, 144, 238, 76, 149, 170, 42, 150, 191, 34, 157, 47, 90, 198, 104] := by
  rw [Internal.climbUpto, katRoot25]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot27 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 27 (by decide) katLeaf = #v[0, 33, 5, 48, 80, 81, 122, 37, 28, 3, 156, 146, 211, 118, 34, 198] := by
  rw [Internal.climbUpto, katRoot26]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot28 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 28 (by decide) katLeaf = #v[30, 219, 52, 11, 71, 87, 73, 107, 8, 13, 230, 143, 99, 71, 239, 125] := by
  rw [Internal.climbUpto, katRoot27]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot29 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 29 (by decide) katLeaf = #v[122, 110, 10, 55, 53, 20, 179, 14, 105, 94, 212, 57, 109, 14, 214, 114] := by
  rw [Internal.climbUpto, katRoot28]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot30 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 30 (by decide) katLeaf = #v[46, 55, 219, 167, 50, 63, 15, 112, 239, 145, 58, 148, 235, 248, 157, 107] := by
  rw [Internal.climbUpto, katRoot29]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot31 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 31 (by decide) katLeaf = #v[25, 60, 70, 70, 204, 122, 111, 3, 118, 148, 253, 112, 150, 49, 65, 1] := by
  rw [Internal.climbUpto, katRoot30]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel
theorem katRoot32 : Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 32 (by decide) katLeaf = #v[236, 52, 183, 27, 47, 147, 17, 16, 111, 194, 55, 187, 228, 219, 125, 43] := by
  rw [Internal.climbUpto, katRoot31]; simp only [Internal.climbStep, merkleNode_eq_tweakHashList]; decide +kernel

end EthLib.Cryptography.Xmss
