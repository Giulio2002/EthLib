import EthLib.Cryptography.Proofs.Xmss.KernelKatSupport

/-!
# Proofs: recovered chain ends 0 to 13

Each theorem pins the end of one hash chain, recovered from the signature.

The values are intermediate states of verifying the reference signature at epoch 7.

They are computed by the verifier itself, so they are not checks on their own.

They split one large kernel evaluation into small steps.

The check is the final known answer: the reference signature verifies.
-/

namespace EthLib.Cryptography.Xmss
open Constants

theorem katChain0 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[0] = #v[181, 163, 163, 38, 150, 230, 253, 43, 199, 91, 248, 207, 111, 11, 231, 92] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain1 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[1] = #v[109, 183, 186, 39, 176, 220, 58, 155, 155, 212, 203, 196, 230, 11, 28, 10] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain2 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[2] = #v[232, 155, 197, 207, 191, 233, 22, 237, 97, 12, 100, 17, 143, 130, 58, 209] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain3 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[3] = #v[123, 225, 48, 117, 106, 118, 161, 250, 103, 17, 251, 21, 178, 148, 61, 186] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain4 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[4] = #v[251, 33, 253, 232, 194, 216, 103, 223, 251, 202, 234, 102, 166, 44, 209, 149] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain5 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[5] = #v[131, 35, 144, 223, 156, 171, 23, 97, 174, 213, 63, 164, 83, 251, 140, 117] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain6 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[6] = #v[57, 113, 239, 94, 84, 229, 163, 138, 241, 214, 168, 79, 212, 126, 162, 210] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain7 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[7] = #v[90, 228, 35, 116, 179, 87, 116, 107, 210, 107, 108, 163, 80, 76, 54, 108] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain8 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[8] = #v[17, 73, 40, 87, 161, 31, 136, 80, 207, 181, 195, 120, 130, 164, 118, 215] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain9 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[9] = #v[148, 187, 190, 164, 202, 44, 3, 130, 249, 218, 180, 69, 127, 53, 171, 245] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain10 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[10] = #v[95, 249, 25, 14, 167, 48, 56, 25, 136, 155, 235, 212, 66, 36, 134, 230] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain11 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[11] = #v[216, 40, 200, 210, 161, 122, 143, 238, 109, 155, 133, 166, 160, 228, 40, 12] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain12 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[12] = #v[56, 169, 242, 225, 163, 155, 76, 40, 40, 48, 167, 112, 28, 248, 133, 55] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain13 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[13] = #v[112, 55, 132, 162, 42, 185, 156, 122, 36, 17, 82, 48, 139, 184, 138, 104] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel

end EthLib.Cryptography.Xmss
