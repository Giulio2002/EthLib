import EthLib.Cryptography.Proofs.Xmss.KernelKatSupport

/-!
# Proofs: recovered chain ends 28 to 41

Each theorem pins the end of one hash chain, recovered from the signature.

The values are intermediate states of verifying the reference signature at epoch 7.

They are computed by the verifier itself, so they are not checks on their own.

They split one large kernel evaluation into small steps.

The check is the final known answer: the reference signature verifies.
-/

namespace EthLib.Cryptography.Xmss
open Constants

theorem katChain28 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[28] = #v[213, 104, 106, 164, 228, 60, 49, 249, 36, 42, 117, 143, 134, 254, 178, 101] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain29 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[29] = #v[7, 59, 19, 119, 100, 42, 202, 63, 209, 72, 111, 191, 51, 10, 254, 53] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain30 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[30] = #v[70, 71, 119, 29, 159, 208, 175, 249, 171, 64, 125, 129, 201, 103, 212, 105] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain31 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[31] = #v[97, 6, 159, 112, 196, 29, 162, 116, 184, 97, 236, 1, 190, 120, 181, 41] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain32 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[32] = #v[238, 95, 189, 56, 27, 198, 80, 11, 1, 55, 186, 84, 210, 133, 196, 88] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain33 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[33] = #v[44, 212, 111, 128, 241, 183, 140, 250, 188, 129, 155, 4, 137, 180, 230, 47] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain34 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[34] = #v[74, 131, 26, 76, 93, 143, 213, 241, 240, 35, 240, 5, 80, 110, 234, 192] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain35 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[35] = #v[242, 203, 117, 221, 192, 97, 186, 66, 2, 75, 21, 214, 63, 234, 122, 116] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain36 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[36] = #v[238, 61, 38, 243, 166, 230, 22, 126, 190, 96, 130, 168, 239, 184, 251, 177] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain37 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[37] = #v[3, 222, 217, 130, 84, 247, 17, 89, 184, 122, 5, 246, 114, 58, 227, 25] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain38 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[38] = #v[253, 15, 8, 94, 206, 109, 221, 233, 47, 40, 218, 222, 241, 123, 192, 194] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain39 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[39] = #v[174, 96, 118, 196, 151, 106, 133, 219, 6, 163, 244, 94, 10, 134, 38, 72] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain40 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[40] = #v[8, 149, 216, 9, 170, 75, 149, 240, 204, 134, 154, 3, 117, 192, 27, 189] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain41 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[41] = #v[208, 182, 13, 62, 23, 2, 235, 248, 45, 121, 15, 48, 154, 29, 98, 118] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel

end EthLib.Cryptography.Xmss
