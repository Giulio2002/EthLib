import EthLib.Cryptography.Proofs.Xmss.KernelKatSupport

/-!
# Proofs: recovered chain ends 14 to 27

Each theorem pins the end of one hash chain, recovered from the signature.

The values are intermediate states of verifying the reference signature at epoch 7.

They are computed by the verifier itself, so they are not checks on their own.

They split one large kernel evaluation into small steps.

The check is the final known answer: the reference signature verifies.
-/

namespace EthLib.Cryptography.Xmss
open Constants

theorem katChain14 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[14] = #v[65, 117, 119, 35, 236, 236, 119, 220, 177, 158, 206, 111, 90, 178, 1, 140] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain15 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[15] = #v[180, 148, 223, 168, 74, 18, 51, 73, 229, 143, 0, 192, 132, 140, 184, 41] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain16 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[16] = #v[120, 6, 28, 216, 253, 38, 11, 45, 30, 35, 133, 93, 81, 182, 46, 173] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain17 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[17] = #v[250, 201, 50, 231, 1, 152, 226, 189, 66, 147, 102, 77, 166, 43, 230, 124] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain18 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[18] = #v[224, 181, 241, 128, 90, 69, 123, 106, 136, 44, 71, 249, 75, 44, 180, 219] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain19 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[19] = #v[165, 6, 54, 170, 117, 80, 44, 111, 116, 191, 253, 71, 90, 121, 185, 184] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain20 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[20] = #v[193, 6, 191, 12, 123, 49, 72, 227, 252, 5, 70, 205, 74, 79, 254, 172] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain21 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[21] = #v[202, 38, 141, 4, 132, 55, 43, 42, 73, 6, 202, 38, 222, 21, 79, 152] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain22 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[22] = #v[229, 161, 162, 6, 172, 154, 118, 28, 55, 105, 40, 232, 178, 179, 177, 213] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain23 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[23] = #v[243, 84, 104, 1, 209, 210, 218, 247, 13, 168, 213, 110, 254, 21, 217, 143] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain24 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[24] = #v[91, 222, 18, 9, 169, 3, 239, 234, 252, 124, 164, 182, 187, 2, 248, 236] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain25 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[25] = #v[173, 172, 181, 195, 64, 68, 20, 56, 248, 254, 30, 38, 223, 46, 74, 84] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain26 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[26] = #v[173, 3, 89, 14, 111, 214, 203, 74, 174, 50, 23, 127, 2, 116, 166, 10] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel
theorem katChain27 : (otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits)[27] = #v[12, 192, 213, 37, 11, 94, 120, 111, 165, 52, 229, 100, 237, 229, 52, 182] := by
  rw [otsRecover_getElem_eq_chainList]; decide +kernel

end EthLib.Cryptography.Xmss
