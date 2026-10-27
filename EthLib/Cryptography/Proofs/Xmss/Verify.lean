import EthLib.Cryptography.Xmss.Verify
import EthLib.Cryptography.Proofs.Xmss.VerifyLeaf
import EthLib.Cryptography.Proofs.Xmss.VerifyRoots

/-!
# Proofs: `Xmss.Verify`

What an accepting verifier has checked.
-/

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {pk : PublicKey} {msg : Message} {sig : Signature} {epoch : Epoch}

/-- An inadmissible digest rejects, whatever the rest of the signature. -/
theorem verify_of_wotsEncode_none
    (h : wotsEncode pk.publicParam msg sig.randomness epoch = none) :
    verify pk msg sig epoch = false := by
  simp only [verify, h]

/-- Acceptance, unfolded.

The message encodes, and the leaf its chains claim reaches the root. -/
theorem verify_iff :
    verify pk msg sig epoch = true ↔
      ∃ x, wotsEncode pk.publicParam msg sig.randomness epoch = some x ∧
        computeRoot pk.publicParam epoch sig.merklePath
          (otsLeaf pk.publicParam epoch
            (otsRecover pk.publicParam epoch sig.chainElements x))
          = pk.merkleRoot := by
  -- Split on the encoding: the rejecting branch has no witness to offer.
  cases h : wotsEncode pk.publicParam msg sig.randomness epoch <;>
    simp only [verify, h, reduceCtorEq, false_and, exists_false,
      Option.some.injEq, exists_eq_left', decide_eq_true_eq]

/-! ## Known answer

One honest signature, pinned byte for byte.

It fixes every hash the verifier makes, not just its accept or reject. -/


/-- The reference signature verifies. -/
theorem verify_known_answer :
    verify examplePublicKey exampleMessage exampleSignature 7 = true := by
  dsimp only [verify]
  rw [katEncode]
  dsimp only
  rw [katRecover, katLeaf_eq]
  change decide (Internal.climbUpto _ 7 _ 32 _ katLeaf = _) = true
  rw [katRoot32]
  decide +kernel

/-- The same signature at the neighbouring epoch rejects.

The epoch enters the encoding hash, so the digest there is inadmissible. -/
theorem verify_wrong_epoch :
    verify examplePublicKey exampleMessage exampleSignature 6 = false := by
  -- Rejection stops after the encoding hash, which the kernel can evaluate.
  decide +kernel

/-- Changing the topmost sibling rejects.

A root computation that ignored one side of a node would still accept. -/
theorem verify_tampered_path :
    verify examplePublicKey exampleMessage
      { exampleSignature with
        merklePath := exampleSignature.merklePath.set 31 (Vector.replicate 16 0) }
      7 = false := by
  dsimp only [verify]
  rw [katEncode]
  dsimp only
  rw [katRecover, katLeaf_eq]
  change decide (Internal.climbUpto examplePublicKey.publicParam 7
    (exampleSignature.merklePath.set 31 (Vector.replicate 16 0)) 32 (by decide) katLeaf =
    examplePublicKey.merkleRoot) = false
  rw [Internal.climbUpto]
  have hprefix : Internal.climbUpto examplePublicKey.publicParam 7
      (exampleSignature.merklePath.set 31 (Vector.replicate 16 0)) 31 (by decide) katLeaf =
      Internal.climbUpto examplePublicKey.publicParam 7 exampleSignature.merklePath 31 (by decide) katLeaf := by
    apply Internal.climbUpto_congr_path
    intro i hi
    simp [show 31 ≠ i by omega]
  rw [hprefix, katRoot31]
  simp only [Internal.climbStep, merkleNode_eq_tweakHashList]
  decide +kernel

end EthLib.Cryptography.Xmss
