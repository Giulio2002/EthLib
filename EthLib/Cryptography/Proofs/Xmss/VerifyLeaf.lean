import EthLib.Cryptography.Proofs.Xmss.VerifyChains0
import EthLib.Cryptography.Proofs.Xmss.VerifyChains1
import EthLib.Cryptography.Proofs.Xmss.VerifyChains2
import Mathlib.Tactic.IntervalCases

/-!
# Proofs: the encoding and the recovered leaf

These theorems pin the message encoding and the 42 recovered chain ends.

```text
    message, randomness  --encode-->  42 digits
    signature chains     --walk to the end-->  42 chain ends  --hash-->  leaf
```

The values are intermediate states of verifying the reference signature at epoch 7.

They are computed by the verifier itself, so they are not checks on their own.

They split one large kernel evaluation into small steps.

The check is the final known answer: the reference signature verifies.
-/

namespace EthLib.Cryptography.Xmss
open Constants

theorem katEncodingHash :
    tweakHash examplePublicKey.publicParam .encoding 0 7
      (encodingPayload exampleMessage exampleSignature.randomness) =
    #v[89, 201, 250, 143, 73, 159, 199, 111, 250, 232, 236, 123, 233, 43, 242, 121] := by
  decide +kernel

theorem katEncode :
    wotsEncode examplePublicKey.publicParam exampleMessage exampleSignature.randomness 7 =
      some katDigits := by
  unfold wotsEncode
  rw [katEncodingHash]
  decide +kernel

theorem katRecover :
    otsRecover examplePublicKey.publicParam 7 exampleSignature.chainElements katDigits =
      katPublic := by
  apply Vector.ext
  intro i hi
  change i < 42 at hi
  interval_cases i
  · exact katChain0
  · exact katChain1
  · exact katChain2
  · exact katChain3
  · exact katChain4
  · exact katChain5
  · exact katChain6
  · exact katChain7
  · exact katChain8
  · exact katChain9
  · exact katChain10
  · exact katChain11
  · exact katChain12
  · exact katChain13
  · exact katChain14
  · exact katChain15
  · exact katChain16
  · exact katChain17
  · exact katChain18
  · exact katChain19
  · exact katChain20
  · exact katChain21
  · exact katChain22
  · exact katChain23
  · exact katChain24
  · exact katChain25
  · exact katChain26
  · exact katChain27
  · exact katChain28
  · exact katChain29
  · exact katChain30
  · exact katChain31
  · exact katChain32
  · exact katChain33
  · exact katChain34
  · exact katChain35
  · exact katChain36
  · exact katChain37
  · exact katChain38
  · exact katChain39
  · exact katChain40
  · exact katChain41

theorem katLeaf_eq : otsLeaf examplePublicKey.publicParam 7 katPublic = katLeaf := by
  rw [otsLeaf_eq_tweakHashList]
  decide +kernel

end EthLib.Cryptography.Xmss
