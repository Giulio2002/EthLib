import EthLib.Cryptography.Xmss.KeyGen
import EthLib.Cryptography.Xmss.Sign
import EthLib.Cryptography.Xmss.Serialization

/-!
# `Xmss.Exports`

C-ABI exports for the Python bindings.

Only key generation, signing and verification cross the boundary.
The scheme is a black box to callers: no hash or encoding layer is exported.
-/

namespace EthLib.Cryptography.Xmss.Exports

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

/-- Read a fixed-size input, rejecting any other length with the given error. -/
private def readExact (n : Nat) (bytes : ByteArray) (bad : Nat → XmssError) :
    Except XmssError (Vector UInt8 n) :=
  -- Too short or too long is refused: no padding, no truncation.
  if h : bytes.size = n then .ok ⟨bytes.data, h⟩ else .error (bad bytes.size)

/-- The public key grown from a seed, for the epochs `[epochStart, epochEnd]`. -/
@[export eth_xmss_key_gen]
def keyGenExport (seed : ByteArray) (epochStart epochEnd : Epoch) :
    IO ByteArray :=
  runXmss do
    let seed ← readExact SEED_LEN seed .badSeedSize
    -- The secret half is dropped: the seed and the range regrow it.
    let (_, pk) ← keyGen seed epochStart epochEnd
    return encodePublicKey pk

/-- Sign a message at an epoch with the key grown from a seed. -/
@[export eth_xmss_sign]
def signExport (seed : ByteArray) (epochStart epochEnd epoch : Epoch)
    (msg : ByteArray) : IO ByteArray :=
  runXmss do
    let seed ← readExact SEED_LEN seed .badSeedSize
    let msg ← readExact MESSAGE_LEN msg .badMessageSize
    -- Only the secret key: signing never needs the root, so no tree is built here.
    let sk ← SecretKey.ofSeed seed epochStart epochEnd
    -- An epoch outside the range fails before any hashing.
    let sig ← sign sk msg epoch
    return encodeSignature sig

/-- Whether a signature signs a message at an epoch under a public key, as 1 or 0. -/
@[export eth_xmss_verify]
def verifyExport (pk : ByteArray) (epoch : Epoch) (msg : ByteArray)
    (sig : ByteArray) : IO UInt8 :=
  runXmss do
    -- Only the lengths are checked: every correctly sized string decodes.
    let pk ← decodePublicKey pk
    let msg ← readExact MESSAGE_LEN msg .badMessageSize
    let sig ← decodeSignature sig
    return if verify pk msg sig epoch then 1 else 0

end EthLib.Cryptography.Xmss.Exports
