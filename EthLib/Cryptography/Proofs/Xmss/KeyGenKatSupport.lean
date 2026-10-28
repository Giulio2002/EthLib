import EthLib.Cryptography.Xmss.KeyGen
import EthLib.Cryptography.Proofs.Xmss.Verify
import EthLib.Cryptography.Proofs.Xmss.Ots
import EthLib.Cryptography.Proofs.Xmss.Merkle
import EthLib.Cryptography.Proofs.Hash.Blake2sKernel

/-!
# Proofs: support for the key generation known answer

The kernel checks the key generation known answer by evaluating every hash it makes.

That is several hundred BLAKE2s compressions.

This file restates each hash of key generation with the fast form of BLAKE2s.

Each restatement holds for every input.

A known answer rewrites to it, then lets the kernel evaluate.
-/

namespace EthLib.Cryptography.Xmss
open Constants

/-! ## The reference key -/

/-- The seed `0, 1, ..., 31` the reference key is grown from. -/
def exampleSeed : Seed := Vector.ofFn fun i => UInt8.ofNat i.val

/-- The secret key for epochs 6 to 8 grown from the reference seed. -/
def exampleSk : SecretKey := ⟨exampleSeed, 6, 8, by decide⟩

/-! ## Hashes in fast form -/

/-- The tweak hash, computed with the fast form of BLAKE2s. -/
def tweakHashFast (pp : PublicParam) (tweakType : TweakType)
    (subPosition index : UInt32) (payload : List UInt8) : Digest :=
  (Hash.Blake2s.hashFast
    ⟨⟨(makeTweak tweakType subPosition index).toList ++ pp.toList ++ payload⟩⟩).take DIGEST_LEN

/-- Both forms of the tweak hash agree on every input. -/
theorem tweakHashList_eq_fast (pp : PublicParam) (tweakType : TweakType)
    (subPosition index : UInt32) (payload : List UInt8) :
    tweakHashList pp tweakType subPosition index payload =
      tweakHashFast pp tweakType subPosition index payload := by
  unfold tweakHashList tweakHashFast
  rw [Hash.Blake2s.hash_eq_hashFast]

/-- A hash chain walked with the fast tweak hash. -/
def chainFast (pp : PublicParam) (epoch : Epoch) (index : Fin V)
    (start steps : Nat) (h : start + steps < CHAIN_LENGTH) (value : Digest) : Digest :=
  match steps, h with
  | 0, _ => value
  | s + 1, h => tweakHashFast pp .chain (chainPosition index ⟨start + s, by omega⟩) epoch
      (chainFast pp epoch index start s (by omega) value).toList

/-- Both walks of a chain agree on every input. -/
theorem chainList_eq_fast (pp : PublicParam) (epoch : Epoch) (index : Fin V)
    (start steps : Nat) (h : start + steps < CHAIN_LENGTH) (value : Digest) :
    chainList pp epoch index start steps h value =
      chainFast pp epoch index start steps h value := by
  induction steps with
  | zero => rfl
  | succ s ih => simp only [chainList, chainFast, tweakHashList_eq_fast, ih (by omega)]

/-- A filler node is the fast tweak hash of the seed. -/
theorem fillerNode_eq_fast (pp : PublicParam) (seed : Seed) (level index : Nat) :
    fillerNode pp seed level index =
      tweakHashFast pp .filler (UInt32.ofNat level) (UInt32.ofNat index) seed.toList := by
  unfold fillerNode
  rw [packBytes_eq_list, tweakHash_eq_list, tweakHashList_eq_fast]

/-- A Merkle node is the fast tweak hash of its two children. -/
theorem merkleNode_eq_fast (pp : PublicParam) (level index : Nat) (left right : Digest) :
    merkleNode pp level index left right =
      tweakHashFast pp .merkle (UInt32.ofNat level) (UInt32.ofNat index)
        (left.toList ++ right.toList) := by
  rw [merkleNode_eq_tweakHashList, tweakHashList_eq_fast]

/-- A leaf is the fast tweak hash of the one-time public key. -/
theorem otsLeaf_eq_fast (pp : PublicParam) (epoch : Epoch) (pk : Vector Digest V) :
    otsLeaf pp epoch pk =
      tweakHashFast pp .leaf 0 epoch (pk.toList.map Vector.toList).flatten := by
  rw [otsLeaf_eq_tweakHashList, tweakHashList_eq_fast]

/-! ## One-time keys in fast form -/

/-- Chain `i` of a one-time public key walks seven steps from its secret value. -/
theorem otsPublicKey_getElem_eq_fast (pp : PublicParam) (seed : Seed) (epoch : Epoch)
    (i : Nat) (hi : i < V) :
    (otsPublicKey pp epoch (otsSecretKey pp seed epoch))[i] =
      chainFast pp epoch ⟨i, hi⟩ 0 7 (by decide)
        (tweakHashFast pp .prf (UInt32.ofNat i) epoch seed.toList) := by
  simp only [otsPublicKey, otsSecretKey, Vector.getElem_ofFn, Fin.getElem_fin,
    chain_eq_chainList, packBytes_eq_list, tweakHash_eq_list, chainList_eq_fast,
    tweakHashList_eq_fast]
  rfl

/-- Chain `i` of a one-time signature walks as many steps as its digit. -/
theorem otsReveal_getElem_eq_fast (pp : PublicParam) (seed : Seed) (epoch : Epoch)
    (x : Vector (Fin CHAIN_LENGTH) V) (i : Nat) (hi : i < V) :
    (otsReveal pp epoch (otsSecretKey pp seed epoch) x)[i] =
      chainFast pp epoch ⟨i, hi⟩ 0 (x[i] : Nat) (by simp)
        (tweakHashFast pp .prf (UInt32.ofNat i) epoch seed.toList) := by
  simp only [otsReveal, otsSecretKey, Vector.getElem_ofFn, Fin.getElem_fin,
    chain_eq_chainList, packBytes_eq_list, tweakHash_eq_list, chainList_eq_fast,
    tweakHashList_eq_fast]

/-! ## The public parameter -/

/-- The reference key derives the reference public parameter from its seed. -/
theorem katPublicParam : exampleSk.publicParam = examplePublicKey.publicParam := by
  change (tweakHash (Vector.replicate PUBLIC_PARAM_LEN 0) .parameter 0 0 (packBytes exampleSeed) :
    Digest) = examplePublicKey.publicParam
  rw [packBytes_eq_list, tweakHash_eq_list, tweakHashList_eq_fast]
  decide +kernel

end EthLib.Cryptography.Xmss
