import EthLib.Cryptography.Xmss.KeyGen
import EthLib.Cryptography.Proofs.Xmss.Verify
import EthLib.Cryptography.Proofs.Xmss.KeyGenPath
import EthLib.Cryptography.Proofs.Xmss.KeyGenReveal7

/-!
# Proofs: `Xmss.KeyGen`
-/

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {seed : Seed} {epochStart epochEnd : Epoch} {sk : SecretKey}
  {pk : PublicKey}

/-- Building a secret key fails exactly on an empty range. -/
theorem SecretKey.ofSeed_eq_error_iff :
    (∃ err, SecretKey.ofSeed seed epochStart epochEnd = .error err)
      ↔ epochEnd < epochStart := by
  unfold SecretKey.ofSeed
  split
  · rename_i h
    simp only [reduceCtorEq, exists_false, false_iff, UInt32.not_lt]
    exact h
  · rename_i h
    simp only [Except.error.injEq, exists_eq', true_iff]
    exact UInt32.not_le.mp h

/-- An accepted secret key is the seed over the requested range. -/
theorem SecretKey.ofSeed_eq_ok (h : SecretKey.ofSeed seed epochStart epochEnd = .ok sk) :
    sk.seed = seed ∧ sk.epochStart = epochStart ∧ sk.epochEnd = epochEnd := by
  unfold SecretKey.ofSeed at h
  split at h
  · cases Except.ok.inj h
    exact ⟨rfl, rfl, rfl⟩
  · exact absurd h (by simp)

/-- Key generation fails exactly on an empty range. -/
theorem keyGen_eq_error_iff :
    (∃ err, keyGen seed epochStart epochEnd = .error err)
      ↔ epochEnd < epochStart := by
  -- Key generation fails exactly when building the secret key does.
  rw [← SecretKey.ofSeed_eq_error_iff]
  unfold keyGen
  cases SecretKey.ofSeed seed epochStart epochEnd <;> simp [Except.map]

/-- An accepted key pair is the seed's key over the requested range. -/
theorem keyGen_eq_ok (h : keyGen seed epochStart epochEnd = .ok (sk, pk)) :
    pk = sk.publicKey ∧ sk.seed = seed ∧
      sk.epochStart = epochStart ∧ sk.epochEnd = epochEnd := by
  unfold keyGen at h
  cases built : SecretKey.ofSeed seed epochStart epochEnd with
  | error err => simp [built, Except.map] at h
  | ok sk' =>
    simp only [built, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, SecretKey.ofSeed_eq_ok built⟩

/-- The leaf at an epoch hashes that epoch's one-time public key. -/
theorem leaves_toNat (sk : SecretKey) (epoch : Epoch) :
    sk.leaves epoch.toNat = otsLeaf sk.publicParam epoch
      (otsPublicKey sk.publicParam epoch
        (otsSecretKey sk.publicParam sk.seed epoch)) := by
  -- A 32-bit epoch survives the round trip through the natural numbers.
  simp only [SecretKey.leaves, UInt32.ofNat_toNat]

/-! ## Known answer -/

/-- Key generation over epochs 6 to 8 gives the reference public key. -/
theorem keyGen_known_answer :
    (keyGen exampleSeed 6 8).toOption.map Prod.snd = some examplePublicKey := by
  -- The root is the climb from leaf 7 along its path.
  -- The leaf and the path match the reference signature, whose climb is already checked.
  have hroot : exampleSk.tree.root exampleSk.leaves = examplePublicKey.merkleRoot := by
    rw [← computeRoot_authPath exampleSk.tree exampleSk.leaves 7 (by decide) (by decide)]
    change computeRoot exampleSk.publicParam 7
      (exampleSk.tree.authPath exampleSk.leaves 7) (exampleSk.leaves 7) = _
    rw [katPublicParam, katAuthPath7, katLeaf7_eq]
    exact katRoot32
  -- The public key holds that root and the public parameter.
  have hpk : exampleSk.publicKey = examplePublicKey := by
    unfold SecretKey.publicKey
    rw [hroot, katPublicParam]
  -- The range 6 to 8 is not empty, so key generation returns that key.
  unfold keyGen SecretKey.ofSeed
  rw [dif_pos (by decide)]
  exact congrArg some hpk

/-- An empty epoch range rejects. -/
theorem keyGen_empty_range : (keyGen exampleSeed 8 6).toOption.isNone := by
  decide +kernel

end EthLib.Cryptography.Xmss
