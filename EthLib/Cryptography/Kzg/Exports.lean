import EthLib.Cryptography.Bls
import EthLib.Cryptography.Kzg.Constants
import EthLib.Cryptography.Kzg.Polynomials
import EthLib.Cryptography.Kzg.Core
import EthLib.Cryptography.Kzg.Cells
import EthLib.Cryptography.Kzg.Recovery
import EthLib.Cryptography.Kzg.TrustedSetup
import EthLib.Cryptography.Kzg.Errors

/-!
# `Exports`

C-ABI exports for the Python bindings.

Lean's `@[export]` attribute generates a C symbol with the given name
that takes Lean-runtime objects (`lean_object*`) and returns one. The
CPython extension under `bindings/python/` calls these symbols directly
after marshalling Python values into `ByteArray`s and `Array`s.

Two notes:

* `lean_initialize_runtime_module()` must be called by the loader
  before any of these are invoked. The Python wrapper does this in its
  `PyInit_*` function.

* All inputs are `ByteArray` or `Array X`. We return `ByteArray` for
  single outputs, `Array ByteArray` (or pairs thereof) for multi-output
  public methods. Booleans are returned as `UInt8`.
-/

namespace EthLib.Cryptography.Kzg.Exports

open EthLib.Cryptography.Kzg

/-- Decode a buffer of packed indices.

Each index is 8 bytes, big-endian:

```text
    [ index_0: 8 | index_1: 8 | ... | index_(n-1): 8 ]
```

The Python wrapper packs index arrays this way, so the C exports take only byte arrays.

A length that is not a multiple of 8 is rejected, never truncated.
-/
def unpackIndicesBE (b : ByteArray) : Except KzgError (Array Nat) := do
  -- A partial last index means a malformed buffer.
  if b.size % 8 != 0 then
    throw (.badIndicesBytesSize b.size)
  let n := b.size / 8
  let mut out : Array Nat := Array.mkEmpty n
  for i in [:n] do
    out := out.push (bytesBEToNat (b.extract (i*8) ((i+1)*8)))
  return out

@[export eth_kzg_blob_to_kzg_commitment]
def blobToKzgCommitmentExport (blob : ByteArray) : IO ByteArray :=
  runKzg (blobToKzgCommitment blob)

@[export eth_kzg_compute_challenge]
def computeChallengeExport
    (blob : ByteArray) (commitment : ByteArray) : IO ByteArray :=
  runKzg do
    if blob.size ≠ Constants.BYTES_PER_BLOB then
      throw (.badBlobSize blob.size)
    if commitment.size ≠ Constants.BYTES_PER_COMMITMENT then
      throw (.badCommitmentSize commitment.size)
    let _ ← blobToPolynomial blob
    let commitment ← bytesToKzgCommitment commitment
    return blsFieldToBytes (computeChallenge blob commitment)

/-- Returns a 80-byte buffer: 48-byte proof followed by 32-byte y. -/
@[export eth_kzg_compute_kzg_proof]
def computeKzgProofExport
    (blob : ByteArray) (z : ByteArray) : IO ByteArray := do
  let (proof, y) ← runKzg (computeKzgProof blob z)
  return proof ++ y

@[export eth_kzg_verify_kzg_proof]
def verifyKzgProofExport
    (commitment : ByteArray) (z : ByteArray)
    (y : ByteArray) (proof : ByteArray) : IO UInt8 := do
  let ok ← runKzg (verifyKzgProof commitment z y proof)
  return if ok then 1 else 0

@[export eth_kzg_compute_blob_kzg_proof]
def computeBlobKzgProofExport
    (blob : ByteArray) (commitment : ByteArray) : IO ByteArray :=
  runKzg (computeBlobKzgProof blob commitment)

@[export eth_kzg_verify_blob_kzg_proof]
def verifyBlobKzgProofExport
    (blob : ByteArray) (commitment : ByteArray) (proof : ByteArray)
    : IO UInt8 := do
  let ok ← runKzg (verifyBlobKzgProof blob commitment proof)
  return if ok then 1 else 0

@[export eth_kzg_verify_blob_kzg_proof_batch]
def verifyBlobKzgProofBatchExport
    (blobs : Array ByteArray)
    (commitments : Array ByteArray)
    (proofs : Array ByteArray) : IO UInt8 := do
  let ok ← runKzg (verifyBlobKzgProofBatch blobs commitments proofs)
  return if ok then 1 else 0

@[export eth_kzg_compute_cells]
def computeCellsExport (blob : ByteArray) : IO ByteArray := do
  let cells ← runKzg (computeCells blob)
  return cells.foldl (· ++ ·) ByteArray.empty

@[export eth_kzg_compute_verify_cell_kzg_proof_batch_challenge]
def computeVerifyCellKzgProofBatchChallengeExport
    (commitments : Array ByteArray)
    (commitmentIndicesBE : ByteArray)
    (cellIndicesBE : ByteArray)
    (cosetsEvals : Array ByteArray)
    (proofs : Array ByteArray) : IO ByteArray :=
  runKzg do
    let commitmentIndices ← unpackIndicesBE commitmentIndicesBE
    let cellIndices       ← unpackIndicesBE cellIndicesBE
    if cellIndices.size ≠ commitmentIndices.size then
      throw (.inputLengthMismatch "cellIndices" commitmentIndices.size cellIndices.size)
    if cosetsEvals.size ≠ commitmentIndices.size then
      throw (.inputLengthMismatch "cosetsEvals" commitmentIndices.size cosetsEvals.size)
    if proofs.size ≠ commitmentIndices.size then
      throw (.inputLengthMismatch "proofs" commitmentIndices.size proofs.size)
    if let some cb := commitments.find? (fun cb => cb.size != Constants.BYTES_PER_COMMITMENT) then
      throw (.badCommitmentSize cb.size)
    for i in [:commitments.size] do
      match bytesToKzgCommitment commitments[i]! with
      | .ok _    => pure ()
      | .error _ => throw (.invalidCommitment (some i))
    if commitmentIndices.any (· ≥ commitments.size) then
      throw .commitmentIndexOutOfBounds
    if cellIndices.any (· ≥ Constants.CELLS_PER_EXT_BLOB) then
      throw .cellIndexOutOfBounds
    if let some pb := proofs.find? (fun pb => pb.size != Constants.BYTES_PER_PROOF) then
      throw (.badProofSize pb.size)
    for i in [:proofs.size] do
      match bytesToKzgProof proofs[i]! with
      | .ok _    => pure ()
      | .error _ => throw (.invalidProof (some i))
    let evals : Array CosetEvals ← cosetsEvals.mapM fun ce =>
      cellToCosetEvals ce
    return blsFieldToBytes
      (computeVerifyCellKzgProofBatchChallenge
        commitments commitmentIndices cellIndices evals proofs)

@[export eth_kzg_compute_cells_and_kzg_proofs]
def computeCellsAndKzgProofsExport (blob : ByteArray) : IO ByteArray := do
  let (cells, proofs) ← runKzg (computeCellsAndKzgProofs blob)
  let cellsBuf  := cells.foldl  (· ++ ·) ByteArray.empty
  let proofsBuf := proofs.foldl (· ++ ·) ByteArray.empty
  return cellsBuf ++ proofsBuf

@[export eth_kzg_verify_cell_kzg_proof_batch]
def verifyCellKzgProofBatchExport
    (commitments : Array ByteArray)
    (cellIndicesBE : ByteArray)
    (cells : Array ByteArray)
    (proofs : Array ByteArray) : IO UInt8 := do
  let ok ← runKzg do
    let cellIndices ← unpackIndicesBE cellIndicesBE
    verifyCellKzgProofBatch commitments cellIndices cells proofs
  return if ok then 1 else 0

@[export eth_kzg_recover_cells_and_kzg_proofs]
def recoverCellsAndKzgProofsExport
    (cellIndicesBE : ByteArray) (cells : Array ByteArray) : IO ByteArray := do
  let (cells', proofs') ← runKzg do
    let cellIndices ← unpackIndicesBE cellIndicesBE
    recoverCellsAndKzgProofs cellIndices cells
  let cellsBuf  := cells'.foldl  (· ++ ·) ByteArray.empty
  let proofsBuf := proofs'.foldl (· ++ ·) ByteArray.empty
  return cellsBuf ++ proofsBuf

end EthLib.Cryptography.Kzg.Exports
