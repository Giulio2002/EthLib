module

public import EthLib.EVM.Word
public import EthLib.EVM.BlobFee

/-!
# Immutable message environment

Cancun execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`,
`vm/__init__.py`, `vm/instructions/block.py`, and
`vm/instructions/environment.py` define these fields.
Number, gas limit, and base fee are restricted to values accepted by U256.
PREVRANDAO is the big-endian decoded value of the source bytes.
The gas price is restricted to the U256 domain accepted by GASPRICE.
The context supplies metadata and does not execute calls or transactions.
-/

@[expose] public section
namespace EthLib.EVM.Environment

/-- A 160-bit account address interpreted as an unsigned big-endian integer. -/
abbrev Address := Fin (2 ^ 160)

/-- Zero-extend the address to a stack word. -/
def addressWord (address : Address) : Word := BitVec.ofNat 256 address.val

/-- Immutable metadata supplied to a message frame. -/
structure Context where
  currentTarget : Address
  origin : Address
  caller : Address
  value : Word
  gasPrice : Word
  /-- Cancun `vm/__init__.py`, `BlockEnvironment.coinbase`. -/
  coinbase : Address
  /-- Cancun `BlockEnvironment.time` is U256. -/
  timestamp : Word
  /-- The accepted U256 domain of Cancun `BlockEnvironment.number`. -/
  number : Word
  /-- The big-endian decoded Cancun `BlockEnvironment.prev_randao`. -/
  prevRandao : Word
  /-- The accepted U256 domain of Cancun `BlockEnvironment.block_gas_limit`. -/
  gasLimit : Word
  /-- Cancun `BlockEnvironment.chain_id` is U64. -/
  chainId : Fin (2 ^ 64)
  /-- The accepted U256 domain of Cancun `BlockEnvironment.base_fee_per_gas`. -/
  baseFee : Word
  /-- Cancun `BlockEnvironment.excess_blob_gas` is U64. -/
  excessBlobGas : Fin (2 ^ 64)
  /-- Transaction versioned hashes, decoded from 32-byte big-endian values. -/
  blobVersionedHashes : List Word
  /-- Previous block hashes, oldest first, decoded from 32-byte big-endian values. -/
  blockHashes : List Word

/-- Cancun `environment.py`, `blob_hash`, indexes without narrowing the word. -/
def blobHash (context : Context) (index : Word) : Word :=
  (context.blobVersionedHashes[index.toNat]?).getD 0

/-- A history is ordered by increasing block number.

Cancun `fork.py`, `get_last_256_block_hashes`, constructs this order.
Each word is the big-endian decoding of a 32-byte hash.
-/
abbrev BlockHistory := List Word

/-- The supplied suffix covers every block that EELS may index. -/
def HistoryCoversWindow (history : BlockHistory) (current : Word) : Prop :=
  min current.toNat 256 ≤ history.length

/-- The history covers the window and agrees with the supplied chain.

The oldest entry can be the parent of genesis and has no natural block number.
The remaining entries use the age-based index of Cancun `block_hash`.
The relation assumes the chain hashes; it does not validate headers.
-/
def HistoryMatches (history : BlockHistory) (current : Word) (chain : Nat → Word) : Prop :=
  HistoryCoversWindow history current ∧ history.length ≤ 256 ∧
  history.length ≤ current.toNat + 1 ∧
  ∀ i (h : i < history.length), history.length ≤ current.toNat + i →
    history[i]'h = chain (current.toNat + i - history.length)

/-- Cancun `block.py`, `block_hash`, with a total extension for short history.

The source raises an index error when a requested in-window hash is missing.
This function returns zero in that case.
The block number is restricted to the existing U256 context domain.
-/
def blockHash (history : BlockHistory) (current index : Word) : Word :=
  if index.toNat < current.toNat ∧ current.toNat ≤ index.toNat + 256 then
    if current.toNat - index.toNat ≤ history.length then
      (history[history.length - (current.toNat - index.toNat)]?).getD 0
    else 0
  else 0

end EthLib.EVM.Environment
