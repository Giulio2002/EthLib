module

public import EthLib.EVM.Word

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
  /-- Transaction versioned hashes, decoded from 32-byte big-endian values. -/
  blobVersionedHashes : List Word

/-- Cancun `environment.py`, `blob_hash`, indexes without narrowing the word. -/
def blobHash (context : Context) (index : Word) : Word :=
  (context.blobVersionedHashes[index.toNat]?).getD 0

end EthLib.EVM.Environment
