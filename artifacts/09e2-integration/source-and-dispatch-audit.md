# Historical 09e2 source and dispatch audit

The source revision is `fd9298410ec7218838c8348f69c1eb633f1797dc` in `ethereum/execution-specs`.
The source is Python, and inspection is not a proof of its equivalence to Lean.
The following correspondence is scoped to Cancun and the supplied frame inputs.

Cancun `fork.py`, `get_last_256_block_hashes`, constructs an oldest-first list from up to 255 headers and their parent hashes.
Cancun `vm/instructions/block.py`, `block_hash`, pops the full U256 query, charges 20 gas, and indexes by negative age in the 256-block window.
It uses an unbounded `Uint` for the current block number.
The Lean context uses a word, so correspondence requires a source number below `2^256` and matching decoded word.
`HistoryMatches` requires coverage, an upper bound of 256 entries, and agreement with supplied chain words.
It allows a leading genesis-parent entry and does not validate headers or ancestry.
A source execution with an unavailable in-window list entry raises an indexing error.
The total Lean helper returns zero in that case.
Outside the window, both the source operation and Lean return zero.

Cancun `vm/instructions/environment.py`, `blob_hash`, pops a U256 index, charges three gas, and selects a 32-byte transaction hash or zero.
The caller supplies the list in transaction order and each word must be the big-endian decoding of its source bytes.
The context neither validates the transaction nor derives versioned hashes from commitments.
`blob_base_fee` charges two gas, computes the fee from U64 excess blob gas, and converts it to U256 before the stack push.
Cancun `vm/gas.py`, `calculate_blob_gas_price`, uses factor 1 and denominator 3338477.
The source conversion requires the computed fee to be less than `2^256`.
Lean instead wraps larger natural values modulo `2^256` as a total extension.
The mathematical recurrence termination proof does not establish practical runtime for every U64 input.

The combined theorem requires a covered matching history and an in-window query only for its exact chain-hash corollary.
It requires the computed Cancun fee to fit a word for the checked-conversion result.
Its universal theorem uses neither premise and retains both total extensions.
Neither theorem proves that supplied chain or transaction data is valid.

The source paths at the pinned revision are:

- `src/ethereum/forks/cancun/fork.py`, `get_last_256_block_hashes`.
- `src/ethereum/forks/cancun/vm/instructions/block.py`, `block_hash` and `number`.
- `src/ethereum/forks/cancun/vm/instructions/environment.py`, `blob_hash` and `blob_base_fee`.
- `src/ethereum/forks/cancun/vm/gas.py`, `calculate_blob_gas_price` and `GasCosts`.
- `src/ethereum/forks/amsterdam/vm/instructions/block.py`, `block_hash` and `number`.
- `src/ethereum/forks/amsterdam/vm/instructions/environment.py`, `blob_hash` and `blob_base_fee`.
- `src/ethereum/forks/amsterdam/vm/gas.py`, `calculate_blob_gas_price` and `GasCosts`.

The source binding is `0x40` BLOCKHASH to the stack query and block history, `0x90` SWAP1 to the top two stack words, `0x49` BLOBHASH to the transaction hash list, `0x43` NUMBER to the supplied block number, and `0x4a` BLOBBASEFEE to the supplied excess blob gas.
The combined input stack is `[block_number_query, blob_index, ...]`.
The output stack is `[blob_fee, current_number, blob_hash, block_hash, ...]`.
The gas costs are 20, 3, 3, 2, and 2, respectively.
The total is 30 gas, and five runner steps exhaust fuel after PC 5.

`tests/evm/Milestone09cIntegrationDispatch.lean` independently enumerates all 256 unique bytes.
It compares the Cancun reference table, decoder, unsupported classification, and executable frame dispatch.
Its guarded output counts 125 supported, 23 unsupported, 107 unassigned, and one designated INVALID byte.
The executable step groups the last two cases as 108 invalid results.
These are Cancun slice counts, not Amsterdam opcode coverage.
The Amsterdam source adds instructions and changes the blob fee update fraction to 11684671.
Its gas file gives target 14 and maximum 21 blobs in the pinned snapshot.
Those constants alone do not model the intervening excess-gas transition or fork configuration.
