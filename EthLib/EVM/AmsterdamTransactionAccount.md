# Amsterdam account and code tracker subset

The transaction tracker keeps account and code writes separate from the world at the start of the transaction.
A deletion is an explicit account-overlay entry, and code is addressed by a 32-byte hash.
Keeping these writes in the tracker preserves the read and rollback effects that belong to transaction execution.

The source is `ethereum/execution-specs` revision `fd9298410ec7218838c8348f69c1eb633f1797dc`, `src/ethereum/forks/amsterdam/state_tracker.py`, SHA-256 `b8a6082a210bcfdfc51e1487589a0b3ddfdd3b36ceee9dab6783f6bfca1f6229`.
The supplied parent is the effective world at transaction start, including any earlier block writes.
The functions are `get_code`, `destroy_account`, `modify_state`, `set_account_balance`, `increment_nonce`, and `set_code`.

`getCode` returns empty bytes for the empty-code hash before consulting either store.
For other hashes it checks the transaction overlay before the parent code store.
`none` is an explicit library boundary for a missing nonempty hash in the supplied stores.
It does not claim that a valid chain state has missing code.

`modifyState` reads the defaulting account, writes the updated account, then reads it again to check emptiness.
If the result is empty, `destroyAccount` clears its storage before writing a tombstone.
Storage entries removed by this clear become storage reads.
The initial parent, created-account markers, and saved snapshot stack remain unchanged.
Account reads and storage reads survive rollback.

`setCode` hashes the bytes and records them before modifying the account when the hash is not the empty-code hash.
It uses `World.codeHash`, whose byte and independent bit-sponge refinements are in `EthLib.EVM.Proofs.World`.
Neither the implementation nor its contracts assume the hash is injective.
A caller supplies a code store consistent with the hashes it contains.

The proof module states independent map and set observations for code lookup, deletion, and account modification.
`ModifySpec` covers every account, storage, clear, read, code, transient, parent, created, and snapshot observation.
`CodeInsert` describes code recording before that transition.
The empty-hash branch, missing-code boundary, and rollback are separate contracts.
These operations are total except that `getCode` explicitly returns `none` for missing supplied code.
This subset does not implement transfer, gas, frame, call, or block processing.

| Source operation | Lean operation | Contracts | Consumers |
| --- | --- | --- | --- |
| `get_code` | `getCode` | `getCode_spec`, `getCode_none_iff`, `getCode_some_iff`, `getCode_empty` | `TransactionAccountOrdinary`, `TransactionAccountProof` |
| `destroy_account` | `destroyAccount` | `destroyAccount_spec` | `TransactionAccountOrdinary`, `TransactionAccountProof` |
| `modify_state` | `modifyState` | `modifyState_refines` and its field contracts | `TransactionAccountOrdinary`, `TransactionAccountProof` |
| `set_account_balance` | `setAccountBalance` | `setAccountBalance_refines` | `TransactionAccountOrdinary` checks cleanup and nonzero retention; `TransactionAccountProof` applies the contract |
| `increment_nonce` | `incrementNonce` | `incrementNonce_refines` | `TransactionAccountOrdinary`, `TransactionAccountProof` |
| `set_code` | `setCode` | `setCode_refines`, `setCode_accounts`, `setCode_code` | `TransactionAccountOrdinary` checks empty-code cleanup and nonempty code; `TransactionAccountProof` applies the contracts |

The ordinary consumer runs 81 concrete checks, including empty-code cleanup with duplicate storage entries, nonzero balance retention, an account absent from both stores, a nonempty parent-only account, and nested mutation and rollback.
The proof consumer applies the reference contracts and the existing hash refinement.
The new module extends the tracker API and does not alter the existing transaction state or tracker definitions.
