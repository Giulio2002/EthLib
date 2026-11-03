# Amsterdam transaction state

Transaction-original storage is needed when a storage write charges gas based on the value at the start of the transaction.
`TransactionState.State.parent` is an effective world at that point, after any earlier block writes have been applied.
The model returns zero for an address recorded as created in the transaction; otherwise it reads the parent world.
It does not model the construction of the parent world or charge gas.

The source is `ethereum/execution-specs` revision `fd9298410ec7218838c8348f69c1eb633f1797dc`, `src/ethereum/forks/amsterdam/state_tracker.py`, functions `get_storage_original`, `copy_tx_state`, and `restore_tx_state`.
The SHA-256 of that file is `b8a6082a210bcfdfc51e1487589a0b3ddfdd3b36ceee9dab6783f6bfca1f6229`.

A snapshot contains account writes, storage writes, code writes, storage clears, and transient storage.
Rollback restores those five fields while preserving the current parent, account reads, storage reads, and created accounts.
Commit discards the top snapshot and retains current fields.
Both operations reject an empty snapshot stack.
The snapshot stack and commit operation are a pure bookkeeping interface for nested use; the source exposes copy and restore rather than this stack.
Lists allow duplicate entries, and no chain validity is assumed.

The proof module gives success and error converses and a nested example in which an inner commit is followed by an outer rollback.
The ordinary and proof consumers are `tests/evm/TransactionStateOrdinary.lean` and `tests/evm/TransactionStateProof.lean`.
This bookkeeping does not yet implement tracker reads and writes, access lists, frame execution, calls, or host refinement.

`EthLib.EVM.Proofs.TransactionStateReference` defines a separate observation model.
It treats each finite map as a total lookup function, each set as a membership predicate, and the saved scopes as a stack of observations.
The model gives relations for original-storage selection, save, commit, and rollback without calling the executable transitions.
Every concrete success satisfies its relation, and every related concrete observation agrees with the actual successful result.
The error and success conditions characterize an empty or nonempty observed stack.
The field contract covers every saved field, all parent observations, both read sets, and the created set.
The nested relation allows arbitrary intervening observations provided the saved stack has the stated two scopes.
These claims apply to all accepted lists, including repeated entries.
