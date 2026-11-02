# Amsterdam account and storage source checkpoint

Revision: `fd9298410ec7218838c8348f69c1eb633f1797dc` of `ethereum/execution-specs`.
The following SHA-256 hashes cover the raw source files at that revision.

- `src/ethereum/state.py`: `e5973ead6711054144b05e78a4052ea03e808ff10189ffa227077b2dc5612b2d`.
- `src/ethereum/state_mpt.py`: `bec5a5621ab7d4488dd073ae440015358b6e768bb4d661d6d5b1733d3e41cb96`.
- `src/ethereum/forks/amsterdam/state_tracker.py`: `b8a6082a210bcfdfc51e1487589a0b3ddfdd3b36ceee9dab6783f6bfca1f6229`.
- `src/ethereum/forks/amsterdam/fork_types.py`: `3e0013e251867df02aca7b746b77403b36b41d73f7c4158bed09964838c935ca`.

`state.py` defines an address as `Bytes20` and an account as `(nonce: Uint, balance: U256, code_hash: Hash32)`.
The empty account has zero nonce, zero balance, and the hash of empty code.
An absent account is distinct from this account.
The existing `Environment.Address` and `Word` can represent addresses and 32-byte keys and values by big-endian decoding.
The nonce must not be narrowed to 64 or 256 bits.
Account code is represented by its hash in the source, with a separate code store.

The following mathematical model specifies observable state independently of a representation.
Let `A` be a finite partial map from addresses to accounts, and `S` a finite partial map from address and key pairs to nonzero words.
The account and storage maps are independent, so storage may remain at an address whose account is absent.
A lookup of an absent storage pair returns zero.
The optional account lookup returns `A(a)`; the defaulting lookup returns the empty account when `A(a)` is absent.
An account exists exactly when `A(a)` is defined.
It exists and is empty exactly when `A(a)` is defined and equals the empty account.
It is alive exactly when `A(a)` is defined and differs from the empty account.

Setting an optional account at `a` changes only `A(a)` and does not alter `S`.
Setting storage at `(a,k)` requires `A(a)` to be defined; it replaces only `S(a,k)`, removing that pair if the value is zero.
Destroying storage at `a` removes all pairs with first component `a`, without altering `A`.
Destroying an account at `a` removes `A(a)` and destroys storage at `a`.
These rules do not assert that arbitrary pairs `(A,S)` are valid blockchain states.

`state_tracker.modify_state` starts with the defaulting account lookup, applies its update, and sets the account.
If the resulting account is empty, it destroys both account and storage.
`set_account_balance`, `increment_nonce`, and `set_code` use this rule.
`set_code` hashes bytes and records nonempty code in the separate code store.
`set_storage` asserts presence and does not create an account.
`state_mpt.set_storage` deletes zero entries, while the tracker can record a zero write before applying the block diff.
Transaction-original storage, snapshots, access tracking, transfers, and host refinement remain outside this model.

The parent 10 plan also requires nested commit and rollback and host simulation in later work.
The abstract model describes the observable effect of the pure API.

## API and proof map

`EthLib.EVM.World` exposes `Account`, `State`, account queries, and storage queries.
The lists are finite by construction and accept duplicate keys.
The first matching entry is the observable value.
The type of every address and word enforces its width.
All natural nonce values are accepted.
No chain validity or code-hash consistency is implied.

`setAccount` changes an optional account entry without changing storage.
`setStorage` rejects an absent account and removes all prior entries for the slot.
It adds the new entry only when its value is nonzero.
`destroyStorage` clears only storage.
`destroyAccount` removes the account and clears storage.
`modifyState` applies the source's empty-account cleanup rule.

`getCode` looks up a separately supplied code store.
It always returns empty bytes for the empty-code hash.
For other absent hashes it returns `none`, an explicit extension of the provider interface.
The caller must ensure that bytes in the supplied store match their hashes.
Hashing code and updating the code store are reserved for a later child.

`EthLib.EVM.Proofs.World` states pointwise update and destruction contracts.
It proves account presence and emptiness characterizations and checked storage error and success cases.
Overwrite and commutation compare account and storage queries pointwise.
The relation also requires the code lists to be literally equal.
It is stronger than equality of all code query results.
The composed `write_then_destroy` theorem covers a storage write followed by account destruction.
The ordinary and proof consumers are `tests/evm/WorldOrdinary.lean` and `tests/evm/WorldProof.lean`.

Transaction-original storage, transfers, snapshots, host refinement, and frame execution are outside this child.
