# Amsterdam transaction tracker value transfer

`moveEther` transfers value by modifying the sender and then the recipient.
The recipient is read after the sender modification, so the two addresses may be equal.
The operation uses the existing tracker and its empty-account cleanup and read-set rules.
It leaves frame execution, gas, transfer logs, and transaction admission to their callers.

The source is `ethereum/execution-specs` revision `fd9298410ec7218838c8348f69c1eb633f1797dc`, `src/ethereum/forks/amsterdam/state_tracker.py`, `move_ether` and `modify_state`.
Its SHA-256 is `b8a6082a210bcfdfc51e1487589a0b3ddfdd3b36ceee9dab6783f6bfca1f6229`.
The same revision pins `ethereum-types` 0.4.1 in `uv.lock`.
The package archive SHA-256 is `c0eee4464c42ed8217dfc927400db98157cc8b09252ecefa703176496dbe3b4d`.
Its `ethereum_types/numeric.py` has SHA-256 `47d040d4de043e46d19c2fd9f74b318396b6c83ab01fe346f98a3c477e58db46`.
`Unsigned.__add__` and `__sub__`, together with `FixedUnsigned._in_range`, reject results outside `0 <= x < 2^256`.
`ethereum_types/frozen.py` has SHA-256 `50998345b38977de4c5d92b136f00dc30180add2215c59485a513daeef3b3418`.
Its `modify` applies the callback to a copy before returning it, so a callback failure does not write the copy back.

The sender is read before its balance assertion.
If it lacks funds, the typed error carries the state after that read.
Otherwise the sender modification and any empty-account cleanup finish before the recipient is read.
A recipient sum at least `2^256` produces a typed error carrying the state after the debit and recipient read.
These errors expose source failure boundaries as a total Lean API; they are not assigned EVM exceptional-halt meanings.
A successful subtraction and addition are proved to represent the natural-number results without modular reduction.
The immutable transaction-start parent is not replaced by an overlay.

For equal addresses, the credit sees the debited account.
Its final balance is the initial balance when the sender has enough funds.
An intermediate empty account can still be destroyed, clearing storage and recording reads, before the credit recreates it.
A direct zero transfer executes both modifications.
The source's `vm/interpreter.py`, `process_call`, invokes `move_ether` only when transfer is enabled and value is nonzero; `vm/instructions/system.py`, `selfdestruct`, invokes it on the originator's balance.
`vm/instructions/system.py`, `call` and `callcode`, pass an insufficient-balance flag to `generic_call`, which aborts in preflight before spawning the child.
These caller rules are context, not part of this operation.
The SHA-256 hashes of `vm/interpreter.py` and `vm/instructions/system.py` are `8dd244e747b1b1516ba90de947f9f0d5db84bab4dc51256af0db8dd7a051fd7c` and `d6d4df0e26882b26da44c535d4a29d2e8ef61d76da407290be51d403a5356c4b`.

| Operation or property | Contract | Consumers |
| --- | --- | --- |
| Ordered source effects | `moveEther_refines` and `InsufficientSpec`, `OverflowSpec`, `SuccessSpec` | `TransactionTransferProof`, `TransactionTransferOrdinary` |
| Insufficient, overflow and success boundaries | `insufficient_iff`, `overflow_iff`, `success_iff` | `TransactionTransferProof`, `TransactionTransferOrdinary` |
| Checked arithmetic | `debit_exact`, `credit_exact` | `TransactionTransferProof`, `TransactionTransferOrdinary` |
| Distinct and equal addresses | `success_distinct_balances`, `success_distinct_conservation`, `success_self_balance`, `self_success_iff` | `TransactionTransferProof`, `TransactionTransferOrdinary` |
| Other addresses and retained fields | `success_other_account`, `success_other_storage`, `success_retained`, `success_accountReads` | `TransactionTransferProof`, `TransactionTransferOrdinary` |
| Nested rollback | `success_snapshots`, `error_snapshots`, `nested_rollback`, `nested_error_rollback` | `TransactionTransferProof`, `TransactionTransferOrdinary` |

The reference relations use the transaction tracker's independent map and set observations, including duplicate concrete entries.
The concrete examples use synthetic tracker states; they do not assert chain validity or code-hash consistency.
The ordinary consumer executes 52 checks for insufficient and overflow errors, the last in-range sum, exact funds, absent and tombstoned accounts, zero and self transfers, cleanup, and rollback.
The proof consumer applies the universal contracts.
No full EVM, transaction, block, or Amsterdam conformance is claimed.
