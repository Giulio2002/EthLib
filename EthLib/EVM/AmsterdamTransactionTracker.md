# Amsterdam transaction tracker subset

A transaction reads the world at its start through a write overlay.
The effective parent world is supplied by the caller and includes any prior block changes.
The original parent never changes during these operations.

The source is `ethereum/execution-specs` revision `fd9298410ec7218838c8348f69c1eb633f1797dc`, `src/ethereum/forks/amsterdam/state_tracker.py`, SHA-256 `b8a6082a210bcfdfc51e1487589a0b3ddfdd3b36ceee9dab6783f6bfca1f6229`.
The functions are `get_account_optional`, `get_account`, `get_storage`, `set_account`, `set_storage`, `destroy_storage`, `get_transient_storage`, `set_transient_storage`, and `mark_account_created`.

Account writes shadow the parent even when the write deletes an account.
Storage writes shadow storage clears, and clears shadow the parent.
Account and persistent storage reads record their keys.
A storage write also records its account read before checking existence.
The error contains the state after that read, so the effect is retained.
Zero persistent writes remain explicit, while zero transient writes delete the entry.
Clearing storage removes all writes at the address and records their keys as reads.
Created-account markers survive rollback and cause original storage to read as zero.

Association lists use their first entry and may contain duplicates.
Read and clear lists represent sets by membership.
The reference contracts use map and set observations and quantify over arbitrary inputs.
The snapshot proof connects two checked writes around nested snapshots to an inner rollback.
This subset does not implement the complete state tracker, gas, frames, calls, block processing, or host refinement.

| Source operation | Lean operation | Contract | Consumers |
| --- | --- | --- | --- |
| `get_account_optional` | `getAccountOptional` | `getAccountOptional_spec` | `TransactionTrackerOrdinary`, `TransactionTrackerProof` |
| `get_account` | `getAccount` | `getAccount_spec` | `TransactionTrackerOrdinary`, `TransactionTrackerProof` |
| `get_storage` | `getStorage` | `getStorage_spec` | `TransactionTrackerOrdinary`, `TransactionTrackerProof` |
| `set_account` | `setAccount` | `setAccount_spec` | `TransactionTrackerOrdinary`, `TransactionTrackerProof` |
| `set_storage` | `setStorage` | `setStorage_spec`, `setStorage_error_iff`, `setStorage_success_iff` | `TransactionTrackerOrdinary`, `TransactionTrackerProof` |
| `destroy_storage` | `destroyStorage` | `destroyStorage_storage`, `destroyStorage_reads`, `destroyStorage_effects` | `TransactionTrackerOrdinary`, `TransactionTrackerProof` |
| `get_transient_storage` | `getTransientStorage` | `getTransientStorage_spec` | `TransactionTrackerOrdinary`, `TransactionTrackerProof` |
| `set_transient_storage` | `setTransientStorage` | `setTransientStorage_spec` | `TransactionTrackerOrdinary`, `TransactionTrackerProof` |
| `mark_account_created` | `markAccountCreated` | `markAccountCreated_spec`, `markAccountCreated_preserves` | `TransactionTrackerOrdinary`, `TransactionTrackerProof` |

`TransactionTrackerProgram` defines a program that composes two checked storage writes with nested snapshots and an inner rollback.
Its conditional theorem gives observations when both writes succeed.
`TransactionTrackerConcrete` imports the ordinary EVM library and evaluates a concrete successful execution with nonempty metadata and duplicate entries.
It checks the resulting fields and the saved snapshot against explicit values, and runs the same cases through Lean's evaluator.
