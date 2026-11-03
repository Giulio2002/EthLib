module

public import EthLib.EVM.World

/-!
# Amsterdam transaction state bookkeeping

The source is `forks/amsterdam/state_tracker.py` at execution-specs revision
`fd9298410ec7218838c8348f69c1eb633f1797dc`, functions
`get_storage_original`, `copy_tx_state`, and `restore_tx_state`.
The parent is the state at the start of the transaction.
Lists represent finite maps and sets; the first matching map entry wins.
This module does not implement frame execution or block access list construction.
-/

@[expose] public section
namespace EthLib.EVM.TransactionState

open World

/-- Fields copied by `copy_tx_state` and restored by `restore_tx_state`. -/
structure Snapshot where
  accountWrites : List (Address × Option Account) := []
  storageWrites : List ((Address × Word) × Word) := []
  codeWrites : List (Word × ByteArray) := []
  storageClears : List Address := []
  transientStorage : List ((Address × Word) × Word) := []

/-- Transaction state and nested snapshots, with reads retained across rollback. -/
structure State where
  parent : World.State
  writes : Snapshot := {}
  accountReads : List Address := []
  storageReads : List (Address × Word) := []
  createdAccounts : List Address := []
  snapshots : List Snapshot := []

/-- Original storage ignores transaction writes and is zero for created accounts. -/
def getStorageOriginal (s : State) (a : Address) (k : Word) : Word :=
  if s.createdAccounts.contains a then 0 else World.getStorage s.parent a k

/-- Save the revertible fields at the top of the nested snapshot stack. -/
def snapshot (s : State) : State :=
  { s with snapshots := s.writes :: s.snapshots }

/-- An empty stack cannot be committed or rolled back. -/
inductive SnapshotError where
  | noSnapshot
  deriving DecidableEq, Repr

/-- Discard the top snapshot while retaining current writes. -/
def commit (s : State) : Except SnapshotError State :=
  match s.snapshots with
  | [] => .error .noSnapshot
  | _ :: rest => .ok { s with snapshots := rest }

/-- Restore the top snapshot, preserving reads and created accounts. -/
def rollback (s : State) : Except SnapshotError State :=
  match s.snapshots with
  | [] => .error .noSnapshot
  | saved :: rest => .ok { s with writes := saved, snapshots := rest }

end EthLib.EVM.TransactionState
