module

public import EthLib.EVM.TransactionState

/-!
# Amsterdam transaction tracker operations

The source is `forks/amsterdam/state_tracker.py` at execution-specs revision
`fd9298410ec7218838c8348f69c1eb633f1797dc`.
The parent is the effective world at the start of this transaction.
Association lists use their first matching entry, and read lists represent sets.
-/

@[expose] public section
namespace EthLib.EVM.TransactionTracker

open World

abbrev State := TransactionState.State

/-- Amsterdam `get_account_optional`, including its recorded read. -/
def getAccountOptional (s : State) (a : Address) : Option Account × State :=
  let value := match s.writes.accountWrites.lookup a with
    | some value => value
    | none => World.getAccountOptional s.parent a
  (value, { s with accountReads := a :: s.accountReads })

/-- Amsterdam `get_account`, including its recorded read. -/
def getAccount (s : State) (a : Address) : Account × State :=
  let result := getAccountOptional s a
  (result.1.getD emptyAccount, result.2)

/-- Amsterdam `get_storage`, with writes taking priority over clears. -/
def getStorage (s : State) (a : Address) (k : Word) : Word × State :=
  let value := match s.writes.storageWrites.lookup (a, k) with
    | some value => value
    | none => if s.writes.storageClears.contains a then 0 else World.getStorage s.parent a k
  (value, { s with storageReads := (a, k) :: s.storageReads })

/-- Amsterdam `get_transient_storage` does not record a persistent storage read. -/
def getTransientStorage (s : State) (a : Address) (k : Word) : Word :=
  (s.writes.transientStorage.lookup (a, k)).getD 0

/-- Amsterdam `set_account` records a deletion as a present `none` write. -/
def setAccount (s : State) (a : Address) (value : Option Account) : State :=
  { s with writes := { s.writes with accountWrites := (a, value) :: s.writes.accountWrites } }

/-- The state accompanying a failed storage write retains the account read. -/
inductive StorageError where
  | missingAccount
  deriving DecidableEq, Repr

/-- Amsterdam `set_storage`, including the account read before its assertion.

A zero value remains an explicit write in the transaction overlay.
-/
def setStorage (s : State) (a : Address) (k value : Word) : Except (StorageError × State) State :=
  let result := getAccountOptional s a
  match result.1 with
  | none => .error (.missingAccount, result.2)
  | some _ => .ok { result.2 with writes := { result.2.writes with
      storageWrites := ((a, k), value) :: result.2.writes.storageWrites } }

/-- Amsterdam `destroy_storage` records written slots as reads before clearing them. -/
def destroyStorage (s : State) (a : Address) : State :=
  let removed := s.writes.storageWrites.filter (fun entry => entry.1.1 == a)
  let kept := s.writes.storageWrites.filter (fun entry => entry.1.1 != a)
  { s with
    storageReads := removed.map Prod.fst ++ s.storageReads
    writes := { s.writes with storageWrites := kept, storageClears := a :: s.writes.storageClears } }

/-- Amsterdam `mark_account_created`; the marker survives rollback. -/
def markAccountCreated (s : State) (a : Address) : State :=
  { s with createdAccounts := a :: s.createdAccounts }

/-- Amsterdam `set_transient_storage`, deleting every entry for a zero value. -/
def setTransientStorage (s : State) (a : Address) (k value : Word) : State :=
  let rest := s.writes.transientStorage.filter (fun entry => entry.1 != (a, k))
  let updated := if value == 0 then rest else ((a, k), value) :: rest
  { s with writes := { s.writes with transientStorage := updated } }

end EthLib.EVM.TransactionTracker
