module
import EthLib.EVM
public meta import EthLib.EVM

open EthLib.EVM EthLib.EVM.TransactionTransfer

/-! Concrete checked transfer cases with duplicate overlays and rollback. -/

private def payload : ByteArray := ⟨#[1, 2, 3]⟩
private def maxWord : Word :=
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
private def fixture : State where
  parent := {
    accounts := [(1, ⟨0, 10, World.emptyCodeHash⟩), (2, ⟨0, 5, World.emptyCodeHash⟩),
      (3, ⟨0, maxWord, World.emptyCodeHash⟩), (5, ⟨0, 8, World.emptyCodeHash⟩),
      (6, ⟨2, 7, 123⟩)]
    storage := [((1, 7), 90), ((6, 5), 80)]
    codes := [(123, payload)] }
  writes := {
    accountWrites := [(1, some ⟨0, 10, World.emptyCodeHash⟩), (1, none), (5, none)]
    storageWrites := [((1, 7), 11), ((1, 7), 22), ((6, 5), 33)]
    codeWrites := [(123, payload)]
    storageClears := [8]
    transientStorage := [((6, 9), 44)] }
  accountReads := [9]
  storageReads := [(6, 5)]
  createdAccounts := [4]
  snapshots := [{ storageWrites := [((7, 7), 77)] }]

private def successState (result : Except (TransferError × State) State) : Option State :=
  match result with | .ok s => some s | .error _ => none

private def errorKind (result : Except (TransferError × State) State) : Option TransferError :=
  match result with | .ok _ => none | .error (e, _) => some e

private def errorState (result : Except (TransferError × State) State) : Option State :=
  match result with | .ok _ => none | .error (_, s) => some s

private def normal : Option State := successState (moveEther fixture 1 2 3)
private def exactFunds : Option State := successState (moveEther fixture 1 2 10)
private def selfExact : Option State := successState (moveEther fixture 1 1 10)
private def zeroSelf : Option State := successState (moveEther fixture 4 4 0)
private def overflow : Except (TransferError × State) State := moveEther fixture 1 3 1
private def insufficient : Except (TransferError × State) State := moveEther fixture 1 2 11
private def overflowAfterCleanup : Except (TransferError × State) State := moveEther fixture 1 3 10
private def almostMax : Word :=
  0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe
private def boundaryFixture : State :=
  { fixture with writes := { fixture.writes with accountWrites :=
      (3, some ⟨0, almostMax, World.emptyCodeHash⟩) :: fixture.writes.accountWrites } }

private def rolledBack : Option State :=
  match moveEther (TransactionState.snapshot (TransactionState.snapshot fixture)) 1 2 3 with
  | .error _ => none
  | .ok result =>
    match TransactionState.rollback result with
    | .error _ => none
    | .ok restored => some restored

private def requireCase (label : String) (ok : Bool) : IO Unit := do
  if !ok then throw (IO.userError label)

#eval do
  requireCase "normal sender" (decide (normal.map (fun (s : State) => (TransactionTracker.getAccount s 1).1.balance) = some 7))
  requireCase "normal recipient" (decide (normal.map (fun (s : State) => (TransactionTracker.getAccount s 2).1.balance) = some 8))
  requireCase "normal reads" (decide (normal.map (fun (s : State) => s.accountReads) = some [2, 2, 1, 1, 9]))
  requireCase "normal storage" (decide (normal.map (fun (s : State) => s.writes.storageWrites) =
    some [((1, 7), 11), ((1, 7), 22), ((6, 5), 33)]))
  requireCase "insufficient kind" (decide (errorKind insufficient = some TransferError.insufficientBalance))
  requireCase "insufficient read" (decide ((errorState insufficient).map (fun (s : State) => s.accountReads) = some [1, 9]))
  requireCase "insufficient unchanged writes" (decide ((errorState insufficient).map (fun (s : State) => s.writes.storageWrites) =
    some [((1, 7), 11), ((1, 7), 22), ((6, 5), 33)]))
  requireCase "overflow kind" (decide (errorKind overflow = some TransferError.recipientOverflow))
  requireCase "overflow after debit" (decide ((errorState overflow).map (fun (s : State) =>
    (TransactionTracker.getAccount s 1).1.balance) = some 9))
  requireCase "overflow recipient read" (decide ((errorState overflow).map (fun (s : State) => s.accountReads) = some [3, 1, 1, 9]))
  requireCase "exact funds sender" (decide (exactFunds.map (fun (s : State) => s.writes.accountWrites.lookup 1) = some (some none)))
  requireCase "exact funds recipient" (decide (exactFunds.map (fun (s : State) => (TransactionTracker.getAccount s 2).1.balance) = some 15))
  requireCase "cleanup duplicate writes" (decide (exactFunds.map (fun (s : State) => s.writes.storageWrites) = some [((6, 5), 33)]))
  requireCase "cleanup duplicate reads" (decide (exactFunds.map (fun (s : State) => s.storageReads) = some [(1, 7), (1, 7), (6, 5)]))
  requireCase "absent sender insufficient" (decide (errorKind (moveEther fixture 4 2 1) = some TransferError.insufficientBalance))
  requireCase "tombstone sender insufficient" (decide (errorKind (moveEther fixture 5 2 1) = some TransferError.insufficientBalance))
  requireCase "absent recipient created" (decide ((successState (moveEther fixture 1 4 3)).map
    (fun (s : State) => (TransactionTracker.getAccount s 4).1.balance) = some 3))
  requireCase "self balance restored" (decide (selfExact.map (fun (s : State) => (TransactionTracker.getAccount s 1).1.balance) = some 10))
  requireCase "self cleanup persists" (decide (selfExact.map (fun (s : State) => s.writes.storageWrites) = some [((6, 5), 33)]))
  requireCase "self duplicate reads" (decide (selfExact.map (fun (s : State) => s.storageReads) = some [(1, 7), (1, 7), (6, 5)]))
  requireCase "self reads" (decide (selfExact.map (fun (s : State) => s.accountReads) = some [1, 1, 1, 1, 9]))
  requireCase "zero direct reads" (decide (zeroSelf.map (fun (s : State) => s.accountReads) = some [4, 4, 4, 4, 9]))
  requireCase "zero direct cleanup" (decide (zeroSelf.map (fun (s : State) => s.writes.storageClears) = some [4, 4, 8]))
  requireCase "rollback account writes" (decide (rolledBack.map (fun (s : State) => s.writes.accountWrites) =
    some [(1, some (⟨0, 10, World.emptyCodeHash⟩ : World.Account)), (1, none), (5, none)]))
  requireCase "rollback storage writes" (decide (rolledBack.map (fun (s : State) => s.writes.storageWrites) =
    some [((1, 7), 11), ((1, 7), 22), ((6, 5), 33)]))
  requireCase "rollback account reads" (decide (rolledBack.map (fun (s : State) => s.accountReads) = some [2, 2, 1, 1, 9]))
  requireCase "rollback storage reads" (decide (rolledBack.map (fun (s : State) => s.storageReads) = some [(6, 5)]))
  requireCase "rollback code" (decide (rolledBack.map (fun (s : State) => s.writes.codeWrites) = some [(123, (⟨#[1, 2, 3]⟩ : ByteArray))]))
  requireCase "rollback created" (decide (rolledBack.map (fun (s : State) => s.createdAccounts) = some [4]))
  requireCase "rollback transient" (decide (rolledBack.map (fun (s : State) => s.writes.transientStorage) = some [((6, 9), 44)]))
  requireCase "rollback clears" (decide (rolledBack.map (fun (s : State) => s.writes.storageClears) = some [8]))
  requireCase "rollback parent storage" (decide (rolledBack.map (fun (s : State) => s.parent.storage) =
    some [((1, 7), 90), ((6, 5), 80)]))
  requireCase "rollback snapshots" (decide (rolledBack.map (fun (s : State) => s.snapshots.length) = some 2))
  requireCase "last valid recipient sum" (decide ((successState (moveEther boundaryFixture 1 3 1)).map
    (fun (s : State) => (TransactionTracker.getAccount s 3).1.balance) = some maxWord))
  requireCase "overflow after cleanup kind" (decide (errorKind overflowAfterCleanup = some TransferError.recipientOverflow))
  requireCase "overflow after cleanup tombstone" (decide ((errorState overflowAfterCleanup).map
    (fun (s : State) => s.writes.accountWrites.lookup 1) = some (some none)))
  requireCase "overflow after cleanup storage" (decide ((errorState overflowAfterCleanup).map
    (fun (s : State) => s.writes.storageWrites) = some [((6, 5), 33)]))
  requireCase "overflow after cleanup reads" (decide ((errorState overflowAfterCleanup).map
    (fun (s : State) => s.storageReads) = some [(1, 7), (1, 7), (6, 5)]))
  requireCase "overflow after cleanup account reads" (decide ((errorState overflowAfterCleanup).map
    (fun (s : State) => s.accountReads) = some [3, 1, 1, 9]))
  requireCase "nonempty code retained" (decide (normal.map (fun (s : State) => s.writes.codeWrites) =
    some [(123, (⟨#[1, 2, 3]⟩ : ByteArray))]))
  requireCase "unrelated nonempty account" (decide (normal.map (fun (s : State) =>
    (TransactionTracker.getAccount s 6).1) = some (⟨2, 7, 123⟩ : World.Account)))
  requireCase "normal created markers" (decide (normal.map (fun (s : State) => s.createdAccounts) = some [4]))
  requireCase "overflow cleanup created" (decide ((errorState overflowAfterCleanup).map
    (fun (s : State) => s.createdAccounts) = some [4]))
  requireCase "overflow cleanup code" (decide ((errorState overflowAfterCleanup).map
    (fun (s : State) => s.writes.codeWrites) = some [(123, (⟨#[1, 2, 3]⟩ : ByteArray))]))
  requireCase "rollback parent accounts" (decide (rolledBack.map (fun (s : State) => s.parent.accounts) =
    some [(1, (⟨0, 10, World.emptyCodeHash⟩ : World.Account)),
      (2, (⟨0, 5, World.emptyCodeHash⟩ : World.Account)),
      (3, (⟨0, maxWord, World.emptyCodeHash⟩ : World.Account)),
      (5, (⟨0, 8, World.emptyCodeHash⟩ : World.Account)),
      (6, (⟨2, 7, 123⟩ : World.Account))]))
  requireCase "rollback parent code" (decide (rolledBack.map (fun (s : State) => s.parent.codes) =
    some [(123, (⟨#[1, 2, 3]⟩ : ByteArray))]))
  requireCase "rollback snapshot accounts" (decide (rolledBack.map (fun (s : State) =>
    s.snapshots.map (fun (w : TransactionState.Snapshot) => w.accountWrites)) =
    some [[(1, some (⟨0, 10, World.emptyCodeHash⟩ : World.Account)), (1, none), (5, none)], []]))
  requireCase "rollback snapshot storage" (decide (rolledBack.map (fun (s : State) =>
    s.snapshots.map (fun (w : TransactionState.Snapshot) => w.storageWrites)) =
    some [[((1, 7), 11), ((1, 7), 22), ((6, 5), 33)], [((7, 7), 77)]]))
  requireCase "rollback snapshot code" (decide (rolledBack.map (fun (s : State) =>
    s.snapshots.map (fun (w : TransactionState.Snapshot) => w.codeWrites)) =
    some [[(123, (⟨#[1, 2, 3]⟩ : ByteArray))], []]))
  requireCase "rollback snapshot clears" (decide (rolledBack.map (fun (s : State) =>
    s.snapshots.map (fun (w : TransactionState.Snapshot) => w.storageClears)) = some [[8], []]))
  requireCase "rollback snapshot transient" (decide (rolledBack.map (fun (s : State) =>
    s.snapshots.map (fun (w : TransactionState.Snapshot) => w.transientStorage)) = some [[((6, 9), 44)], []]))
  requireCase "insufficient before overflow" (decide (errorKind (moveEther fixture 1 3 11) =
    some TransferError.insufficientBalance))
  IO.println "PASS: 52 concrete transfer runtime checks"
