module
import EthLib.EVM
public meta import EthLib.EVM

open EthLib.EVM EthLib.EVM.TransactionTracker

/-! Concrete tracker observations on duplicate entries and a nested rollback. -/

private def parentAccount : World.Account := ⟨1, 10, 100⟩
private def overlayAccount : World.Account := ⟨2, 20, 200⟩
private def otherAccount : World.Account := ⟨3, 30, 300⟩

private def fixture : State where
  parent := {
    accounts := [(1, parentAccount), (2, parentAccount), (3, otherAccount)]
    storage := [((1, 10), 9), ((1, 12), 50), ((3, 13), 77)]
    codes := [(55, ByteArray.empty)] }
  writes := {
    accountWrites := [(1, some overlayAccount), (2, none), (1, some parentAccount)]
    storageWrites := [((1, 10), 111), ((1, 10), 222), ((1, 11), 333),
      ((2, 10), 444), ((2, 11), 555)]
    codeWrites := [(5, ByteArray.empty)]
    storageClears := [1]
    transientStorage := [((1, 10), 11), ((1, 10), 22), ((1, 11), 33), ((2, 10), 44)] }
  accountReads := [4]
  storageReads := [(3, 13)]
  createdAccounts := [3]

-- Overlay presence and deletion both shadow the parent; absent accounts default.
example : (getAccountOptional fixture 1).1 = some ⟨2, 20, 200⟩ := by decide
example : (getAccountOptional fixture 2).1 = none := by decide
example : (getAccount fixture 2).1 = World.emptyAccount := by decide
example : (getAccountOptional fixture 3).1 = some ⟨3, 30, 300⟩ := by decide
example : (getAccount fixture 5).1 = World.emptyAccount := by decide
example : (getAccountOptional fixture 3).2.accountReads = [3, 4] := by decide

-- A write wins over a clear; an unfilled cleared slot is zero; other addresses fall back.
example : (getStorage fixture 1 10).1 = 111 := by decide
example : (getStorage fixture 1 12).1 = 0 := by decide
example : (getStorage fixture 3 13).1 = 77 := by decide
example : (getStorage fixture 3 14).1 = 0 := by decide
example : (getStorage fixture 1 10).2.storageReads = [(1, 10), (3, 13)] := by decide

-- Zero removes every duplicate at one slot and keeps the other slots and addresses.
example : (setTransientStorage fixture 1 10 0).writes.transientStorage =
    [((1, 11), 33), ((2, 10), 44)] := by decide
example : (setTransientStorage fixture 1 10 66).writes.transientStorage =
    [((1, 10), 66), ((1, 11), 33), ((2, 10), 44)] := by decide
example : getTransientStorage (setTransientStorage fixture 1 10 0) 1 10 = 0 := by decide
example : getTransientStorage (setTransientStorage fixture 1 10 66) 1 10 = 66 := by decide
example : getTransientStorage (setTransientStorage fixture 1 10 0) 2 10 = 44 := by decide

-- Clearing records every removed entry, including both occurrences of one key.
example : (destroyStorage fixture 1).writes.storageWrites =
    [((2, 10), 444), ((2, 11), 555)] := by decide
example : (destroyStorage fixture 1).storageReads =
    [(1, 10), (1, 10), (1, 11), (3, 13)] := by decide
example : (destroyStorage fixture 1).writes.storageClears = [1, 1] := by decide
example : (destroyStorage fixture 1).accountReads = [4] := by decide
example : (destroyStorage fixture 1).createdAccounts = [3] := by decide
example : (destroyStorage fixture 1).parent.storage =
    [((1, 10), 9), ((1, 12), 50), ((3, 13), 77)] := by decide

/-- Execute two writes around nested snapshots and roll back the inner one. -/
private def runNested : Option State :=
  match setStorage fixture 1 10 901 with
  | .error _ => none
  | .ok first =>
    match setStorage (TransactionState.snapshot (TransactionState.snapshot first)) 3 13 902 with
    | .error _ => none
    | .ok second =>
      match TransactionState.rollback second with
      | .error _ => none
      | .ok result => some result

-- The first write survives, the second disappears, and both account reads survive.
example : runNested.map (fun s => s.writes.storageWrites) =
    some [((1, 10), 901), ((1, 10), 111), ((1, 10), 222), ((1, 11), 333),
      ((2, 10), 444), ((2, 11), 555)] := by decide
example : runNested.map (fun s => s.accountReads) = some [3, 1, 4] := by decide
example : runNested.map (fun s => s.storageReads) = some [(3, 13)] := by decide
example : runNested.map (fun s => s.createdAccounts) = some [3] := by decide
example : runNested.map (fun s => s.writes.accountWrites) =
    some [(1, some ⟨2, 20, 200⟩), (2, none), (1, some ⟨1, 10, 100⟩)] := by decide
example : runNested.map (fun s => s.writes.codeWrites) = some [(5, ByteArray.empty)] := by decide
example : runNested.map (fun s => s.writes.storageClears) = some [1] := by decide
example : runNested.map (fun s => s.writes.transientStorage) =
    some [((1, 10), 11), ((1, 10), 22), ((1, 11), 33), ((2, 10), 44)] := by decide
example : runNested.map (fun s => s.snapshots.map (fun w => w.storageWrites)) =
    some [[((1, 10), 901), ((1, 10), 111), ((1, 10), 222), ((1, 11), 333),
      ((2, 10), 444), ((2, 11), 555)]] := by decide
example : runNested.map (fun s => s.parent.accounts) =
    some [(1, ⟨1, 10, 100⟩), (2, ⟨1, 10, 100⟩), (3, ⟨3, 30, 300⟩)] := by decide
example : runNested.map (fun s => s.parent.storage) =
    some [((1, 10), 9), ((1, 12), 50), ((3, 13), 77)] := by decide
example : runNested.map (fun s => s.parent.codes) = some [(55, ByteArray.empty)] := by decide
example : runNested.map (fun s => TransactionState.getStorageOriginal s 3 13) = some 0 := by decide

private def requireCase (label : String) (ok : Bool) : IO Unit := do
  if !ok then throw (IO.userError label)

-- The remaining saved fields are also restored in the outer snapshot.
example : runNested.map (fun s => s.snapshots.map (fun w => w.accountWrites)) =
    some [[(1, some ⟨2, 20, 200⟩), (2, none), (1, some ⟨1, 10, 100⟩)]] := by decide
example : runNested.map (fun s => s.snapshots.map (fun w => w.codeWrites)) =
    some [[(5, ByteArray.empty)]] := by decide
example : runNested.map (fun s => s.snapshots.map (fun w => w.storageClears)) =
    some [[1]] := by decide
example : runNested.map (fun s => s.snapshots.map (fun w => w.transientStorage)) =
    some [[((1, 10), 11), ((1, 10), 22), ((1, 11), 33), ((2, 10), 44)]] := by decide
example : runNested.map (fun s => TransactionState.getStorageOriginal s 1 10) = some 9 := by decide

-- Run the concrete checks through Lean's evaluator as well as the kernel.
#eval do
  requireCase "account overlay" (decide ((getAccountOptional fixture 1).1 = some (⟨2, 20, 200⟩ : World.Account)))
  requireCase "account deletion" (decide ((getAccountOptional fixture 2).1 = none))
  requireCase "account default" (decide ((getAccount fixture 5).1 = World.emptyAccount))
  requireCase "parent account" (decide ((getAccountOptional fixture 3).1 = some (⟨3, 30, 300⟩ : World.Account)))
  requireCase "account read" (decide ((getAccountOptional fixture 3).2.accountReads = [3, 4]))
  requireCase "write before clear" (decide ((getStorage fixture 1 10).1 = 111))
  requireCase "clear before parent" (decide ((getStorage fixture 1 12).1 = 0))
  requireCase "storage parent" (decide ((getStorage fixture 3 13).1 = 77))
  requireCase "storage default" (decide ((getStorage fixture 3 14).1 = 0))
  requireCase "storage read" (decide ((getStorage fixture 1 10).2.storageReads = [(1, 10), (3, 13)]))
  requireCase "transient duplicate deletion" (decide ((setTransientStorage fixture 1 10 0).writes.transientStorage =
    [((1, 11), 33), ((2, 10), 44)]))
  requireCase "transient replacement" (decide ((setTransientStorage fixture 1 10 66).writes.transientStorage =
    [((1, 10), 66), ((1, 11), 33), ((2, 10), 44)]))
  requireCase "cleared storage writes" (decide ((destroyStorage fixture 1).writes.storageWrites =
    [((2, 10), 444), ((2, 11), 555)]))
  requireCase "cleared storage reads" (decide ((destroyStorage fixture 1).storageReads =
    [(1, 10), (1, 10), (1, 11), (3, 13)]))
  requireCase "clear marker" (decide ((destroyStorage fixture 1).writes.storageClears = [1, 1]))
  requireCase "nested writes" (decide (runNested.map (fun (s : State) => s.writes.storageWrites) =
    some [((1, 10), 901), ((1, 10), 111), ((1, 10), 222), ((1, 11), 333),
      ((2, 10), 444), ((2, 11), 555)]))
  requireCase "nested account reads" (decide (runNested.map (fun (s : State) => s.accountReads) = some [3, 1, 4]))
  requireCase "nested storage reads" (decide (runNested.map (fun (s : State) => s.storageReads) = some [(3, 13)]))
  requireCase "nested created" (decide (runNested.map (fun (s : State) => s.createdAccounts) = some [3]))
  requireCase "nested account writes" (decide (runNested.map (fun (s : State) => s.writes.accountWrites) =
    some [(1, some (⟨2, 20, 200⟩ : World.Account)), (2, none), (1, some (⟨1, 10, 100⟩ : World.Account))]))
  requireCase "nested code writes" (decide (runNested.map (fun (s : State) => s.writes.codeWrites) = some [(5, ByteArray.empty)]))
  requireCase "nested clears" (decide (runNested.map (fun (s : State) => s.writes.storageClears) = some [1]))
  requireCase "nested transient" (decide (runNested.map (fun (s : State) => s.writes.transientStorage) =
    some [((1, 10), 11), ((1, 10), 22), ((1, 11), 33), ((2, 10), 44)]))
  requireCase "nested snapshot" (decide (runNested.map (fun (s : State) => s.snapshots.map (fun (w : TransactionState.Snapshot) => w.storageWrites)) =
    some [[((1, 10), 901), ((1, 10), 111), ((1, 10), 222), ((1, 11), 333),
      ((2, 10), 444), ((2, 11), 555)]]))
  requireCase "nested parent accounts" (decide (runNested.map (fun (s : State) => s.parent.accounts) =
    some [(1, (⟨1, 10, 100⟩ : World.Account)), (2, (⟨1, 10, 100⟩ : World.Account)), (3, (⟨3, 30, 300⟩ : World.Account))]))
  requireCase "nested parent storage" (decide (runNested.map (fun (s : State) => s.parent.storage) =
    some [((1, 10), 9), ((1, 12), 50), ((3, 13), 77)]))
  requireCase "nested parent code" (decide (runNested.map (fun (s : State) => s.parent.codes) = some [(55, ByteArray.empty)]))
  requireCase "created original storage" (decide (runNested.map (fun (s : State) => TransactionState.getStorageOriginal s 3 13) = some 0))
  requireCase "deleted account default" (decide ((getAccount fixture 2).1 = World.emptyAccount))
  requireCase "clear account reads" (decide ((destroyStorage fixture 1).accountReads = [4]))
  requireCase "clear created set" (decide ((destroyStorage fixture 1).createdAccounts = [3]))
  requireCase "clear parent storage" (decide ((destroyStorage fixture 1).parent.storage =
    [((1, 10), 9), ((1, 12), 50), ((3, 13), 77)]))
  requireCase "nested snapshot accounts" (decide (runNested.map (fun (s : State) =>
    s.snapshots.map (fun (w : TransactionState.Snapshot) => w.accountWrites)) =
    some [[(1, some (⟨2, 20, 200⟩ : World.Account)), (2, none),
      (1, some (⟨1, 10, 100⟩ : World.Account))]]))
  requireCase "nested snapshot code" (decide (runNested.map (fun (s : State) =>
    s.snapshots.map (fun (w : TransactionState.Snapshot) => w.codeWrites)) = some [[(5, ByteArray.empty)]]))
  requireCase "nested snapshot clears" (decide (runNested.map (fun (s : State) =>
    s.snapshots.map (fun (w : TransactionState.Snapshot) => w.storageClears)) = some [[1]]))
  requireCase "nested snapshot transient" (decide (runNested.map (fun (s : State) =>
    s.snapshots.map (fun (w : TransactionState.Snapshot) => w.transientStorage)) =
    some [[((1, 10), 11), ((1, 10), 22), ((1, 11), 33), ((2, 10), 44)]]))
  requireCase "parent original storage" (decide (runNested.map (fun (s : State) =>
    TransactionState.getStorageOriginal s 1 10) = some 9))
  IO.println "PASS: 37 concrete transaction tracker runtime checks"
