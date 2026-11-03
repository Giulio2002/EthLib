module
import EthLib.EVM
public meta import EthLib.EVM

open EthLib.EVM EthLib.EVM.TransactionAccount

/-! Concrete Amsterdam account, code, cleanup and rollback observations. -/

private def abc : ByteArray := ⟨#[97, 98, 99]⟩
private def abcHash : Word :=
  0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45
private def parentAccount : World.Account := ⟨0, 7, World.emptyCodeHash⟩
private def fixture : State where
  parent := {
    accounts := [(1, parentAccount), (2, World.emptyAccount)]
    storage := [((1, 7), 90), ((3, 8), 80), ((4, 6), 66)]
    codes := [(World.emptyCodeHash, abc), (777, ByteArray.empty), (888, abc)] }
  writes := {
    accountWrites := [(1, some parentAccount), (1, none), (4, none)]
    storageWrites := [((1, 7), 11), ((1, 7), 22), ((3, 8), 33)]
    codeWrites := [(World.emptyCodeHash, abc), (777, abc), (777, ByteArray.empty)]
    storageClears := [5]
    transientStorage := [((3, 9), 44)] }
  accountReads := [5]
  storageReads := [(3, 8)]
  createdAccounts := [4]

example : getCode fixture World.emptyCodeHash = some ByteArray.empty := by decide
example : getCode fixture 777 = some abc := by decide
example : getCode fixture 888 = some abc := by decide
example : getCode fixture 999 = none := by decide
example : (destroyAccount fixture 1).writes.storageWrites = [((3, 8), 33)] := by decide
example : (destroyAccount fixture 1).storageReads = [(1, 7), (1, 7), (3, 8)] := by decide
example : (destroyAccount fixture 1).writes.accountWrites.lookup 1 = some none := by decide
example : (setAccountBalance fixture 1 0).writes.accountWrites.lookup 1 = some none := by decide
example : (setAccountBalance fixture 1 0).accountReads = [1, 1, 5] := by decide
example : (setAccountBalance fixture 1 0).storageReads = [(1, 7), (1, 7), (3, 8)] := by decide
example : (incrementNonce fixture 4).writes.accountWrites.lookup 4 =
    some (some ⟨1, 0, World.emptyCodeHash⟩) := by decide
example : (incrementNonce fixture 4).accountReads = [4, 4, 5] := by decide

-- Account 6 becomes empty when empty code is assigned.
-- Its storage includes duplicate keys and account 7 has only a parent entry.
private def cleanupFixture : State where
  parent := {
    accounts := [(6, ⟨0, 0, 123⟩), (7, ⟨3, 50, 456⟩)]
    storage := [((6, 10), 90), ((7, 10), 80)]
    codes := [(888, abc)] }
  writes := {
    accountWrites := [(6, some ⟨0, 0, 123⟩), (6, none)]
    storageWrites := [((6, 10), 11), ((6, 10), 22), ((6, 11), 33), ((7, 10), 44)]
    codeWrites := [(World.emptyCodeHash, abc), (777, abc), (777, ByteArray.empty)]
    storageClears := [8]
    transientStorage := [((7, 9), 44)] }
  accountReads := [5]
  storageReads := [(7, 10)]
  createdAccounts := [4]
  snapshots := [{ storageWrites := [((9, 9), 99)] }]

private def runNested : Option State :=
  let first := setAccountBalance fixture 1 0
  let second := setCode (TransactionState.snapshot (TransactionState.snapshot first)) 4 abc
  match TransactionState.rollback second with
  | .ok result => some result
  | .error _ => none

private def requireCase (label : String) (ok : Bool) : IO Unit := do
  if !ok then throw (IO.userError label)

-- The Keccak-256 answers are pinned in `Cryptography/Proofs/Hash/Keccak256.lean`.
#eval do
  requireCase "empty digest" (decide (World.codeHash ByteArray.empty = World.emptyCodeHash))
  requireCase "abc digest" (decide (World.codeHash abc = abcHash))
  requireCase "empty hash before overlays" (decide (getCode fixture World.emptyCodeHash = some ByteArray.empty))
  requireCase "overlay before parent" (decide (getCode fixture 777 = some abc))
  requireCase "parent code fallback" (decide (getCode fixture 888 = some abc))
  requireCase "missing code" (decide (getCode fixture 999 = none))
  requireCase "destroy tombstone" (decide ((destroyAccount fixture 1).writes.accountWrites.lookup 1 = some none))
  requireCase "destroy entries" (decide ((destroyAccount fixture 1).writes.storageWrites = [((3, 8), 33)]))
  requireCase "destroy reads" (decide ((destroyAccount fixture 1).storageReads = [(1, 7), (1, 7), (3, 8)]))
  requireCase "zero balance cleanup" (decide ((setAccountBalance fixture 1 0).writes.accountWrites.lookup 1 = some none))
  requireCase "cleanup account reads" (decide ((setAccountBalance fixture 1 0).accountReads = [1, 1, 5]))
  requireCase "cleanup storage reads" (decide ((setAccountBalance fixture 1 0).storageReads = [(1, 7), (1, 7), (3, 8)]))
  requireCase "absent increment" (decide ((incrementNonce fixture 4).writes.accountWrites.lookup 4 =
    some (some (⟨1, 0, World.emptyCodeHash⟩ : World.Account))))
  requireCase "nonce account reads" (decide ((incrementNonce fixture 4).accountReads = [4, 4, 5]))
  requireCase "empty code not recorded" (decide ((setCode fixture 1 ByteArray.empty).writes.codeWrites =
    [(World.emptyCodeHash, abc), (777, abc), (777, ByteArray.empty)]))
  requireCase "abc code write" (decide ((setCode fixture 4 abc).writes.codeWrites.lookup abcHash = some abc))
  requireCase "abc account" (decide ((setCode fixture 4 abc).writes.accountWrites.lookup 4 =
    some (some (⟨0, 0, abcHash⟩ : World.Account))))
  requireCase "rollback code" (decide (runNested.map (fun (s : State) => s.writes.codeWrites) =
    some [(World.emptyCodeHash, abc), (777, abc), (777, ByteArray.empty)]))
  requireCase "rollback accounts" (decide (runNested.map (fun (s : State) => s.accountReads) = some [4, 4, 1, 1, 5]))
  requireCase "rollback storage reads" (decide (runNested.map (fun (s : State) => s.storageReads) = some [(1, 7), (1, 7), (3, 8)]))
  requireCase "rollback created" (decide (runNested.map (fun (s : State) => s.createdAccounts) = some [4]))
  requireCase "rollback clears" (decide (runNested.map (fun (s : State) => s.writes.storageClears) = some [1, 5]))
  requireCase "rollback storage" (decide (runNested.map (fun (s : State) => s.writes.storageWrites) = some [((3, 8), 33)]))
  requireCase "rollback parent storage" (decide (runNested.map (fun (s : State) => s.parent.storage) =
    some [((1, 7), 90), ((3, 8), 80), ((4, 6), 66)]))
  requireCase "modify nonempty" (decide ((modifyState fixture 1 (fun account =>
    { account with balance := 8 })).writes.accountWrites.lookup 1 =
    some (some (⟨0, 8, World.emptyCodeHash⟩ : World.Account))))
  requireCase "empty parent cleanup" (decide ((setAccountBalance fixture 2 0).writes.accountWrites.lookup 2 = some none))
  requireCase "empty parent read twice" (decide ((setAccountBalance fixture 2 0).accountReads = [2, 2, 5]))
  requireCase "nonce nonempty" (decide ((incrementNonce fixture 1).writes.accountWrites.lookup 1 =
    some (some (⟨1, 7, World.emptyCodeHash⟩ : World.Account))))
  requireCase "rollback parent accounts" (decide (runNested.map (fun (s : State) => s.parent.accounts) =
    some [(1, (⟨0, 7, World.emptyCodeHash⟩ : World.Account)), (2, World.emptyAccount)]))
  requireCase "rollback parent code" (decide (runNested.map (fun (s : State) => s.parent.codes) =
    some [(World.emptyCodeHash, abc), (777, ByteArray.empty), (888, abc)]))
  requireCase "rollback transient" (decide (runNested.map (fun (s : State) => s.writes.transientStorage) =
    some [((3, 9), 44)]))
  requireCase "rollback cleanup tombstone" (decide (runNested.map (fun (s : State) =>
    s.writes.accountWrites.lookup 1) = some (some none)))
  requireCase "rollback prior tombstone" (decide (runNested.map (fun (s : State) =>
    s.writes.accountWrites.lookup 4) = some (some none)))
  requireCase "rollback account overlay" (decide (runNested.map (fun (s : State) => s.writes.accountWrites) =
    some [(1, none), (1, some World.emptyAccount),
      (1, some (⟨0, 7, World.emptyCodeHash⟩ : World.Account)), (1, none), (4, none)]))
  requireCase "rollback saved code" (decide (runNested.map (fun (s : State) =>
    s.snapshots.map (fun (w : TransactionState.Snapshot) => w.codeWrites)) =
    some [[(World.emptyCodeHash, abc), (777, abc), (777, ByteArray.empty)]]))
  requireCase "rollback saved storage" (decide (runNested.map (fun (s : State) =>
    s.snapshots.map (fun (w : TransactionState.Snapshot) => w.storageWrites)) = some [[((3, 8), 33)]]))
  requireCase "rollback saved clears" (decide (runNested.map (fun (s : State) =>
    s.snapshots.map (fun (w : TransactionState.Snapshot) => w.storageClears)) = some [[1, 5]]))
  requireCase "rollback saved transient" (decide (runNested.map (fun (s : State) =>
    s.snapshots.map (fun (w : TransactionState.Snapshot) => w.transientStorage)) = some [[((3, 9), 44)]]))
  requireCase "rollback saved accounts" (decide (runNested.map (fun (s : State) =>
    s.snapshots.map (fun (w : TransactionState.Snapshot) => w.accountWrites)) =
    some [[(1, none), (1, some World.emptyAccount),
      (1, some (⟨0, 7, World.emptyCodeHash⟩ : World.Account)), (1, none), (4, none)]]))
  requireCase "rollback created original storage" (decide (runNested.map (fun (s : State) =>
    TransactionState.getStorageOriginal s 4 6) = some 0))
  requireCase "rollback parent original storage" (decide (runNested.map (fun (s : State) =>
    TransactionState.getStorageOriginal s 1 7) = some 90))
  -- Empty code makes account 6 empty, so both its duplicate slots are cleared.
  requireCase "empty code cleanup tombstone" (decide ((setCode cleanupFixture 6 ByteArray.empty).writes.accountWrites =
    [(6, none), (6, some World.emptyAccount), (6, some (⟨0, 0, 123⟩ : World.Account)), (6, none)]))
  requireCase "empty code cleanup storage" (decide ((setCode cleanupFixture 6 ByteArray.empty).writes.storageWrites =
    [((7, 10), 44)]))
  requireCase "empty code cleanup reads" (decide ((setCode cleanupFixture 6 ByteArray.empty).storageReads =
    [(6, 10), (6, 10), (6, 11), (7, 10)]))
  requireCase "empty code cleanup marker" (decide ((setCode cleanupFixture 6 ByteArray.empty).writes.storageClears = [6, 8]))
  requireCase "empty code cleanup account reads" (decide ((setCode cleanupFixture 6 ByteArray.empty).accountReads = [6, 6, 5]))
  requireCase "empty code cleanup code history" (decide ((setCode cleanupFixture 6 ByteArray.empty).writes.codeWrites =
    [(World.emptyCodeHash, abc), (777, abc), (777, ByteArray.empty)]))
  requireCase "empty code cleanup transient" (decide ((setCode cleanupFixture 6 ByteArray.empty).writes.transientStorage =
    [((7, 9), 44)]))
  requireCase "empty code cleanup created" (decide ((setCode cleanupFixture 6 ByteArray.empty).createdAccounts = [4]))
  requireCase "empty code cleanup parent accounts" (decide ((setCode cleanupFixture 6 ByteArray.empty).parent.accounts =
    [(6, (⟨0, 0, 123⟩ : World.Account)), (7, (⟨3, 50, 456⟩ : World.Account))]))
  requireCase "empty code cleanup parent storage" (decide ((setCode cleanupFixture 6 ByteArray.empty).parent.storage =
    [((6, 10), 90), ((7, 10), 80)]))
  requireCase "empty code cleanup parent code" (decide ((setCode cleanupFixture 6 ByteArray.empty).parent.codes = [(888, abc)]))
  requireCase "empty code cleanup saved storage" (decide ((setCode cleanupFixture 6 ByteArray.empty).snapshots.map
    (fun (w : TransactionState.Snapshot) => w.storageWrites) = [[((9, 9), 99)]]))
  requireCase "empty code cleanup saved accounts" (decide ((setCode cleanupFixture 6 ByteArray.empty).snapshots.map
    (fun (w : TransactionState.Snapshot) => w.accountWrites) = [[]]))
  requireCase "empty code cleanup saved code" (decide ((setCode cleanupFixture 6 ByteArray.empty).snapshots.map
    (fun (w : TransactionState.Snapshot) => w.codeWrites) = [[]]))
  requireCase "empty code cleanup saved clears" (decide ((setCode cleanupFixture 6 ByteArray.empty).snapshots.map
    (fun (w : TransactionState.Snapshot) => w.storageClears) = [[]]))
  requireCase "empty code cleanup saved transient" (decide ((setCode cleanupFixture 6 ByteArray.empty).snapshots.map
    (fun (w : TransactionState.Snapshot) => w.transientStorage) = [[]]))
  -- A nonzero balance retains the account and every unrelated field.
  requireCase "balance retained account" (decide ((setAccountBalance cleanupFixture 6 55).writes.accountWrites =
    [(6, some (⟨0, 55, 123⟩ : World.Account)), (6, some (⟨0, 0, 123⟩ : World.Account)), (6, none)]))
  requireCase "balance retained storage" (decide ((setAccountBalance cleanupFixture 6 55).writes.storageWrites =
    [((6, 10), 11), ((6, 10), 22), ((6, 11), 33), ((7, 10), 44)]))
  requireCase "balance retained storage reads" (decide ((setAccountBalance cleanupFixture 6 55).storageReads = [(7, 10)]))
  requireCase "balance retained account reads" (decide ((setAccountBalance cleanupFixture 6 55).accountReads = [6, 6, 5]))
  requireCase "balance retained code" (decide ((setAccountBalance cleanupFixture 6 55).writes.codeWrites =
    [(World.emptyCodeHash, abc), (777, abc), (777, ByteArray.empty)]))
  requireCase "balance retained clears" (decide ((setAccountBalance cleanupFixture 6 55).writes.storageClears = [8]))
  requireCase "balance retained transient" (decide ((setAccountBalance cleanupFixture 6 55).writes.transientStorage = [((7, 9), 44)]))
  requireCase "balance retained created" (decide ((setAccountBalance cleanupFixture 6 55).createdAccounts = [4]))
  requireCase "balance retained parent accounts" (decide ((setAccountBalance cleanupFixture 6 55).parent.accounts =
    [(6, (⟨0, 0, 123⟩ : World.Account)), (7, (⟨3, 50, 456⟩ : World.Account))]))
  requireCase "balance retained parent storage" (decide ((setAccountBalance cleanupFixture 6 55).parent.storage =
    [((6, 10), 90), ((7, 10), 80)]))
  requireCase "balance retained parent code" (decide ((setAccountBalance cleanupFixture 6 55).parent.codes = [(888, abc)]))
  requireCase "balance retained snapshot storage" (decide ((setAccountBalance cleanupFixture 6 55).snapshots.map
    (fun (w : TransactionState.Snapshot) => w.storageWrites) = [[((9, 9), 99)]]))
  requireCase "balance retained snapshot accounts" (decide ((setAccountBalance cleanupFixture 6 55).snapshots.map
    (fun (w : TransactionState.Snapshot) => w.accountWrites) = [[]]))
  requireCase "balance retained snapshot code" (decide ((setAccountBalance cleanupFixture 6 55).snapshots.map
    (fun (w : TransactionState.Snapshot) => w.codeWrites) = [[]]))
  requireCase "balance retained snapshot clears" (decide ((setAccountBalance cleanupFixture 6 55).snapshots.map
    (fun (w : TransactionState.Snapshot) => w.storageClears) = [[]]))
  requireCase "balance retained snapshot transient" (decide ((setAccountBalance cleanupFixture 6 55).snapshots.map
    (fun (w : TransactionState.Snapshot) => w.transientStorage) = [[]]))
  -- Address 9 is absent in both stores; address 7 is present only in the parent.
  requireCase "absent overlay" (decide (cleanupFixture.writes.accountWrites.lookup 9 = none))
  requireCase "absent parent" (decide (cleanupFixture.parent.accounts.lookup 9 = none))
  requireCase "parent only overlay absent" (decide (cleanupFixture.writes.accountWrites.lookup 7 = none))
  requireCase "parent only account present" (decide (cleanupFixture.parent.accounts.lookup 7 =
    some (⟨3, 50, 456⟩ : World.Account)))
  requireCase "genuinely absent nonce" (decide ((incrementNonce cleanupFixture 9).writes.accountWrites.lookup 9 =
    some (some (⟨1, 0, World.emptyCodeHash⟩ : World.Account))))
  requireCase "genuinely absent reads" (decide ((incrementNonce cleanupFixture 9).accountReads = [9, 9, 5]))
  requireCase "parent only balance" (decide ((setAccountBalance cleanupFixture 7 60).writes.accountWrites.lookup 7 =
    some (some (⟨3, 60, 456⟩ : World.Account))))
  requireCase "parent only reads" (decide ((setAccountBalance cleanupFixture 7 60).accountReads = [7, 7, 5]))
  IO.println "PASS: 81 concrete account and code tracker runtime checks"
