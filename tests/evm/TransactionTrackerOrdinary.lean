module
import EthLib.EVM

open EthLib.EVM EthLib.EVM.TransactionTracker

example (s : State) (a : World.Address) :
    (getAccountOptional s a).2.accountReads = a :: s.accountReads := rfl

example (s : State) (a : World.Address) :
    (getAccount s a).1 = (getAccountOptional s a).1.getD World.emptyAccount := rfl

example (s : State) (a : World.Address) (k : Word) :
    (getStorage s a k).2.storageReads = (a, k) :: s.storageReads := rfl

example (s : State) (a : World.Address) (k : Word) :
    getTransientStorage s a k = (s.writes.transientStorage.lookup (a, k)).getD 0 := rfl

example (s : State) (a : World.Address) :
    (setAccount s a none).writes.accountWrites.lookup a = some none := by
  simp [setAccount]

example (s : State) (a : World.Address) :
    a ∈ (markAccountCreated s a).createdAccounts := by
  simp [markAccountCreated]

example (s : State) (a : World.Address) (k : Word) :
    (setTransientStorage s a k 0).writes.transientStorage =
      s.writes.transientStorage.filter (fun entry => entry.1 != (a, k)) := by
  simp [setTransientStorage]

example (s : State) (a : World.Address) :
    a ∈ (destroyStorage s a).writes.storageClears := by
  simp [destroyStorage]

example (s : State) (a : World.Address) (k v : Word)
    (h : (getAccountOptional s a).1 = none) :
    setStorage s a k v = .error (.missingAccount, (getAccountOptional s a).2) := by
  simp [setStorage, h]

example (s : State) (a : World.Address) (k v : Word)
    (h : s.writes.storageWrites.lookup (a, k) = some v) :
    (getStorage s a k).1 = v := by
  simp [getStorage, h]

example (s : State) (a : World.Address) (k v : Word) (account : World.Account)
    (h : (getAccountOptional s a).1 = some account) :
    setStorage s a k v = .ok { (getAccountOptional s a).2 with writes :=
      { (getAccountOptional s a).2.writes with
        storageWrites := ((a, k), v) :: (getAccountOptional s a).2.writes.storageWrites } } := by
  simp [setStorage, h]
