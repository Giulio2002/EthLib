module
import EthLib.EVM

open EthLib.EVM EthLib.EVM.TransactionState

example (s : State) : commit (snapshot s) = .ok s := by
  cases s
  rfl

example (s : State) (a : World.Address) (k : Word) :
    getStorageOriginal { s with createdAccounts := [a] } a k = 0 := by
  simp [getStorageOriginal]

example (s : State) (a : World.Address) (k : Word)
    (h : a ∉ s.createdAccounts) :
    getStorageOriginal s a k = World.getStorage s.parent a k := by
  simp [getStorageOriginal, h]

example (s : State) :
    (snapshot s).writes = s.writes ∧
    (snapshot s).snapshots = s.writes :: s.snapshots ∧
    (snapshot s).parent = s.parent ∧
    (snapshot s).accountReads = s.accountReads ∧
    (snapshot s).storageReads = s.storageReads ∧
    (snapshot s).createdAccounts = s.createdAccounts := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

example (s : State) (h : s.snapshots = []) :
    commit s = .error .noSnapshot ∧ rollback s = .error .noSnapshot := by
  simp [commit, rollback, h]

example (s : State) (saved : Snapshot) (rest : List Snapshot)
    (h : s.snapshots = saved :: rest) :
    commit s = .ok { s with snapshots := rest } ∧
    rollback s = .ok { s with writes := saved, snapshots := rest } := by
  simp [commit, rollback, h]

example (s : State) (w₁ w₂ : Snapshot) (ar : List World.Address)
    (sr : List (World.Address × Word)) (created : List World.Address) :
    let outer := snapshot s
    let inner := snapshot { outer with writes := w₁ }
    let changed := { inner with writes := w₂, accountReads := ar, storageReads := sr, createdAccounts := created }
    (commit changed).bind rollback =
      .ok { s with accountReads := ar, storageReads := sr, createdAccounts := created } := by
  cases s
  rfl
