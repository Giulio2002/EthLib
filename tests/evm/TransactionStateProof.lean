module
import EthLib.EVM.Proofs

open EthLib.EVM EthLib.EVM.TransactionState

example (s : State) : rollback (snapshot s) = .ok s := rollback_snapshot s

example (s t : State) : rollback s = .ok t ↔
    ∃ top rest, s.snapshots = top :: rest ∧
      t = { s with writes := top, snapshots := rest } := rollback_ok_iff s t

example (s : State) (w₁ w₂ : Snapshot) (ar : List World.Address)
    (sr : List (World.Address × Word)) (created : List World.Address) :
    let outer := snapshot s
    let inner := snapshot { outer with writes := w₁ }
    let changed := { inner with writes := w₂, accountReads := ar, storageReads := sr, createdAccounts := created }
    (commit changed).bind rollback =
      .ok { s with accountReads := ar, storageReads := sr, createdAccounts := created } :=
  nested_commit_rollback s w₁ w₂ ar sr created

open EthLib.EVM.TransactionState.Reference

example (s : State) (a : World.Address) (k : Word) :
    Original (observe s) a k (getStorageOriginal s a k) := original_refines s a k

example (s : State) : Save (observe s) (observe (snapshot s)) := snapshot_refines s

example (s t : State) (h : commit s = .ok t) : Commit (observe s) (observe t) :=
  commit_refines s t h

example (s t : State) (h : rollback s = .ok t) : Rollback (observe s) (observe t) :=
  rollback_refines s t h

example (s t : State) (h : Commit (observe s) (observe t)) :
    ∃ u, commit s = .ok u ∧ observe u = observe t := commit_complete s t h

example (s t : State) (h : Rollback (observe s) (observe t)) :
    ∃ u, rollback s = .ok u ∧ observe u = observe t := rollback_complete s t h

example (s : State) : commit s = .error .noSnapshot ↔ (observe s).stack = [] :=
  EthLib.EVM.TransactionState.Reference.commit_error_iff s

example (s : State) : rollback s = .error .noSnapshot ↔ (observe s).stack = [] :=
  EthLib.EVM.TransactionState.Reference.rollback_error_iff s

example (s : State) : (∃ t, commit s = .ok t) ↔ (observe s).stack ≠ [] :=
  commit_success_iff s

example (s : State) : (∃ t, rollback s = .ok t) ↔ (observe s).stack ≠ [] :=
  rollback_success_iff s

example (initial changed middle result : View) (inner : Writes)
    (hs : changed.stack = inner :: initial.writes :: initial.stack)
    (hc : Commit changed middle) (hr : Rollback middle result) :
    result.writes = initial.writes ∧ result.stack = initial.stack ∧ Retained changed result :=
  nested_relations initial changed middle result inner hs hc hr

example (before after : View) (h : Rollback before after) :
    ∃ saved rest, before.stack = saved :: rest ∧
      after.writes.accounts = saved.accounts ∧ after.writes.storage = saved.storage ∧
      after.writes.code = saved.code ∧ after.writes.clears = saved.clears ∧
      after.writes.transient = saved.transient ∧
      before.parentAccounts = after.parentAccounts ∧
      before.parentStorage = after.parentStorage ∧ before.parentCode = after.parentCode ∧
      before.accountReads = after.accountReads ∧ before.storageReads = after.storageReads ∧
      before.created = after.created ∧ after.stack = rest := rollback_fields before after h

example (s : State) (a : World.Address) (k value : Word)
    (h : Original (observe s) a k value) : value = getStorageOriginal s a k :=
  original_complete s a k value h

example (s t : State) (h : Save (observe s) (observe t)) :
    observe (snapshot s) = observe t := snapshot_complete s t h
