module

public import EthLib.EVM.TransactionState

/-! Pointwise contracts for transaction-original storage and nested snapshots. -/

@[expose] public section
namespace EthLib.EVM.TransactionState

/-- Original storage follows the transaction-start world unless the account was created. -/
theorem getStorageOriginal_spec (s : State) (a : World.Address) (k : Word) :
    getStorageOriginal s a k =
      if a ∈ s.createdAccounts then 0 else World.getStorage s.parent a k := by
  simp [getStorageOriginal]

/-- Saving preserves every current field and adds exactly one snapshot. -/
theorem snapshot_spec (s : State) :
    (snapshot s).parent = s.parent ∧ (snapshot s).writes = s.writes ∧
    (snapshot s).accountReads = s.accountReads ∧
    (snapshot s).storageReads = s.storageReads ∧
    (snapshot s).createdAccounts = s.createdAccounts ∧
    (snapshot s).snapshots = s.writes :: s.snapshots := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Commit fails exactly when the snapshot stack is empty. -/
theorem commit_error_iff (s : State) :
    commit s = .error .noSnapshot ↔ s.snapshots = [] := by
  cases h : s.snapshots <;> simp [commit, h]

/-- Rollback fails exactly when the snapshot stack is empty. -/
theorem rollback_error_iff (s : State) :
    rollback s = .error .noSnapshot ↔ s.snapshots = [] := by
  cases h : s.snapshots <;> simp [rollback, h]

/-- Commit succeeds exactly with the top snapshot removed and all other fields retained. -/
theorem commit_ok_iff (s t : State) :
    commit s = .ok t ↔ ∃ top rest, s.snapshots = top :: rest ∧
      t = { s with snapshots := rest } := by
  cases h : s.snapshots with
  | nil => simp [commit, h]
  | cons top rest =>
    simp only [commit, h, Except.ok.injEq, List.cons.injEq]
    constructor
    · intro eq
      exact ⟨top, rest, ⟨rfl, rfl⟩, eq.symm⟩
    · rintro ⟨_, _, ⟨rfl, rfl⟩, eq⟩
      exact eq.symm

/-- Rollback restores all saved writes and retains all non-revertible fields. -/
theorem rollback_ok_iff (s t : State) :
    rollback s = .ok t ↔ ∃ top rest, s.snapshots = top :: rest ∧
      t = { s with writes := top, snapshots := rest } := by
  cases h : s.snapshots with
  | nil => simp [rollback, h]
  | cons top rest =>
    simp only [rollback, h, Except.ok.injEq, List.cons.injEq]
    constructor
    · intro eq
      exact ⟨top, rest, ⟨rfl, rfl⟩, eq.symm⟩
    · rintro ⟨_, _, ⟨rfl, rfl⟩, eq⟩
      exact eq.symm

/-- Successful rollback restores each revertible field and preserves the rest. -/
theorem rollback_effects (s t : State) (h : rollback s = .ok t) :
    ∃ saved rest, s.snapshots = saved :: rest ∧
      t.writes.accountWrites = saved.accountWrites ∧
      t.writes.storageWrites = saved.storageWrites ∧
      t.writes.codeWrites = saved.codeWrites ∧
      t.writes.storageClears = saved.storageClears ∧
      t.writes.transientStorage = saved.transientStorage ∧
      t.parent = s.parent ∧ t.accountReads = s.accountReads ∧
      t.storageReads = s.storageReads ∧ t.createdAccounts = s.createdAccounts ∧
      t.snapshots = rest := by
  obtain ⟨saved, rest, hs, rfl⟩ := (rollback_ok_iff s t).mp h
  exact ⟨saved, rest, hs, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A saved state can be committed immediately. -/
theorem commit_snapshot (s : State) : commit (snapshot s) = .ok s := by
  cases s
  rfl

/-- A saved state can be rolled back immediately. -/
theorem rollback_snapshot (s : State) : rollback (snapshot s) = .ok s := by
  cases s
  rfl

/-- A nested commit keeps inner writes; the outer rollback restores its saved writes.

Reads and created accounts accumulated in the inner scope survive both steps.
-/
theorem nested_commit_rollback (s : State) (w₁ w₂ : Snapshot)
    (ar : List World.Address) (sr : List (World.Address × Word))
    (created : List World.Address) :
    let outer := snapshot s
    let inner := snapshot { outer with writes := w₁ }
    let changed := { inner with writes := w₂, accountReads := ar, storageReads := sr, createdAccounts := created }
    (commit changed).bind rollback =
      .ok { s with accountReads := ar, storageReads := sr, createdAccounts := created } := by
  cases s
  rfl

end EthLib.EVM.TransactionState
