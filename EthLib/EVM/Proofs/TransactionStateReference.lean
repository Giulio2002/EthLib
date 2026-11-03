module

public import EthLib.EVM.Proofs.TransactionState

/-!
# Observable transaction-state model

The reference state uses total functions for finite-map and set observations.
Its transition relations describe the pinned Amsterdam `state_tracker.py`
functions `get_storage_original`, `copy_tx_state`, and `restore_tx_state`.
The stack and commit relation describe nested use of copy and restore.
The observation map accepts every executable state, including duplicate entries.
-/

@[expose] public section
namespace EthLib.EVM.TransactionState.Reference

abbrev Address := World.Address
abbrev Slot := Address × Word

/-- Observations of all five revertible fields. -/
structure Writes where
  accounts : Address → Option (Option World.Account)
  storage : Slot → Option Word
  code : Word → Option ByteArray
  clears : Address → Prop
  transient : Slot → Option Word

/-- Observations of the parent, current transaction and saved scopes. -/
structure View where
  parentAccounts : Address → Option World.Account
  parentStorage : Slot → Word
  parentCode : Word → Option ByteArray
  writes : Writes
  accountReads : Address → Prop
  storageReads : Slot → Prop
  created : Address → Prop
  stack : List Writes

/-- Interpret association lists by their first entry and lists as sets. -/
def observeWrites (w : Snapshot) : Writes where
  accounts := fun key => w.accountWrites.lookup key
  storage := fun key => w.storageWrites.lookup key
  code := fun key => w.codeWrites.lookup key
  clears := (· ∈ w.storageClears)
  transient := fun key => w.transientStorage.lookup key

/-- Observe a concrete transaction without assuming uniqueness or chain validity. -/
def observe (s : State) : View where
  parentAccounts := fun key => s.parent.accounts.lookup key
  parentStorage := fun key => (s.parent.storage.lookup key).getD 0
  parentCode := fun key => s.parent.codes.lookup key
  writes := observeWrites s.writes
  accountReads := (· ∈ s.accountReads)
  storageReads := (· ∈ s.storageReads)
  created := (· ∈ s.createdAccounts)
  stack := s.snapshots.map observeWrites

/-- Parent observations and non-revertible transaction observations agree. -/
def Retained (x y : View) : Prop :=
  x.parentAccounts = y.parentAccounts ∧ x.parentStorage = y.parentStorage ∧
  x.parentCode = y.parentCode ∧ x.accountReads = y.accountReads ∧
  x.storageReads = y.storageReads ∧ x.created = y.created

/-- The original slot is zero for a created account and otherwise comes from the parent. -/
def Original (s : View) (a : Address) (k value : Word) : Prop :=
  (s.created a → value = 0) ∧ (¬ s.created a → value = s.parentStorage (a, k))

/-- Saving adds the current write observations to the stack. -/
def Save (before after : View) : Prop :=
  Retained before after ∧ after.writes = before.writes ∧
  after.stack = before.writes :: before.stack

/-- Commit retains current writes and drops the most recent saved scope. -/
def Commit (before after : View) : Prop :=
  ∃ saved rest, before.stack = saved :: rest ∧ Retained before after ∧
    after.writes = before.writes ∧ after.stack = rest

/-- Rollback restores the saved writes and retains non-revertible observations. -/
def Rollback (before after : View) : Prop :=
  ∃ saved rest, before.stack = saved :: rest ∧ Retained before after ∧
    after.writes = saved ∧ after.stack = rest

/-- Original storage agrees with the independent selection rule. -/
theorem original_refines (s : State) (a : Address) (k : Word) :
    Original (observe s) a k (getStorageOriginal s a k) := by
  by_cases h : a ∈ s.createdAccounts <;> simp [Original, observe, getStorageOriginal, World.getStorage, h]

/-- The selection relation determines the result for every input. -/
theorem original_complete (s : State) (a : Address) (k value : Word)
    (h : Original (observe s) a k value) : value = getStorageOriginal s a k := by
  by_cases created : a ∈ s.createdAccounts
  · exact (h.1 created).trans (((original_refines s a k).1 created).symm)
  · exact (h.2 created).trans (((original_refines s a k).2 created).symm)

/-- Every snapshot refines the reference save relation. -/
theorem snapshot_refines (s : State) : Save (observe s) (observe (snapshot s)) := by
  simp [Save, Retained, observe, snapshot]

/-- Commit succeeds with exactly the reference observations of its input. -/
theorem commit_refines (s t : State) (h : commit s = .ok t) :
    Commit (observe s) (observe t) := by
  obtain ⟨saved, rest, hs, rfl⟩ := (commit_ok_iff s t).mp h
  refine ⟨observeWrites saved, rest.map observeWrites, ?_, ?_, rfl, rfl⟩
  · simp [observe, hs]
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Rollback succeeds with exactly the reference observations of its input. -/
theorem rollback_refines (s t : State) (h : rollback s = .ok t) :
    Rollback (observe s) (observe t) := by
  obtain ⟨saved, rest, hs, rfl⟩ := (rollback_ok_iff s t).mp h
  refine ⟨observeWrites saved, rest.map observeWrites, ?_, ?_, rfl, rfl⟩
  · simp [observe, hs]
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The rollback relation specifies every saved and retained observation. -/
theorem rollback_fields (before after : View) (h : Rollback before after) :
    ∃ saved rest, before.stack = saved :: rest ∧
      after.writes.accounts = saved.accounts ∧
      after.writes.storage = saved.storage ∧
      after.writes.code = saved.code ∧
      after.writes.clears = saved.clears ∧
      after.writes.transient = saved.transient ∧
      before.parentAccounts = after.parentAccounts ∧
      before.parentStorage = after.parentStorage ∧
      before.parentCode = after.parentCode ∧
      before.accountReads = after.accountReads ∧
      before.storageReads = after.storageReads ∧
      before.created = after.created ∧ after.stack = rest := by
  rcases h with ⟨saved, rest, hs, retained, hw, hr⟩
  rcases retained with ⟨a, b, c, d, e, f⟩
  cases hw
  exact ⟨after.writes, rest, hs, rfl, rfl, rfl, rfl, rfl, a, b, c, d, e, f, hr⟩

/-- A view is determined by its retained, write and stack observations. -/
theorem view_ext (x y : View) (h : Retained x y)
    (hw : x.writes = y.writes) (hs : x.stack = y.stack) : x = y := by
  cases x
  cases y
  simp_all [Retained]

/-- Every reference save outcome has the observation of the concrete snapshot. -/
theorem snapshot_complete (s t : State) (h : Save (observe s) (observe t)) :
    observe (snapshot s) = observe t := by
  rcases h with ⟨hret, hw, hs⟩
  apply view_ext
  · simpa [Retained, observe, snapshot] using hret
  · simpa [observe, snapshot] using hw.symm
  · simpa [observe, snapshot] using hs.symm

/-- Every reference commit outcome is represented by the concrete commit outcome. -/
theorem commit_complete (s t : State) (h : Commit (observe s) (observe t)) :
    ∃ u, commit s = .ok u ∧ observe u = observe t := by
  rcases h with ⟨saved, rest, hstack, hret, hw, hr⟩
  cases hs : s.snapshots with
  | nil => simp [observe, hs] at hstack
  | cons top tail =>
    simp only [observe, hs, List.map_cons, List.cons.injEq] at hstack
    rcases hstack with ⟨rfl, rfl⟩
    refine ⟨{ s with snapshots := tail }, ?_, ?_⟩
    · simp [commit, hs]
    · apply view_ext
      · simpa [Retained, observe] using hret
      · simpa [observe] using hw.symm
      · simpa [observe] using hr.symm

/-- Every reference rollback outcome is represented by the concrete rollback outcome. -/
theorem rollback_complete (s t : State) (h : Rollback (observe s) (observe t)) :
    ∃ u, rollback s = .ok u ∧ observe u = observe t := by
  rcases h with ⟨saved, rest, hstack, hret, hw, hr⟩
  cases hs : s.snapshots with
  | nil => simp [observe, hs] at hstack
  | cons top tail =>
    simp only [observe, hs, List.map_cons, List.cons.injEq] at hstack
    rcases hstack with ⟨rfl, rfl⟩
    refine ⟨{ s with writes := top, snapshots := tail }, ?_, ?_⟩
    · simp [rollback, hs]
    · apply view_ext
      · simpa [Retained, observe] using hret
      · simpa [observe] using hw.symm
      · simpa [observe] using hr.symm

/-- Commit fails exactly when the observed stack is empty. -/
theorem commit_error_iff (s : State) :
    commit s = .error .noSnapshot ↔ (observe s).stack = [] := by
  simpa [observe] using TransactionState.commit_error_iff s

/-- Rollback fails exactly when the observed stack is empty. -/
theorem rollback_error_iff (s : State) :
    rollback s = .error .noSnapshot ↔ (observe s).stack = [] := by
  simpa [observe] using TransactionState.rollback_error_iff s

/-- A nonempty reference stack is exactly the condition for commit success. -/
theorem commit_success_iff (s : State) :
    (∃ t, commit s = .ok t) ↔ (observe s).stack ≠ [] := by
  cases h : s.snapshots <;> simp [commit, observe, h]

/-- A nonempty reference stack is exactly the condition for rollback success. -/
theorem rollback_success_iff (s : State) :
    (∃ t, rollback s = .ok t) ↔ (observe s).stack ≠ [] := by
  cases h : s.snapshots <;> simp [rollback, observe, h]

/-- Reference composition permits arbitrary intervening observations.

The inner commit keeps its current writes.
The following rollback restores the outer saved writes and retains the latest reads.
-/
theorem nested_relations (initial changed middle result : View) (inner : Writes)
    (hstack : changed.stack = inner :: initial.writes :: initial.stack)
    (hc : Commit changed middle) (hr : Rollback middle result) :
    result.writes = initial.writes ∧ result.stack = initial.stack ∧
    Retained changed result := by
  obtain ⟨_, _, hcstack, hcRetained, _, hcrest⟩ := hc
  rw [hstack] at hcstack
  have hrest : middle.stack = initial.writes :: initial.stack := by
    cases hcstack
    exact hcrest
  obtain ⟨_, _, hrstack, hrRetained, hrwrites, hrrest⟩ := hr
  rw [hrest] at hrstack
  cases hrstack
  refine ⟨hrwrites, hrrest, ?_⟩
  rcases hcRetained with ⟨a, b, c, d, e, f⟩
  rcases hrRetained with ⟨a', b', c', d', e', f'⟩
  exact ⟨a.trans a', b.trans b', c.trans c', d.trans d', e.trans e', f.trans f'⟩

/-- A committed inner scope followed by outer rollback restores the outer writes. -/
theorem nested_refines (s : State) (w₁ w₂ : Snapshot)
    (ar : List Address) (sr : List Slot) (created : List Address) :
    let outer := snapshot s
    let inner := snapshot { outer with writes := w₁ }
    let changed := { inner with writes := w₂, accountReads := ar, storageReads := sr, createdAccounts := created }
    ∃ middle result, commit changed = .ok middle ∧ rollback middle = .ok result ∧
      Commit (observe changed) (observe middle) ∧
      Rollback (observe middle) (observe result) ∧
      (observe result).writes = (observe s).writes ∧
      (observe result).stack = (observe s).stack ∧
      (observe result).accountReads = (fun a => a ∈ ar) ∧
      (observe result).storageReads = (fun p => p ∈ sr) ∧
      (observe result).created = (fun a => a ∈ created) := by
  dsimp only
  refine ⟨_, _, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · apply commit_refines
    rfl
  · apply rollback_refines
    rfl

end EthLib.EVM.TransactionState.Reference
