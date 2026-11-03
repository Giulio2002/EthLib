module

public import EthLib.EVM.TransactionTracker
public import EthLib.EVM.Proofs.TransactionStateReference

/-!
# Transaction tracker observations

The reference read rules use the total map and set observations from
`TransactionState.Reference`, independent of association-list operations.
-/

@[expose] public section
namespace EthLib.EVM.TransactionTracker

open TransactionState.Reference

/-- An account write shadows the transaction-start parent, including deletion. -/
def AccountValue (v : View) (a : World.Address) (result : Option World.Account) : Prop :=
  (∀ x, v.writes.accounts a = some x → result = x) ∧
  (v.writes.accounts a = none → result = v.parentAccounts a)

/-- A storage write has priority over a clear and the transaction-start parent. -/
def StorageValue (v : View) (a : World.Address) (k result : Word) : Prop :=
  (∀ x, v.writes.storage (a, k) = some x → result = x) ∧
  (v.writes.storage (a, k) = none → v.writes.clears a → result = 0) ∧
  (v.writes.storage (a, k) = none → ¬ v.writes.clears a → result = v.parentStorage (a, k))

/-- An account is absent after applying the account overlay to the parent. -/
def AccountAbsent (v : View) (a : World.Address) : Prop :=
  v.writes.accounts a = some none ∨
    (v.writes.accounts a = none ∧ v.parentAccounts a = none)

/-- All fields except account reads are preserved by an account read. -/
def AccountReadEffect (before after : View) (a : World.Address) : Prop :=
  before.parentAccounts = after.parentAccounts ∧ before.parentStorage = after.parentStorage ∧
  before.parentCode = after.parentCode ∧ before.writes = after.writes ∧
  (∀ b, after.accountReads b ↔ b = a ∨ before.accountReads b) ∧
  before.storageReads = after.storageReads ∧ before.created = after.created ∧
  before.stack = after.stack

/-- All fields except persistent storage reads are preserved by a storage read. -/
def StorageReadEffect (before after : View) (a : World.Address) (k : Word) : Prop :=
  before.parentAccounts = after.parentAccounts ∧ before.parentStorage = after.parentStorage ∧
  before.parentCode = after.parentCode ∧ before.writes = after.writes ∧
  before.accountReads = after.accountReads ∧
  (∀ p, after.storageReads p ↔ p = (a, k) ∨ before.storageReads p) ∧
  before.created = after.created ∧ before.stack = after.stack

/-- World.Account lookup and its read-set effect refine the reference on all inputs. -/
theorem getAccountOptional_spec (s : State) (a : World.Address) :
    AccountValue (observe s) a (getAccountOptional s a).1 ∧
    AccountReadEffect (observe s) (observe (getAccountOptional s a).2) a := by
  constructor
  · unfold AccountValue getAccountOptional observe observeWrites
    cases h : s.writes.accountWrites.lookup a <;> simp [h, World.getAccountOptional]
  · simp [AccountReadEffect, getAccountOptional, observe, List.mem_cons]

/-- The optional account result is absent exactly in the reference cases. -/
theorem getAccountOptional_none_iff (s : State) (a : World.Address) :
    (getAccountOptional s a).1 = none ↔ AccountAbsent (observe s) a := by
  unfold AccountAbsent getAccountOptional observe observeWrites World.getAccountOptional
  cases h : s.writes.accountWrites.lookup a with
  | none => simp [h]
  | some value => cases value <;> simp [h]

/-- The defaulting account read has the same read-set effect. -/
theorem getAccount_spec (s : State) (a : World.Address) :
    (getAccount s a).1 = (getAccountOptional s a).1.getD World.emptyAccount ∧
    AccountReadEffect (observe s) (observe (getAccount s a).2) a := by
  exact ⟨rfl, (getAccountOptional_spec s a).2⟩

/-- The defaulting account read follows the independent account map rule. -/
theorem getAccount_value (s : State) (a : World.Address) :
    (∀ x, (observe s).writes.accounts a = some x →
      (getAccount s a).1 = x.getD World.emptyAccount) ∧
    ((observe s).writes.accounts a = none →
      (getAccount s a).1 = ((observe s).parentAccounts a).getD World.emptyAccount) := by
  have h := (getAccountOptional_spec s a).1
  constructor
  · intro x hx
    have hv := h.1 x hx
    simp [getAccount, hv]
  · intro hx
    have hv := h.2 hx
    simp [getAccount, hv]

/-- Storage lookup and its read-set effect refine the reference on all inputs. -/
theorem getStorage_spec (s : State) (a : World.Address) (k : Word) :
    StorageValue (observe s) a k (getStorage s a k).1 ∧
    StorageReadEffect (observe s) (observe (getStorage s a k).2) a k := by
  constructor
  · unfold StorageValue getStorage observe observeWrites
    cases h : s.writes.storageWrites.lookup (a, k) with
    | some x => simp [h]
    | none =>
      by_cases hc : a ∈ s.writes.storageClears <;>
        simp [h, hc, World.getStorage]
  · simp [StorageReadEffect, getStorage, observe, List.mem_cons]

/-- A transient read returns the current transient map value or zero. -/
theorem getTransientStorage_spec (s : State) (a : World.Address) (k : Word) :
    getTransientStorage s a k = ((observe s).writes.transient (a, k)).getD 0 := rfl

/-- A created marker changes membership only at the given address. -/
theorem markAccountCreated_spec (s : State) (a b : World.Address) :
    (observe (markAccountCreated s a)).created b ↔ b = a ∨ (observe s).created b := by
  simp [observe, markAccountCreated, List.mem_cons]

/-- All parent, read, created and snapshot observations are unchanged. -/
def ContextPreserved (before after : View) : Prop :=
  before.parentAccounts = after.parentAccounts ∧ before.parentStorage = after.parentStorage ∧
  before.parentCode = after.parentCode ∧ before.accountReads = after.accountReads ∧
  before.storageReads = after.storageReads ∧ before.created = after.created ∧
  before.stack = after.stack

/-- An account write changes exactly the selected account overlay entry. -/
theorem setAccount_spec (s : State) (a : World.Address) (value : Option World.Account) :
    ContextPreserved (observe s) (observe (setAccount s a value)) ∧
    (∀ b, (observe (setAccount s a value)).writes.accounts b =
      if b = a then some value else (observe s).writes.accounts b) ∧
    (observe (setAccount s a value)).writes.storage = (observe s).writes.storage ∧
    (observe (setAccount s a value)).writes.code = (observe s).writes.code ∧
    (observe (setAccount s a value)).writes.clears = (observe s).writes.clears ∧
    (observe (setAccount s a value)).writes.transient = (observe s).writes.transient := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, rfl, rfl, rfl, rfl⟩
  intro b
  by_cases h : b = a
  · subst b
    simp [observe, observeWrites, setAccount]
  · have hb : (b == a) = false := beq_eq_false_iff_ne.mpr h
    simp [observe, observeWrites, setAccount, List.lookup_cons, h, hb]

/-- A failed write is exactly an absent effective account, with its read recorded. -/
theorem setStorage_error_iff (s : State) (a : World.Address) (k value : Word) :
    setStorage s a k value = .error (.missingAccount, (getAccountOptional s a).2) ↔
      (getAccountOptional s a).1 = none := by
  unfold setStorage
  cases h : (getAccountOptional s a).1 <;> simp [h]

/-- Every storage-write error carries exactly the state after the account read. -/
theorem setStorage_error_state_iff (s t : State) (a : World.Address) (k value : Word) :
    setStorage s a k value = .error (.missingAccount, t) ↔
      (getAccountOptional s a).1 = none ∧ t = (getAccountOptional s a).2 := by
  unfold setStorage
  cases h : (getAccountOptional s a).1 <;> simp [h, eq_comm]

/-- Failure is exactly reference account absence, with the recorded read state. -/
theorem setStorage_reference_error_iff (s t : State) (a : World.Address) (k value : Word) :
    setStorage s a k value = .error (.missingAccount, t) ↔
      AccountAbsent (observe s) a ∧ t = (getAccountOptional s a).2 := by
  rw [setStorage_error_state_iff, getAccountOptional_none_iff]

/-- The account read is present on either storage-write outcome. -/
theorem setStorage_accountRead (s : State) (a : World.Address) (k value : Word) :
    match setStorage s a k value with
    | .error (_, t) => a ∈ t.accountReads
    | .ok t => a ∈ t.accountReads := by
  unfold setStorage
  cases h : (getAccountOptional s a).1 <;> simp only [h]
  all_goals change a ∈ a :: s.accountReads
  all_goals exact List.mem_cons_self

/-- A successful storage write changes only its overlay slot and records the account read. -/
theorem setStorage_spec (s t : State) (a : World.Address) (k value : Word)
    (h : setStorage s a k value = .ok t) :
    (∀ p, (observe t).writes.storage p =
      if p = (a, k) then some value else (observe s).writes.storage p) ∧
    (observe t).writes.accounts = (observe s).writes.accounts ∧
    (observe t).writes.code = (observe s).writes.code ∧
    (observe t).writes.clears = (observe s).writes.clears ∧
    (observe t).writes.transient = (observe s).writes.transient ∧
    (∀ b, (observe t).accountReads b ↔ b = a ∨ (observe s).accountReads b) ∧
    (observe t).storageReads = (observe s).storageReads ∧
    (observe t).created = (observe s).created ∧
    (observe t).parentAccounts = (observe s).parentAccounts ∧
    (observe t).parentStorage = (observe s).parentStorage ∧
    (observe t).parentCode = (observe s).parentCode ∧
    (observe t).stack = (observe s).stack := by
  unfold setStorage at h
  cases ha : (getAccountOptional s a).1 with
  | none => simp [ha] at h
  | some account =>
    simp only [ha, Except.ok.injEq] at h
    subst t
    refine ⟨?_, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro p
      by_cases hp : p = (a, k)
      · subst p
        simp [observe, observeWrites, getAccountOptional]
      · have hb : (p == (a, k)) = false := beq_eq_false_iff_ne.mpr hp
        simp [observe, observeWrites, getAccountOptional, List.lookup_cons, hp, hb]
    · intro b
      simp [observe, getAccountOptional, List.mem_cons]

/-- A storage write succeeds exactly when the effective account is present. -/
theorem setStorage_success_iff (s : State) (a : World.Address) (k value : Word) :
    (∃ t, setStorage s a k value = .ok t) ↔
      ∃ account, (getAccountOptional s a).1 = some account := by
  unfold setStorage
  cases h : (getAccountOptional s a).1 <;> simp [h]

private theorem lookup_filter_ne {α β : Type} [BEq α] [LawfulBEq α]
    (xs : List (α × β)) (a b : α) (h : a ≠ b) :
    (xs.filter (fun p => p.1 != b)).lookup a = xs.lookup a := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨k, v⟩
    by_cases hk : k = b <;> by_cases ha : a = k <;>
      simp_all [List.lookup_cons, beq_eq_false_iff_ne.mpr h]

private theorem lookup_filter_same {α β : Type} [BEq α] [LawfulBEq α]
    (xs : List (α × β)) (a : α) :
    (xs.filter (fun p => p.1 != a)).lookup a = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨k, v⟩
    by_cases hk : k = a
    · subst k
      simpa only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ite_false] using ih
    · have hb : (k != a) = true := bne_iff_ne.mpr hk
      have ha : (a == k) = false := beq_eq_false_iff_ne.mpr (Ne.symm hk)
      simp [hb, List.lookup_cons, ha, ih]

/-- A transient write deletes a zero and changes no other observable field. -/
theorem setTransientStorage_spec (s : State) (a : World.Address) (k value : Word) :
    ContextPreserved (observe s) (observe (setTransientStorage s a k value)) ∧
    (∀ p, (observe (setTransientStorage s a k value)).writes.transient p =
      if p = (a, k) then (if value = 0 then none else some value)
      else (observe s).writes.transient p) ∧
    (observe (setTransientStorage s a k value)).writes.accounts = (observe s).writes.accounts ∧
    (observe (setTransientStorage s a k value)).writes.storage = (observe s).writes.storage ∧
    (observe (setTransientStorage s a k value)).writes.code = (observe s).writes.code ∧
    (observe (setTransientStorage s a k value)).writes.clears = (observe s).writes.clears := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, rfl, rfl, rfl, rfl⟩
  intro p
  by_cases hp : p = (a, k)
  · subst p
    by_cases hv : value = 0
    · subst value
      simp [observe, observeWrites, setTransientStorage, lookup_filter_same]
    · have hz : value ≠ 0#256 := by simpa using hv
      simp [observe, observeWrites, setTransientStorage, hz]
  · have hb : (p == (a, k)) = false := beq_eq_false_iff_ne.mpr hp
    by_cases hv : value = 0
    · subst value
      simp [observe, observeWrites, setTransientStorage, hp, lookup_filter_ne _ _ _ hp]
    · have hz : value ≠ 0#256 := by simpa using hv
      simp [observe, observeWrites, setTransientStorage, hz, hp, hb, List.lookup_cons,
        lookup_filter_ne _ _ _ hp]

private theorem lookup_filter_address (xs : List ((World.Address × Word) × Word))
    (p : World.Address × Word) (a : World.Address) :
    (xs.filter (fun entry => entry.1.1 != a)).lookup p =
      if p.1 = a then none else xs.lookup p := by
  by_cases hp : p.1 = a
  · simp only [hp, ↓reduceIte]
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      rcases x with ⟨⟨b, k⟩, v⟩
      by_cases hb : b = a
      · subst b
        simpa using ih
      · have he : p ≠ (b, k) := by
          intro eq
          have := congrArg Prod.fst eq
          exact hb (this.symm.trans hp)
        have hbe : (p == (b, k)) = false := beq_eq_false_iff_ne.mpr he
        have hbb : (b != a) = true := bne_iff_ne.mpr hb
        simp [hbb, List.lookup_cons, hbe, ih]
  · simp only [hp, ↓reduceIte]
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      rcases x with ⟨⟨b, k⟩, v⟩
      by_cases hb : b = a
      · subst b
        have he : p ≠ (a, k) := by
          intro eq
          exact hp (congrArg Prod.fst eq)
        have hbe : (p == (a, k)) = false := beq_eq_false_iff_ne.mpr he
        simp [List.lookup_cons, hbe, ih]
      · have hbb : (b != a) = true := bne_iff_ne.mpr hb
        simp [hbb, List.lookup_cons, ih]

/-- Clearing removes precisely the storage overlay entries at the address. -/
theorem destroyStorage_storage (s : State) (a : World.Address) (p : Slot) :
    (observe (destroyStorage s a)).writes.storage p =
      if p.1 = a then none else (observe s).writes.storage p := by
  exact lookup_filter_address s.writes.storageWrites p a

/-- Clearing retains the non-storage fields and records discarded storage keys as reads. -/
theorem destroyStorage_effects (s : State) (a : World.Address) :
    (observe (destroyStorage s a)).parentAccounts = (observe s).parentAccounts ∧
    (observe (destroyStorage s a)).parentStorage = (observe s).parentStorage ∧
    (observe (destroyStorage s a)).parentCode = (observe s).parentCode ∧
    (observe (destroyStorage s a)).writes.accounts = (observe s).writes.accounts ∧
    (observe (destroyStorage s a)).writes.code = (observe s).writes.code ∧
    (observe (destroyStorage s a)).writes.transient = (observe s).writes.transient ∧
    (observe (destroyStorage s a)).accountReads = (observe s).accountReads ∧
    (observe (destroyStorage s a)).created = (observe s).created ∧
    (observe (destroyStorage s a)).stack = (observe s).stack ∧
    (∀ b, (observe (destroyStorage s a)).writes.clears b ↔
      b = a ∨ (observe s).writes.clears b) ∧
    (∀ p, (observe (destroyStorage s a)).storageReads p ↔
      (∃ value, (p, value) ∈ s.writes.storageWrites ∧ p.1 = a) ∨
        (observe s).storageReads p) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro b
    simp [observe, observeWrites, destroyStorage, List.mem_cons]
  · intro p
    simp only [observe, destroyStorage, List.mem_append, List.mem_map, List.mem_filter,
      beq_iff_eq]
    constructor
    · rintro (⟨⟨q, v⟩, ⟨hm, ha⟩, eq⟩ | old)
      · cases eq
        exact Or.inl ⟨v, hm, ha⟩
      · exact Or.inr old
    · rintro (⟨v, hm, ha⟩ | old)
      · exact Or.inl ⟨(p, v), ⟨hm, ha⟩, rfl⟩
      · exact Or.inr old

/-- Clearing adds exactly the prior overlay keys at the address to storage reads. -/
theorem destroyStorage_reads (s : State) (a : World.Address) (p : Slot) :
    (observe (destroyStorage s a)).storageReads p ↔
      (p.1 = a ∧ ((observe s).writes.storage p).isSome) ∨ (observe s).storageReads p := by
  have h := (destroyStorage_effects s a).2.2.2.2.2.2.2.2.2.2 p
  have hex : (∃ value, (p, value) ∈ s.writes.storageWrites) ↔
      ((observe s).writes.storage p).isSome := by
    simp only [observe, observeWrites, List.lookup_isSome_iff, beq_iff_eq]
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨(p, v), hv, rfl⟩
    · rintro ⟨⟨key, value⟩, hm, eq⟩
      cases eq
      exact ⟨value, hm⟩
  constructor
  · intro hp
    rcases h.mp hp with ⟨value, hm, ha⟩ | old
    · exact Or.inl ⟨ha, hex.mp ⟨value, hm⟩⟩
    · exact Or.inr old
  · intro hp
    rcases hp with ⟨ha, hm⟩ | old
    · obtain ⟨value, hv⟩ := hex.mpr hm
      exact h.mpr (Or.inl ⟨value, hv, ha⟩)
    · exact h.mpr (Or.inr old)

/-- Marking creation preserves all observations other than the created set. -/
theorem markAccountCreated_preserves (s : State) (a : World.Address) :
    (observe (markAccountCreated s a)).parentAccounts = (observe s).parentAccounts ∧
    (observe (markAccountCreated s a)).parentStorage = (observe s).parentStorage ∧
    (observe (markAccountCreated s a)).parentCode = (observe s).parentCode ∧
    (observe (markAccountCreated s a)).writes = (observe s).writes ∧
    (observe (markAccountCreated s a)).accountReads = (observe s).accountReads ∧
    (observe (markAccountCreated s a)).storageReads = (observe s).storageReads ∧
    (observe (markAccountCreated s a)).stack = (observe s).stack := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A successful storage write retains the snapshot stack exactly. -/
theorem setStorage_snapshots (s t : State) (a : World.Address) (k value : Word)
    (h : setStorage s a k value = .ok t) : t.snapshots = s.snapshots := by
  unfold setStorage at h
  cases ha : (getAccountOptional s a).1 with
  | none => simp [ha] at h
  | some account =>
    simp only [ha, Except.ok.injEq] at h
    subst t
    rfl

/-- Two successful writes around nested snapshots roll back the inner write.

The result keeps the account reads recorded by both writes.
-/
theorem write_nested_rollback (s first second : State) (a b : World.Address)
    (k j x y : Word) (hfirst : setStorage s a k x = .ok first)
    (hsecond : setStorage (TransactionState.snapshot (TransactionState.snapshot first)) b j y = .ok second) :
    ∃ result, TransactionState.rollback second = .ok result ∧
      (observe result).writes = (observe first).writes ∧
      (observe result).stack = (observe (TransactionState.snapshot first)).stack ∧
      (∀ c, (observe result).accountReads c ↔
        c = b ∨ c = a ∨ (observe s).accountReads c) ∧
      (observe result).storageReads = (observe s).storageReads ∧
      (observe result).created = (observe s).created ∧
      (observe result).parentStorage = (observe s).parentStorage ∧
      (observe result).parentAccounts = (observe s).parentAccounts ∧
      (observe result).parentCode = (observe s).parentCode := by
  have hstack := setStorage_snapshots _ _ _ _ _ hsecond
  change second.snapshots = first.writes :: first.writes :: first.snapshots at hstack
  refine ⟨{ second with writes := first.writes, snapshots := first.writes :: first.snapshots }, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [TransactionState.rollback, hstack]
  · rfl
  · intro c
    have hread2 := (setStorage_spec _ _ _ _ _ hsecond).2.2.2.2.2.1 c
    have hread1 := (setStorage_spec _ _ _ _ _ hfirst).2.2.2.2.2.1 c
    have hr1 : c ∈ first.accountReads ↔ c = a ∨ c ∈ s.accountReads := by
      simpa [observe] using hread1
    simpa [observe, TransactionState.snapshot, hr1] using hread2
  · have h1 := (setStorage_spec _ _ _ _ _ hfirst).2.2.2.2.2.2.1
    have h2 := (setStorage_spec _ _ _ _ _ hsecond).2.2.2.2.2.2.1
    exact h2.trans h1
  · have h1 := (setStorage_spec _ _ _ _ _ hfirst).2.2.2.2.2.2.2.1
    have h2 := (setStorage_spec _ _ _ _ _ hsecond).2.2.2.2.2.2.2.1
    exact h2.trans h1
  · have h1 := (setStorage_spec _ _ _ _ _ hfirst).2.2.2.2.2.2.2.2.2.1
    have h2 := (setStorage_spec _ _ _ _ _ hsecond).2.2.2.2.2.2.2.2.2.1
    exact h2.trans h1
  · have h1 := (setStorage_spec _ _ _ _ _ hfirst).2.2.2.2.2.2.2.2.1
    have h2 := (setStorage_spec _ _ _ _ _ hsecond).2.2.2.2.2.2.2.2.1
    exact h2.trans h1
  · have h1 := (setStorage_spec _ _ _ _ _ hfirst).2.2.2.2.2.2.2.2.2.2.1
    have h2 := (setStorage_spec _ _ _ _ _ hsecond).2.2.2.2.2.2.2.2.2.2.1
    exact h2.trans h1

end EthLib.EVM.TransactionTracker
