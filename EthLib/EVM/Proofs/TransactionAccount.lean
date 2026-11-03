module

public import EthLib.EVM.TransactionAccount
public import EthLib.EVM.Proofs.TransactionTracker
public import EthLib.EVM.Proofs.World

/-!
# Account and code tracker contracts

The reference observations are maps and sets on arbitrary transaction states.
The source is Amsterdam `state_tracker.py` at revision
`fd9298410ec7218838c8348f69c1eb633f1797dc`.
-/

@[expose] public section
namespace EthLib.EVM.TransactionAccount

open TransactionState.Reference

/-- The empty hash takes priority over both supplied code stores. -/
def CodeValue (v : View) (hash : Word) (result : Option ByteArray) : Prop :=
  (hash = World.emptyCodeHash → result = some ByteArray.empty) ∧
  (hash ≠ World.emptyCodeHash →
    (∀ code, v.writes.code hash = some code → result = some code) ∧
    (v.writes.code hash = none → result = v.parentCode hash))

/-- Code lookup follows the reference priority without changing state. -/
theorem getCode_spec (s : State) (hash : Word) :
    CodeValue (observe s) hash (getCode s hash) := by
  by_cases h : hash = World.emptyCodeHash
  · subst hash
    simp [CodeValue, getCode]
  · have hb : (hash == World.emptyCodeHash) = false := beq_eq_false_iff_ne.mpr h
    unfold CodeValue getCode observe observeWrites World.getCode
    simp only [hb, Bool.false_eq_true, ite_false, ne_eq, h, not_false_eq_true]
    cases s.writes.codeWrites.lookup hash <;> simp

/-- Missing code occurs exactly when both stores lack a nonempty hash. -/
theorem getCode_none_iff (s : State) (hash : Word) :
    getCode s hash = none ↔ hash ≠ World.emptyCodeHash ∧
      (observe s).writes.code hash = none ∧ (observe s).parentCode hash = none := by
  by_cases he : hash = World.emptyCodeHash
  · subst hash
    simp [getCode]
  · have hb : (hash == World.emptyCodeHash) = false := beq_eq_false_iff_ne.mpr he
    unfold getCode observe observeWrites World.getCode
    simp only [hb, Bool.false_eq_true, ite_false]
    cases s.writes.codeWrites.lookup hash <;> simp [he]

/-- A successful code lookup has exactly the source's three priority cases. -/
theorem getCode_some_iff (s : State) (hash : Word) (code : ByteArray) :
    getCode s hash = some code ↔
      (hash = World.emptyCodeHash ∧ code = ByteArray.empty) ∨
      (hash ≠ World.emptyCodeHash ∧
        ((observe s).writes.code hash = some code ∨
          ((observe s).writes.code hash = none ∧ (observe s).parentCode hash = some code))) := by
  by_cases he : hash = World.emptyCodeHash
  · subst hash
    simp [getCode, eq_comm]
  · have hb : (hash == World.emptyCodeHash) = false := beq_eq_false_iff_ne.mpr he
    unfold getCode observe observeWrites World.getCode
    simp only [hb, Bool.false_eq_true, ite_false]
    cases s.writes.codeWrites.lookup hash <;> simp [he]

/-- Code lookup succeeds on the empty sentinel regardless of the stores. -/
theorem getCode_empty (s : State) : getCode s World.emptyCodeHash = some ByteArray.empty := by
  simp [getCode]

/-- Destroying an account preserves all retained observations and records a tombstone. -/
theorem destroyAccount_spec (s : State) (a : World.Address) :
    (∀ b, (observe (destroyAccount s a)).writes.accounts b =
      if b = a then some none else (observe s).writes.accounts b) ∧
    (∀ p, (observe (destroyAccount s a)).writes.storage p =
      if p.1 = a then none else (observe s).writes.storage p) ∧
    (∀ b, (observe (destroyAccount s a)).writes.clears b ↔
      b = a ∨ (observe s).writes.clears b) ∧
    (∀ p, (observe (destroyAccount s a)).storageReads p ↔
      (p.1 = a ∧ ((observe s).writes.storage p).isSome) ∨ (observe s).storageReads p) ∧
    (observe (destroyAccount s a)).writes.code = (observe s).writes.code ∧
    (observe (destroyAccount s a)).writes.transient = (observe s).writes.transient ∧
    (observe (destroyAccount s a)).accountReads = (observe s).accountReads ∧
    (observe (destroyAccount s a)).created = (observe s).created ∧
    (observe (destroyAccount s a)).parentAccounts = (observe s).parentAccounts ∧
    (observe (destroyAccount s a)).parentStorage = (observe s).parentStorage ∧
    (observe (destroyAccount s a)).parentCode = (observe s).parentCode ∧
    (observe (destroyAccount s a)).stack = (observe s).stack := by
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro b
    have h := (TransactionTracker.setAccount_spec (TransactionTracker.destroyStorage s a) a none).2.1 b
    simpa [destroyAccount, observe, observeWrites, TransactionTracker.destroyStorage] using h
  · intro p
    exact TransactionTracker.destroyStorage_storage s a p
  · intro b
    exact (TransactionTracker.destroyStorage_effects s a).2.2.2.2.2.2.2.2.2.1 b
  · intro p
    exact TransactionTracker.destroyStorage_reads s a p

/-- The account selected by the reference overlay, with the empty default. -/
def selectedAccount (v : View) (a : World.Address) : World.Account :=
  ((v.writes.accounts a).getD (v.parentAccounts a)).getD World.emptyAccount

/-- Executable selection agrees with the reference account map. -/
theorem selectedAccount_eq (s : State) (a : World.Address) :
    selectedAccount (observe s) a = (TransactionTracker.getAccount s a).1 := by
  unfold selectedAccount observe observeWrites TransactionTracker.getAccount
    TransactionTracker.getAccountOptional World.getAccountOptional
  cases h : s.writes.accountWrites.lookup a <;> simp [h]

/-- Both account reads in `modify_state` add the same address to the read set. -/
theorem modifyState_accountReads (s : State) (a : World.Address) (f : World.Account → World.Account)
    (b : World.Address) :
    (observe (modifyState s a f)).accountReads b ↔
      b = a ∨ (observe s).accountReads b := by
  simp only [modifyState]
  split <;> simp [observe, TransactionTracker.getAccount,
    TransactionTracker.getAccountOptional, TransactionTracker.setAccount,
    destroyAccount, TransactionTracker.destroyStorage, List.mem_cons]

/-- Account modification retains the immutable parent and rollback metadata. -/
theorem modifyState_retained (s : State) (a : World.Address) (f : World.Account → World.Account) :
    (observe (modifyState s a f)).parentAccounts = (observe s).parentAccounts ∧
    (observe (modifyState s a f)).parentStorage = (observe s).parentStorage ∧
    (observe (modifyState s a f)).parentCode = (observe s).parentCode ∧
    (observe (modifyState s a f)).writes.code = (observe s).writes.code ∧
    (observe (modifyState s a f)).writes.transient = (observe s).writes.transient ∧
    (observe (modifyState s a f)).created = (observe s).created ∧
    (observe (modifyState s a f)).stack = (observe s).stack := by
  simp only [modifyState]
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Modification writes the selected updated account or an empty-account tombstone. -/
theorem modifyState_accounts (s : State) (a b : World.Address) (f : World.Account → World.Account) :
    (observe (modifyState s a f)).writes.accounts b =
      if b = a then
        if f (selectedAccount (observe s) a) = World.emptyAccount then some none
        else some (some (f (selectedAccount (observe s) a)))
      else (observe s).writes.accounts b := by
  rw [selectedAccount_eq]
  have hw : (TransactionTracker.getAccount s a).2.writes.accountWrites = s.writes.accountWrites := rfl
  by_cases hb : b = a
  · subst b
    by_cases he : f (TransactionTracker.getAccount s a).1 = World.emptyAccount <;>
      simp [modifyState, TransactionTracker.getAccountOptional, TransactionTracker.setAccount,
        destroyAccount, TransactionTracker.destroyStorage, observe, observeWrites, he]
  · have hbe : (b == a) = false := beq_eq_false_iff_ne.mpr hb
    by_cases he : f (TransactionTracker.getAccount s a).1 = World.emptyAccount <;>
      simp [modifyState, TransactionTracker.getAccountOptional, TransactionTracker.setAccount,
        destroyAccount, TransactionTracker.destroyStorage, observe, observeWrites,
        List.lookup_cons, hb, hbe, he, hw]

/-- Empty-account cleanup removes its storage overlay; other slots are retained. -/
theorem modifyState_storage (s : State) (a : World.Address) (p : Slot)
    (f : World.Account → World.Account) :
    (observe (modifyState s a f)).writes.storage p =
      if f (selectedAccount (observe s) a) = World.emptyAccount ∧ p.1 = a then none
      else (observe s).writes.storage p := by
  rw [selectedAccount_eq]
  have hf := TransactionTracker.destroyStorage_storage s a p
  change (s.writes.storageWrites.filter (fun entry => entry.1.1 != a)).lookup p =
    if p.1 = a then none else s.writes.storageWrites.lookup p at hf
  have hw : (TransactionTracker.getAccount s a).2.writes.storageWrites = s.writes.storageWrites := rfl
  by_cases he : f (TransactionTracker.getAccount s a).1 = World.emptyAccount
  · simp [modifyState, TransactionTracker.getAccountOptional, TransactionTracker.setAccount,
      destroyAccount, TransactionTracker.destroyStorage, observe, observeWrites, he, hw, hf]
  · simp [modifyState, TransactionTracker.getAccountOptional, TransactionTracker.setAccount,
      observe, observeWrites, he, hw]

/-- Cleanup adds a clear exactly for an updated empty account. -/
theorem modifyState_clears (s : State) (a b : World.Address)
    (f : World.Account → World.Account) :
    (observe (modifyState s a f)).writes.clears b ↔
      (f (selectedAccount (observe s) a) = World.emptyAccount ∧ b = a) ∨
        (observe s).writes.clears b := by
  rw [selectedAccount_eq]
  have hw : (TransactionTracker.getAccount s a).2.writes.storageClears = s.writes.storageClears := rfl
  by_cases he : f (TransactionTracker.getAccount s a).1 = World.emptyAccount
  · simp [modifyState, TransactionTracker.getAccountOptional, TransactionTracker.setAccount,
      destroyAccount, TransactionTracker.destroyStorage, observe, observeWrites, he, hw, List.mem_cons]
  · simp [modifyState, TransactionTracker.getAccountOptional, TransactionTracker.setAccount,
      observe, observeWrites, he, hw]

/-- Cleanup records the discarded storage-overlay keys as reads. -/
theorem modifyState_storageReads (s : State) (a : World.Address) (p : Slot)
    (f : World.Account → World.Account) :
    (observe (modifyState s a f)).storageReads p ↔
      (f (selectedAccount (observe s) a) = World.emptyAccount ∧
        p.1 = a ∧ ((observe s).writes.storage p).isSome) ∨ (observe s).storageReads p := by
  rw [selectedAccount_eq]
  have hread := TransactionTracker.destroyStorage_reads s a p
  have hw : (TransactionTracker.getAccount s a).2.writes.storageWrites = s.writes.storageWrites := rfl
  have hr : (TransactionTracker.getAccount s a).2.storageReads = s.storageReads := rfl
  by_cases he : f (TransactionTracker.getAccount s a).1 = World.emptyAccount
  · simpa [modifyState, TransactionTracker.getAccountOptional, TransactionTracker.setAccount,
      destroyAccount, TransactionTracker.destroyStorage, observe, observeWrites, he, hw, hr] using hread
  · simp [modifyState, TransactionTracker.getAccountOptional, TransactionTracker.setAccount,
      observe, observeWrites, he, hr]

/-- Account modification does not change the code overlay. -/
theorem modifyState_code (s : State) (a : World.Address) (f : World.Account → World.Account) :
    (observe (modifyState s a f)).writes.code = (observe s).writes.code :=
  (modifyState_retained s a f).2.2.2.1

/-- Account cleanup retains the concrete code write history. -/
theorem modifyState_codeWrites (s : State) (a : World.Address) (f : World.Account → World.Account) :
    (modifyState s a f).writes.codeWrites = s.writes.codeWrites := by
  simp only [modifyState]
  split <;> rfl

/-- Code recording changes only the written hash when it differs from the empty sentinel. -/
theorem setCode_code (s : State) (a : World.Address) (code : ByteArray) (hash : Word) :
    (observe (setCode s a code)).writes.code hash =
      if World.codeHash code = World.emptyCodeHash then (observe s).writes.code hash
      else if hash = World.codeHash code then some code else (observe s).writes.code hash := by
  by_cases he : World.codeHash code = World.emptyCodeHash
  · simp [setCode, he, modifyState_code]
  · by_cases hh : hash = World.codeHash code
    · subst hash
      simp [setCode, he, observe, observeWrites, modifyState_codeWrites]
    · have hb : (hash == World.codeHash code) = false := beq_eq_false_iff_ne.mpr hh
      simp [setCode, he, observe, observeWrites, modifyState_codeWrites, List.lookup_cons, hh, hb]

/-- Code assignment updates the account using the hash and the reference account map. -/
theorem setCode_accounts (s : State) (a b : World.Address) (code : ByteArray) :
    (observe (setCode s a code)).writes.accounts b =
      if b = a then
        if { (selectedAccount (observe s) a) with codeHash := World.codeHash code } = World.emptyAccount
        then some none else some (some { (selectedAccount (observe s) a) with codeHash := World.codeHash code })
      else (observe s).writes.accounts b := by
  by_cases he : World.codeHash code = World.emptyCodeHash
  · simpa [setCode, he] using
      modifyState_accounts s a b (fun account => { account with codeHash := World.codeHash code })
  · have hb : (World.codeHash code == World.emptyCodeHash) = false := beq_eq_false_iff_ne.mpr he
    let updated : State := { s with writes := { s.writes with codeWrites :=
        (World.codeHash code, code) :: s.writes.codeWrites } }
    have h := modifyState_accounts updated a b (fun account => { account with codeHash := World.codeHash code })
    have hs : selectedAccount (observe updated) a = selectedAccount (observe s) a := rfl
    have ha : (observe updated).writes.accounts b = (observe s).writes.accounts b := rfl
    rw [hs, ha] at h
    simpa only [setCode, hb, Bool.false_eq_true, ite_false, updated] using h

/-- Balance replacement follows the general independent account update contract. -/
theorem setAccountBalance_accounts (s : State) (a b : World.Address) (balance : Word) :
    (observe (setAccountBalance s a balance)).writes.accounts b =
      if b = a then
        if { (selectedAccount (observe s) a) with balance } = World.emptyAccount then some none
        else some (some { (selectedAccount (observe s) a) with balance })
      else (observe s).writes.accounts b := by
  exact modifyState_accounts s a b (fun account => { account with balance })

/-- Nonce increment follows the general independent account update contract. -/
theorem incrementNonce_accounts (s : State) (a b : World.Address) :
    (observe (incrementNonce s a)).writes.accounts b =
      if b = a then
        if { (selectedAccount (observe s) a) with nonce := (selectedAccount (observe s) a).nonce + 1 }
            = World.emptyAccount then some none
        else some (some { (selectedAccount (observe s) a) with
          nonce := (selectedAccount (observe s) a).nonce + 1 })
      else (observe s).writes.accounts b := by
  exact modifyState_accounts s a b (fun account => { account with nonce := account.nonce + 1 })

/-- Independent full-field account-modification relation. -/
def ModifySpec (before after : View) (a : World.Address) (f : World.Account → World.Account) : Prop :=
  (∀ b, after.writes.accounts b = if b = a then
      if f (selectedAccount before a) = World.emptyAccount then some none
      else some (some (f (selectedAccount before a))) else before.writes.accounts b) ∧
  (∀ p, after.writes.storage p =
      if f (selectedAccount before a) = World.emptyAccount ∧ p.1 = a then none
      else before.writes.storage p) ∧
  (∀ b, after.writes.clears b ↔
      (f (selectedAccount before a) = World.emptyAccount ∧ b = a) ∨ before.writes.clears b) ∧
  (∀ p, after.storageReads p ↔
      (f (selectedAccount before a) = World.emptyAccount ∧ p.1 = a ∧
        (before.writes.storage p).isSome) ∨ before.storageReads p) ∧
  (∀ b, after.accountReads b ↔ b = a ∨ before.accountReads b) ∧
  after.parentAccounts = before.parentAccounts ∧ after.parentStorage = before.parentStorage ∧
  after.parentCode = before.parentCode ∧ after.writes.code = before.writes.code ∧
  after.writes.transient = before.writes.transient ∧ after.created = before.created ∧
  after.stack = before.stack

/-- Modification satisfies every field of the reference relation. -/
theorem modifyState_refines (s : State) (a : World.Address) (f : World.Account → World.Account) :
    ModifySpec (observe s) (observe (modifyState s a f)) a f := by
  exact ⟨fun b => modifyState_accounts s a b f, fun p => modifyState_storage s a p f,
    fun b => modifyState_clears s a b f, fun p => modifyState_storageReads s a p f,
    modifyState_accountReads s a f, modifyState_retained s a f⟩

/-- Balance replacement satisfies the full reference transition. -/
theorem setAccountBalance_refines (s : State) (a : World.Address) (balance : Word) :
    ModifySpec (observe s) (observe (setAccountBalance s a balance)) a
      (fun account => { account with balance }) :=
  modifyState_refines s a (fun account => { account with balance })

/-- Nonce increment satisfies the full reference transition. -/
theorem incrementNonce_refines (s : State) (a : World.Address) :
    ModifySpec (observe s) (observe (incrementNonce s a)) a
      (fun account => { account with nonce := account.nonce + 1 }) :=
  modifyState_refines s a (fun account => { account with nonce := account.nonce + 1 })

/-- Independent code-recording relation before account modification. -/
def CodeInsert (before after : View) (code : ByteArray) : Prop :=
  TransactionTracker.ContextPreserved before after ∧
  after.writes.accounts = before.writes.accounts ∧ after.writes.storage = before.writes.storage ∧
  after.writes.clears = before.writes.clears ∧ after.writes.transient = before.writes.transient ∧
  (∀ hash, after.writes.code hash =
    if World.codeHash code = World.emptyCodeHash then before.writes.code hash
    else if hash = World.codeHash code then some code else before.writes.code hash)

/-- Code assignment refines code recording followed by account modification. -/
theorem setCode_refines (s : State) (a : World.Address) (code : ByteArray) :
    ∃ intermediate : State, CodeInsert (observe s) (observe intermediate) code ∧
      ModifySpec (observe intermediate) (observe (setCode s a code)) a
        (fun account => { account with codeHash := World.codeHash code }) := by
  by_cases he : World.codeHash code = World.emptyCodeHash
  · refine ⟨s, ?_, ?_⟩
    · refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, ?_⟩
      intro hash
      simp [he]
    · simpa [setCode, he] using
        modifyState_refines s a (fun account => { account with codeHash := World.codeHash code })
  · let intermediate : State := { s with writes := { s.writes with codeWrites :=
        (World.codeHash code, code) :: s.writes.codeWrites } }
    refine ⟨intermediate, ?_, ?_⟩
    · refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, ?_⟩
      intro hash
      by_cases hh : hash = World.codeHash code
      · subst hash
        simp [intermediate, observe, observeWrites, he]
      · have hb : (hash == World.codeHash code) = false := beq_eq_false_iff_ne.mpr hh
        simp [intermediate, observe, observeWrites, List.lookup_cons, he, hh, hb]
    · have hb : (World.codeHash code == World.emptyCodeHash) = false := beq_eq_false_iff_ne.mpr he
      simpa only [setCode, hb, Bool.false_eq_true, ite_false, intermediate] using
        modifyState_refines intermediate a (fun account => { account with codeHash := World.codeHash code })

/-- Account modification leaves the nested snapshot stack untouched. -/
theorem modifyState_snapshots (s : State) (a : World.Address) (f : World.Account → World.Account) :
    (modifyState s a f).snapshots = s.snapshots := by
  simp only [modifyState]
  split <;> rfl

/-- Recording code and modifying an account leave the snapshot stack untouched. -/
theorem setCode_snapshots (s : State) (a : World.Address) (code : ByteArray) :
    (setCode s a code).snapshots = s.snapshots := by
  simp only [setCode]
  split <;> exact modifyState_snapshots _ _ _

/-- A stack with two saved copies rolls back to the inner saved writes. -/
theorem rollback_nested_stack (first second : State)
    (hs : second.snapshots = first.writes :: first.writes :: first.snapshots) :
    ∃ result, TransactionState.rollback second = .ok result ∧
      (observe result).writes = (observe first).writes ∧
      (observe result).stack = (observe (TransactionState.snapshot first)).stack ∧
      (observe result).accountReads = (observe second).accountReads ∧
      (observe result).storageReads = (observe second).storageReads ∧
      (observe result).created = (observe second).created ∧
      (observe result).parentAccounts = (observe second).parentAccounts ∧
      (observe result).parentStorage = (observe second).parentStorage ∧
      (observe result).parentCode = (observe second).parentCode := by
  refine ⟨{ second with writes := first.writes, snapshots := first.writes :: first.snapshots },
    ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp [TransactionState.rollback, hs]

/-- A code mutation inside nested snapshots rolls back its writes and retains its reads. -/
theorem mutation_nested_rollback (s : State) (a b : World.Address) (balance : Word) (code : ByteArray) :
    let first := setAccountBalance s a balance
    let second := setCode (TransactionState.snapshot (TransactionState.snapshot first)) b code
    ∃ result, TransactionState.rollback second = .ok result ∧
      (observe result).writes = (observe first).writes ∧
      (observe result).stack = (observe (TransactionState.snapshot first)).stack ∧
      (observe result).accountReads = (observe second).accountReads ∧
      (observe result).storageReads = (observe second).storageReads ∧
      (observe result).created = (observe second).created ∧
      (observe result).parentAccounts = (observe second).parentAccounts ∧
      (observe result).parentStorage = (observe second).parentStorage ∧
      (observe result).parentCode = (observe second).parentCode := by
  let first := setAccountBalance s a balance
  let second := setCode (TransactionState.snapshot (TransactionState.snapshot first)) b code
  have hs : second.snapshots = first.writes :: first.writes :: first.snapshots :=
    setCode_snapshots (TransactionState.snapshot (TransactionState.snapshot first)) b code
  exact rollback_nested_stack first second hs

end EthLib.EVM.TransactionAccount
