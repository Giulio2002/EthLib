module
import EthLib.EVM.Proofs

open EthLib.EVM EthLib.EVM.TransactionAccount EthLib.EVM.TransactionState.Reference

example (s : State) (h : Word) := getCode_spec s h
example (s : State) (h : Word) := getCode_none_iff s h
example (s : State) (h : Word) (code : ByteArray) := getCode_some_iff s h code
example (s : State) := getCode_empty s
example (s : State) (a : World.Address) := destroyAccount_spec s a
example (s : State) (a : World.Address) := selectedAccount_eq s a
example (s : State) (a b : World.Address) (f : World.Account → World.Account) :=
  modifyState_accounts s a b f
example (s : State) (a : World.Address) (p : Slot) (f : World.Account → World.Account) :=
  modifyState_storage s a p f
example (s : State) (a b : World.Address) (f : World.Account → World.Account) :=
  modifyState_clears s a b f
example (s : State) (a : World.Address) (p : Slot) (f : World.Account → World.Account) :=
  modifyState_storageReads s a p f
example (s : State) (a b : World.Address) (f : World.Account → World.Account) :=
  modifyState_accountReads s a f b
example (s : State) (a : World.Address) (f : World.Account → World.Account) :=
  modifyState_retained s a f
example (s : State) (a : World.Address) (f : World.Account → World.Account) :=
  modifyState_refines s a f
example (s : State) (a b : World.Address) (balance : Word) :=
  setAccountBalance_accounts s a b balance
example (s : State) (a : World.Address) (balance : Word) :=
  setAccountBalance_refines s a balance
example (s : State) (a b : World.Address) := incrementNonce_accounts s a b
example (s : State) (a : World.Address) := incrementNonce_refines s a
example (s : State) (a : World.Address) (code : ByteArray) (hash : Word) := setCode_code s a code hash
example (s : State) (a b : World.Address) (code : ByteArray) := setCode_accounts s a b code
example (s : State) (a : World.Address) (code : ByteArray) := setCode_refines s a code
example (s : State) (a : World.Address) (code : ByteArray) := setCode_snapshots s a code
example (s : State) (a b : World.Address) (balance : Word) (code : ByteArray) :=
  mutation_nested_rollback s a b balance code
example (code : ByteArray) := World.codeHash_refinement code
example (s : State) (a : World.Address) (f : World.Account → World.Account) :=
  modifyState_code s a f
example (s : State) (a : World.Address) (f : World.Account → World.Account) :=
  modifyState_codeWrites s a f
example (s : State) (a : World.Address) (f : World.Account → World.Account) :=
  modifyState_snapshots s a f
example (first second : State)
    (h : second.snapshots = first.writes :: first.writes :: first.snapshots) :=
  rollback_nested_stack first second h

-- Consume every account-modification observation after the code-recording step.
example (s : State) (a : World.Address) (code : ByteArray) :
    let after := observe (setCode s a code)
    ∃ q : State,
      (∀ hash, (observe q).writes.code hash =
        if World.codeHash code = World.emptyCodeHash then (observe s).writes.code hash
        else if hash = World.codeHash code then some code else (observe s).writes.code hash) ∧
      (∀ b, after.writes.accounts b = if b = a then
        if { (selectedAccount (observe q) a) with codeHash := World.codeHash code } = World.emptyAccount
        then some none else some (some { (selectedAccount (observe q) a) with codeHash := World.codeHash code })
        else (observe q).writes.accounts b) ∧
      (∀ p, after.writes.storage p =
        if { (selectedAccount (observe q) a) with codeHash := World.codeHash code } = World.emptyAccount ∧ p.1 = a
        then none else (observe q).writes.storage p) ∧
      (∀ b, after.writes.clears b ↔
        ({ (selectedAccount (observe q) a) with codeHash := World.codeHash code } = World.emptyAccount ∧ b = a) ∨
          (observe q).writes.clears b) ∧
      (∀ p, after.storageReads p ↔
        ({ (selectedAccount (observe q) a) with codeHash := World.codeHash code } = World.emptyAccount ∧
          p.1 = a ∧ ((observe q).writes.storage p).isSome) ∨ (observe q).storageReads p) ∧
      (∀ b, after.accountReads b ↔ b = a ∨ (observe q).accountReads b) ∧
      after.parentAccounts = (observe q).parentAccounts ∧
      after.parentStorage = (observe q).parentStorage ∧ after.parentCode = (observe q).parentCode ∧
      after.writes.code = (observe q).writes.code ∧ after.writes.transient = (observe q).writes.transient ∧
      after.created = (observe q).created ∧ after.stack = (observe q).stack := by
  obtain ⟨q, hcode, hmodify⟩ := setCode_refines s a code
  exact ⟨q, hcode.2.2.2.2.2, hmodify⟩
