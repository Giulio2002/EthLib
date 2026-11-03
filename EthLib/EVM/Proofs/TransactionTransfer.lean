module

public import EthLib.EVM.TransactionTransfer
public import EthLib.EVM.Proofs.TransactionAccount

/-!
# Transfer reference contracts

The reference relations describe natural-number bounds and the existing
independent tracker observations at each source failure boundary.
-/

@[expose] public section
namespace EthLib.EVM.TransactionTransfer

open TransactionState.Reference
open TransactionAccount

/-- The sender-side assertion fails after its account read. -/
def InsufficientSpec (before after : View) (sender : Address) (amount : Word) : Prop :=
  (selectedAccount before sender).balance.toNat < amount.toNat ∧
  TransactionTracker.AccountReadEffect before after sender

/-- The debit completes, then checked recipient addition fails after its read. -/
def OverflowSpec (before after : View) (sender recipient : Address) (amount : Word) : Prop :=
  amount.toNat ≤ (selectedAccount before sender).balance.toNat ∧
  ∃ debit : View,
    ModifySpec before debit sender (fun account => { account with balance := BitVec.ofNat 256 ((selectedAccount before sender).balance.toNat - amount.toNat) }) ∧
    Word.modulus ≤ (selectedAccount debit recipient).balance.toNat + amount.toNat ∧
    TransactionTracker.AccountReadEffect debit after recipient

/-- Both checked modifications succeed in sender-then-recipient order. -/
def SuccessSpec (before after : View) (sender recipient : Address) (amount : Word) : Prop :=
  amount.toNat ≤ (selectedAccount before sender).balance.toNat ∧
  ∃ debit : View,
    ModifySpec before debit sender (fun account => { account with balance := BitVec.ofNat 256 ((selectedAccount before sender).balance.toNat - amount.toNat) }) ∧
    (selectedAccount debit recipient).balance.toNat + amount.toNat < Word.modulus ∧
    ModifySpec debit after recipient (fun account => { account with balance := BitVec.ofNat 256 ((selectedAccount debit recipient).balance.toNat + amount.toNat) })

/-- Every result follows exactly one reference branch with its full field effects. -/
theorem moveEther_refines (s : State) (sender recipient : Address) (amount : Word) :
    match moveEther s sender recipient amount with
    | .error (.insufficientBalance, t) => InsufficientSpec (observe s) (observe t) sender amount
    | .error (.recipientOverflow, t) => OverflowSpec (observe s) (observe t) sender recipient amount
    | .ok t => SuccessSpec (observe s) (observe t) sender recipient amount := by
  by_cases hsender : (TransactionTracker.getAccount s sender).1.balance.toNat < amount.toNat
  · simp only [moveEther, hsender, ↓reduceIte]
    refine ⟨?_, (TransactionTracker.getAccount_spec s sender).2⟩
    simpa only [selectedAccount_eq] using hsender
  · let debit := TransactionAccount.setAccountBalance s sender
      (BitVec.ofNat 256 ((TransactionTracker.getAccount s sender).1.balance.toNat - amount.toNat))
    by_cases hoverflow : Word.modulus ≤ (TransactionTracker.getAccount debit recipient).1.balance.toNat + amount.toNat
    · simp only [moveEther, hsender, ↓reduceIte]
      rw [ite_eq_left hoverflow]
      change OverflowSpec (observe s) (observe (TransactionTracker.getAccount debit recipient).2) sender recipient amount
      refine ⟨?_, observe debit, ?_, ?_, ?_⟩
      · simpa only [selectedAccount_eq] using Nat.le_of_not_gt hsender
      · simpa only [selectedAccount_eq] using
          TransactionAccount.setAccountBalance_refines s sender
            (BitVec.ofNat 256 ((TransactionTracker.getAccount s sender).1.balance.toNat - amount.toNat))
      · simpa only [selectedAccount_eq] using hoverflow
      · exact (TransactionTracker.getAccount_spec debit recipient).2
    · simp only [moveEther, hsender, ↓reduceIte]
      rw [ite_eq_right hoverflow]
      change SuccessSpec (observe s) (observe (TransactionAccount.setAccountBalance debit recipient
        (BitVec.ofNat 256 ((TransactionTracker.getAccount debit recipient).1.balance.toNat + amount.toNat)))) sender recipient amount
      refine ⟨?_, observe debit, ?_, ?_, ?_⟩
      · simpa only [selectedAccount_eq] using Nat.le_of_not_gt hsender
      · simpa only [selectedAccount_eq] using
          TransactionAccount.setAccountBalance_refines s sender
            (BitVec.ofNat 256 ((TransactionTracker.getAccount s sender).1.balance.toNat - amount.toNat))
      · simpa only [selectedAccount_eq] using Nat.lt_of_not_ge hoverflow
      · simpa only [selectedAccount_eq] using
          TransactionAccount.setAccountBalance_refines debit recipient
            (BitVec.ofNat 256 ((TransactionTracker.getAccount debit recipient).1.balance.toNat + amount.toNat))

/-- Insufficient balance is exactly the first failure and preserves the first read. -/
theorem insufficient_iff (s t : State) (sender recipient : Address) (amount : Word) :
    moveEther s sender recipient amount = .error (.insufficientBalance, t) ↔
      (TransactionTracker.getAccount s sender).1.balance.toNat < amount.toNat ∧
      t = (TransactionTracker.getAccount s sender).2 := by
  by_cases h : (TransactionTracker.getAccount s sender).1.balance.toNat < amount.toNat
  · simp [moveEther, h, eq_comm]
  · simp only [moveEther, h, ↓reduceIte, false_and, iff_false]
    split <;> simp

/-- Recipient overflow occurs only after a successful debit and retains its read. -/
theorem overflow_iff (s t : State) (sender recipient : Address) (amount : Word) :
    let senderRead := TransactionTracker.getAccount s sender
    let debit := TransactionAccount.setAccountBalance s sender
      (BitVec.ofNat 256 (senderRead.1.balance.toNat - amount.toNat))
    moveEther s sender recipient amount = .error (.recipientOverflow, t) ↔
      amount.toNat ≤ senderRead.1.balance.toNat ∧
      Word.modulus ≤ (TransactionTracker.getAccount debit recipient).1.balance.toNat + amount.toNat ∧
      t = (TransactionTracker.getAccount debit recipient).2 := by
  dsimp only
  by_cases h : (TransactionTracker.getAccount s sender).1.balance.toNat < amount.toNat
  · simp [moveEther, h, Nat.not_le_of_gt h]
  · have hn := Nat.le_of_not_gt h
    simp only [moveEther, h, ↓reduceIte, hn, true_and]
    split <;> simp_all [eq_comm]

/-- Success occurs exactly when both checked operations are in range. -/
theorem success_iff (s t : State) (sender recipient : Address) (amount : Word) :
    let senderRead := TransactionTracker.getAccount s sender
    let debit := TransactionAccount.setAccountBalance s sender
      (BitVec.ofNat 256 (senderRead.1.balance.toNat - amount.toNat))
    let receiverRead := TransactionTracker.getAccount debit recipient
    moveEther s sender recipient amount = .ok t ↔
      amount.toNat ≤ senderRead.1.balance.toNat ∧
      receiverRead.1.balance.toNat + amount.toNat < Word.modulus ∧
      t = TransactionAccount.setAccountBalance debit recipient
        (BitVec.ofNat 256 (receiverRead.1.balance.toNat + amount.toNat)) := by
  dsimp only
  by_cases h : (TransactionTracker.getAccount s sender).1.balance.toNat < amount.toNat
  · simp [moveEther, h, Nat.not_le_of_gt h]
  · have hn := Nat.le_of_not_gt h
    simp only [moveEther, h, ↓reduceIte, hn, true_and]
    split <;> simp_all [eq_comm, Nat.not_lt_of_ge]

/-- A reference modification exposes its updated account even after empty cleanup. -/
theorem modify_selected (before after : View) (a : Address) (f : World.Account → World.Account)
    (h : ModifySpec before after a f) :
    selectedAccount after a = f (selectedAccount before a) := by
  have haccount := h.1 a
  by_cases he : f (selectedAccount before a) = World.emptyAccount
  · simp [he] at haccount
    rw [he]
    simp [selectedAccount, haccount]
  · simp [he] at haccount
    simp [selectedAccount, haccount]

/-- A reference modification leaves every other selected account unchanged. -/
theorem modify_other (before after : View) (a b : Address) (f : World.Account → World.Account)
    (h : ModifySpec before after a f) (hne : b ≠ a) :
    selectedAccount after b = selectedAccount before b := by
  have haccount := h.1 b
  have hparent := h.2.2.2.2.2.1
  simp only [hne, ↓reduceIte] at haccount
  simp [selectedAccount, haccount, hparent]

/-- A checked subtraction is represented without modular reduction. -/
theorem debit_exact (balance amount : Word) :
    (BitVec.ofNat 256 (balance.toNat - amount.toNat)).toNat = balance.toNat - amount.toNat := by
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) balance.isLt

/-- A checked addition is represented without modular reduction. -/
theorem credit_exact (balance amount : Word) (h : balance.toNat + amount.toNat < Word.modulus) :
    (BitVec.ofNat 256 (balance.toNat + amount.toNat)).toNat = balance.toNat + amount.toNat := by
  exact Nat.mod_eq_of_lt h

/-- Distinct-account success has exact debited and credited natural balances. -/
theorem success_distinct_balances (before after : View) (sender recipient : Address) (amount : Word)
    (h : SuccessSpec before after sender recipient amount) (hne : sender ≠ recipient) :
    (selectedAccount after sender).balance.toNat = (selectedAccount before sender).balance.toNat - amount.toNat ∧
    (selectedAccount after recipient).balance.toNat = (selectedAccount before recipient).balance.toNat + amount.toNat := by
  obtain ⟨_, debit, hdebit, hbound, hcredit⟩ := h
  have hd := congrArg (fun account : World.Account => account.balance.toNat)
    (modify_selected before debit sender _ hdebit)
  have hr := congrArg (fun account : World.Account => account.balance.toNat)
    (modify_selected debit after recipient _ hcredit)
  have hs := congrArg (fun account : World.Account => account.balance.toNat)
    (modify_other debit after recipient sender _ hcredit hne)
  have hother := congrArg (fun account : World.Account => account.balance.toNat)
    (modify_other before debit sender recipient _ hdebit (Ne.symm hne))
  dsimp only at hd hr
  rw [debit_exact] at hd
  rw [credit_exact _ _ hbound] at hr
  exact ⟨hs.trans hd, hr.trans (congrArg (fun n => n + amount.toNat) hother)⟩

/-- Successful transfers between distinct addresses conserve their total balance. -/
theorem success_distinct_conservation (before after : View) (sender recipient : Address) (amount : Word)
    (h : SuccessSpec before after sender recipient amount) (hne : sender ≠ recipient) :
    (selectedAccount after sender).balance.toNat + (selectedAccount after recipient).balance.toNat =
      (selectedAccount before sender).balance.toNat + (selectedAccount before recipient).balance.toNat := by
  obtain ⟨hs, hr⟩ := success_distinct_balances before after sender recipient amount h hne
  have funds := h.1
  omega

/-- A successful self-transfer restores the initial balance after the ordered updates. -/
theorem success_self_balance (before after : View) (address : Address) (amount : Word)
    (h : SuccessSpec before after address address amount) :
    (selectedAccount after address).balance.toNat = (selectedAccount before address).balance.toNat := by
  obtain ⟨hfund, debit, hdebit, hbound, hcredit⟩ := h
  have hd := congrArg (fun account : World.Account => account.balance.toNat)
    (modify_selected before debit address _ hdebit)
  have hr := congrArg (fun account : World.Account => account.balance.toNat)
    (modify_selected debit after address _ hcredit)
  dsimp only at hd hr
  rw [debit_exact] at hd
  rw [credit_exact _ _ hbound] at hr
  rw [hd] at hr
  simpa [Nat.sub_add_cancel hfund] using hr

/-- A successful transfer leaves other selected accounts unchanged. -/
theorem success_other_account (before after : View) (sender recipient other : Address) (amount : Word)
    (h : SuccessSpec before after sender recipient amount)
    (hs : other ≠ sender) (hr : other ≠ recipient) :
    selectedAccount after other = selectedAccount before other := by
  obtain ⟨_, debit, hdebit, _, hcredit⟩ := h
  exact (modify_other debit after recipient other _ hcredit hr).trans
    (modify_other before debit sender other _ hdebit hs)

/-- A successful transfer preserves parent, code, transient, created and snapshot observations. -/
theorem success_retained (before after : View) (sender recipient : Address) (amount : Word)
    (h : SuccessSpec before after sender recipient amount) :
    after.parentAccounts = before.parentAccounts ∧ after.parentStorage = before.parentStorage ∧
    after.parentCode = before.parentCode ∧ after.writes.code = before.writes.code ∧
    after.writes.transient = before.writes.transient ∧ after.created = before.created ∧
    after.stack = before.stack := by
  obtain ⟨_, debit, hd, _, hc⟩ := h
  rcases hd.2.2.2.2.2 with ⟨a, b, c, d, e, f, g⟩
  rcases hc.2.2.2.2.2 with ⟨a', b', c', d', e', f', g'⟩
  exact ⟨a'.trans a, b'.trans b, c'.trans c, d'.trans d, e'.trans e, f'.trans f, g'.trans g⟩

/-- A successful transfer leaves the concrete nested snapshot stack intact. -/
theorem success_snapshots (s t : State) (sender recipient : Address) (amount : Word)
    (h : moveEther s sender recipient amount = .ok t) : t.snapshots = s.snapshots := by
  obtain ⟨_, _, ht⟩ := (success_iff s t sender recipient amount).mp h
  subst t
  exact (TransactionAccount.modifyState_snapshots _ _ _).trans
    (TransactionAccount.modifyState_snapshots _ _ _)

/-- A successful nested transfer can be rolled back without losing tracked reads. -/
theorem nested_rollback (s t : State) (sender recipient : Address) (amount : Word)
    (h : moveEther (TransactionState.snapshot (TransactionState.snapshot s)) sender recipient amount = .ok t) :
    ∃ result, TransactionState.rollback t = .ok result ∧
      (observe result).writes = (observe s).writes ∧
      (observe result).stack = (observe (TransactionState.snapshot s)).stack ∧
      (observe result).accountReads = (observe t).accountReads ∧
      (observe result).storageReads = (observe t).storageReads ∧
      (observe result).created = (observe t).created ∧
      (observe result).parentAccounts = (observe t).parentAccounts ∧
      (observe result).parentStorage = (observe t).parentStorage ∧
      (observe result).parentCode = (observe t).parentCode := by
  have hs := success_snapshots _ _ _ _ _ h
  change t.snapshots = s.writes :: s.writes :: s.snapshots at hs
  exact TransactionAccount.rollback_nested_stack s t hs

/-- An in-range self-transfer cannot overflow after its sender debit. -/
theorem self_credit_in_range (s : State) (address : Address) (amount : Word)
    (hfund : amount.toNat ≤ (selectedAccount (observe s) address).balance.toNat) :
    let balance := (selectedAccount (observe s) address).balance
    let debit := TransactionAccount.setAccountBalance s address
      (BitVec.ofNat 256 (balance.toNat - amount.toNat))
    (selectedAccount (observe debit) address).balance.toNat + amount.toNat < Word.modulus := by
  dsimp only
  let balance := (selectedAccount (observe s) address).balance
  let debit := TransactionAccount.setAccountBalance s address
    (BitVec.ofNat 256 (balance.toNat - amount.toNat))
  have hd := congrArg (fun account : World.Account => account.balance.toNat)
    (modify_selected (observe s) (observe debit) address _
      (TransactionAccount.setAccountBalance_refines s address
        (BitVec.ofNat 256 (balance.toNat - amount.toNat))))
  dsimp only at hd
  rw [debit_exact] at hd
  rw [hd, Nat.sub_add_cancel hfund]
  exact balance.isLt

/-- A self-transfer succeeds exactly when the sender has enough funds. -/
theorem self_success_iff (s : State) (address : Address) (amount : Word) :
    (∃ t, moveEther s address address amount = .ok t) ↔
      amount.toNat ≤ (selectedAccount (observe s) address).balance.toNat := by
  constructor
  · rintro ⟨t, h⟩
    have hs := (success_iff s t address address amount).mp h
    simpa only [selectedAccount_eq] using hs.1
  · intro hfund
    let balance := (selectedAccount (observe s) address).balance
    let debit := TransactionAccount.setAccountBalance s address
      (BitVec.ofNat 256 (balance.toNat - amount.toNat))
    let credit := (selectedAccount (observe debit) address).balance
    refine ⟨TransactionAccount.setAccountBalance debit address
      (BitVec.ofNat 256 (credit.toNat + amount.toNat)), ?_⟩
    apply (success_iff _ _ _ _ _).mpr
    refine ⟨?_, ?_, ?_⟩
    · simpa only [selectedAccount_eq] using hfund
    · simpa only [selectedAccount_eq] using self_credit_in_range s address amount hfund
    · simp only [credit, debit, balance, selectedAccount_eq]

/-- A successful transfer preserves storage, clears and reads at other addresses. -/
theorem success_other_storage (before after : View) (sender recipient : Address)
    (amount : Word) (p : Slot) (h : SuccessSpec before after sender recipient amount)
    (hs : p.1 ≠ sender) (hr : p.1 ≠ recipient) :
    after.writes.storage p = before.writes.storage p ∧
    (after.writes.clears p.1 ↔ before.writes.clears p.1) ∧
    (after.storageReads p ↔ before.storageReads p) := by
  obtain ⟨_, debit, hdebit, _, hcredit⟩ := h
  have hs1 := hdebit.2.1 p
  have hs2 := hcredit.2.1 p
  have hc1 := hdebit.2.2.1 p.1
  have hc2 := hcredit.2.2.1 p.1
  have hr1 := hdebit.2.2.2.1 p
  have hr2 := hcredit.2.2.2.1 p
  simp [hs] at hs1 hc1 hr1
  simp [hr] at hs2 hc2 hr2
  exact ⟨hs2.trans hs1, hc2.trans hc1, hr2.trans hr1⟩

/-- Both source account modifications contribute their reads on success. -/
theorem success_accountReads (before after : View) (sender recipient : Address)
    (amount : Word) (b : Address) (h : SuccessSpec before after sender recipient amount) :
    after.accountReads b ↔ b = recipient ∨ b = sender ∨ before.accountReads b := by
  obtain ⟨_, debit, hdebit, _, hcredit⟩ := h
  have h1 := hdebit.2.2.2.2.1 b
  have h2 := hcredit.2.2.2.2.1 b
  rw [h2, h1]

/-- Either failure retains the concrete nested snapshot stack. -/
theorem error_snapshots (s t : State) (sender recipient : Address) (amount : Word)
    (error : TransferError) (h : moveEther s sender recipient amount = .error (error, t)) :
    t.snapshots = s.snapshots := by
  cases error with
  | insufficientBalance =>
    have ht := ((insufficient_iff s t sender recipient amount).mp h).2
    subst t
    rfl
  | recipientOverflow =>
    have ht := ((overflow_iff s t sender recipient amount).mp h).2.2
    subst t
    exact TransactionAccount.modifyState_snapshots _ _ _

/-- A failed nested transfer can be rolled back while retaining its recorded reads. -/
theorem nested_error_rollback (s t : State) (sender recipient : Address) (amount : Word)
    (error : TransferError)
    (h : moveEther (TransactionState.snapshot (TransactionState.snapshot s)) sender recipient amount =
      .error (error, t)) :
    ∃ result, TransactionState.rollback t = .ok result ∧
      (observe result).writes = (observe s).writes ∧
      (observe result).stack = (observe (TransactionState.snapshot s)).stack ∧
      (observe result).accountReads = (observe t).accountReads ∧
      (observe result).storageReads = (observe t).storageReads ∧
      (observe result).created = (observe t).created ∧
      (observe result).parentAccounts = (observe t).parentAccounts ∧
      (observe result).parentStorage = (observe t).parentStorage ∧
      (observe result).parentCode = (observe t).parentCode := by
  have hs := error_snapshots _ _ _ _ _ _ h
  change t.snapshots = s.writes :: s.writes :: s.snapshots at hs
  exact TransactionAccount.rollback_nested_stack s t hs

end EthLib.EVM.TransactionTransfer
