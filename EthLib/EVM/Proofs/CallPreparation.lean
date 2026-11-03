module

public import EthLib.EVM.CallPreparation
public import EthLib.EVM.Proofs.TransactionAccount
public import EthLib.EVM.Proofs.Gas.StateMeter

@[expose] public section
namespace EthLib.EVM.CallPreparation

/-- Insufficient state-independent execution gas fails before any state access. -/
theorem initial_gas_failure (s : Frame.State) (r : Frame.CallRequest)
    (hgas : s.gas < (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
      (if r.value == 0 then 0 else 11300) +
      Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat) :
    prepare s r = .outOfGas s := by
  unfold prepare
  simp only [hgas, ↓reduceIte]

/-- The unchanged gas diagnostic occurs exactly at the initial gas check. -/
theorem initial_failure_iff (s : Frame.State) (r : Frame.CallRequest) :
    prepare s r = .outOfGas s ↔
    s.gas < (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
      (if r.value == 0 then 0 else 11300) +
      Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat := by
  constructor
  · intro h
    by_cases hgas : s.gas < (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
      (if r.value == 0 then 0 else 11300) +
      Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat
    · exact hgas
    unfold prepare at h
    simp only [hgas, ↓reduceIte] at h
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h <;> try contradiction
    rename_i e he
    simp only [Result.outOfGas.injEq] at h
    have hh := congrArg Frame.State.gas h
    simp only at hh
    have hcost : 0 < (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
      (if r.value == 0 then 0 else 11300) +
      Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat := by
      split <;> omega
    omega
  · exact initial_gas_failure s r
/-- Missing first-read code produces the access diagnostic from independent maps. -/
theorem first_missing_forward (s : Frame.State) (r : Frame.CallRequest)
    (hgas : (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
      (if r.value == 0 then 0 else 11300) +
      Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat ≤ s.gas)
    (hhash : (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
      (Frame.balanceAddress r.address)).codeHash ≠ World.emptyCodeHash)
    (hwrite : (TransactionState.Reference.observe s.tracker).writes.code
      (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
      (Frame.balanceAddress r.address)).codeHash = none)
    (hparent : (TransactionState.Reference.observe s.tracker).parentCode
      (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
      (Frame.balanceAddress r.address)).codeHash = none) :
    prepare s r = .tooling { s with
      warmAddresses := if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses
        else Frame.balanceAddress r.address :: s.warmAddresses,
      tracker := { s.tracker with accountReads := Frame.balanceAddress r.address :: s.tracker.accountReads } } .missingCode := by
  let address := Frame.balanceAddress r.address
  let read := TransactionTracker.getAccount s.tracker address
  have hsel : (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker) address) = read.1 :=
    TransactionAccount.selectedAccount_eq _ _
  change (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker) address).codeHash ≠ World.emptyCodeHash at hhash
  change (TransactionState.Reference.observe s.tracker).writes.code (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker) address).codeHash = none at hwrite
  change (TransactionState.Reference.observe s.tracker).parentCode (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker) address).codeHash = none at hparent
  rw [hsel] at hhash hwrite hparent
  have hc : TransactionAccount.getCode read.2 read.1.codeHash = none := by
    apply (TransactionAccount.getCode_none_iff _ _).mpr
    refine ⟨?_, ?_, ?_⟩
    · exact hhash
    · simpa [read, TransactionTracker.getAccount, TransactionTracker.getAccountOptional,
        TransactionState.Reference.observe, TransactionState.Reference.observeWrites] using hwrite
    · simpa [read, TransactionTracker.getAccount, TransactionTracker.getAccountOptional,
        TransactionState.Reference.observe] using hparent
  unfold prepare
  simp only [Nat.not_lt.mpr hgas, ↓reduceIte]
  rw [hc]
  rfl
/-- Repeated account reads leave the selected account unchanged. -/
private theorem account_reread (t : TransactionState.State) (a : World.Address) :
    (TransactionTracker.getAccount (TransactionTracker.getAccount t a).2 a).1 =
      (TransactionTracker.getAccount t a).1 := by
  simp [TransactionTracker.getAccount, TransactionTracker.getAccountOptional]

private theorem code_after_read (t : TransactionState.State) (a : World.Address) (hash : Word) :
    TransactionAccount.getCode (TransactionTracker.getAccount t a).2 hash =
      TransactionAccount.getCode t hash := by
  simp [TransactionTracker.getAccount, TransactionTracker.getAccountOptional,
    TransactionAccount.getCode]

theorem missingCode_converse (s d : Frame.State) (r : Frame.CallRequest)
    (h : prepare s r = .tooling d .missingCode) :
    (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
      (if r.value == 0 then 0 else 11300) +
      Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat ≤ s.gas ∧
    (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
      (Frame.balanceAddress r.address)).codeHash ≠ World.emptyCodeHash ∧
    (TransactionState.Reference.observe s.tracker).writes.code
      (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
      (Frame.balanceAddress r.address)).codeHash = none ∧
    (TransactionState.Reference.observe s.tracker).parentCode
      (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
      (Frame.balanceAddress r.address)).codeHash = none ∧
    d = { s with warmAddresses := if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses
        else Frame.balanceAddress r.address :: s.warmAddresses, tracker := { s.tracker with accountReads := Frame.balanceAddress r.address :: s.tracker.accountReads } } := by
  by_cases hg : s.gas < (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
      (if r.value == 0 then 0 else 11300) +
      Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat
  · rw [initial_gas_failure s r hg] at h
    contradiction
  · cases hc : TransactionAccount.getCode s.tracker
        (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).1.codeHash with
    | none =>
      have miss := (TransactionAccount.getCode_none_iff s.tracker _).mp hc
      rw [← TransactionAccount.selectedAccount_eq] at miss
      have forward := first_missing_forward s r (Nat.le_of_not_gt hg) miss.1 miss.2.1 miss.2.2
      rw [forward] at h
      simp only [Result.tooling.injEq] at h
      exact ⟨Nat.le_of_not_gt hg, miss.1, miss.2.1, miss.2.2, h.1.symm⟩
    | some code =>
      unfold prepare at h
      simp only [hg, ↓reduceIte, account_reread, code_after_read, hc] at h
      split at h
      · simp at h
      · split at h <;> contradiction
/-- The independent code overlay and parent selection cases. -/
def SelectedCode (s : Frame.State) (r : Frame.CallRequest) (code : ByteArray) : Prop :=
  let h := (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
    (Frame.balanceAddress r.address)).codeHash
  (h = World.emptyCodeHash ∧ code = ByteArray.empty) ∨
    (h ≠ World.emptyCodeHash ∧
      ((TransactionState.Reference.observe s.tracker).writes.code h = some code ∨
        ((TransactionState.Reference.observe s.tracker).writes.code h = none ∧
          (TransactionState.Reference.observe s.tracker).parentCode h = some code)))

def Designator (code : ByteArray) : Prop :=
  code.size = 23 ∧ code.data.toList.take 3 = [0xef, 0x01, 0x00]

theorem code_reference (s : Frame.State) (r : Frame.CallRequest) (code : ByteArray) :
    TransactionAccount.getCode s.tracker
      (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).1.codeHash = some code ↔
    SelectedCode s r code := by
  rw [← TransactionAccount.selectedAccount_eq]
  exact TransactionAccount.getCode_some_iff _ _ _

theorem delegation_iff (s d : Frame.State) (r : Frame.CallRequest) :
    prepare s r = .tooling d .delegation ↔
    ((if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
      (if r.value == 0 then 0 else 11300) +
      Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat ≤ s.gas ∧
    ∃ code, SelectedCode s r code ∧ Designator code ∧
      d = { s with warmAddresses := if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses
        else Frame.balanceAddress r.address :: s.warmAddresses, tracker := { s.tracker with accountReads := Frame.balanceAddress r.address :: s.tracker.accountReads } }) := by
  have hd (code : ByteArray) : isDelegation code = true ↔ Designator code := by
    simp [isDelegation, Designator]
  constructor
  · intro h
    by_cases hg : s.gas < (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
      (if r.value == 0 then 0 else 11300) +
      Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat
    · rw [initial_gas_failure s r hg] at h
      contradiction
    · cases hc : TransactionAccount.getCode s.tracker
          (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).1.codeHash with
      | none =>
        unfold prepare at h
        simp only [hg, ↓reduceIte, code_after_read, hc] at h
        simp at h
      | some code =>
        unfold prepare at h
        simp only [hg, ↓reduceIte, account_reread, code_after_read, hc] at h
        split at h
        next ht =>
          simp only [Result.tooling.injEq] at h
          refine ⟨Nat.le_of_not_gt hg, code, (code_reference s r code).mp hc, (hd code).mp ht, ?_⟩
          simpa [TransactionTracker.getAccount, TransactionTracker.getAccountOptional] using h.1.symm
        next ht =>
          split at h <;> contradiction
  · rintro ⟨hg, code, hc, ht, rfl⟩
    have hc := (code_reference s r code).mpr hc
    have ht := (hd code).mpr ht
    unfold prepare
    simp only [Nat.not_lt.mpr hg, ↓reduceIte, code_after_read, hc, ht]
    rfl
/-- Missing code has exactly the first account-read diagnostic and map conditions. -/
theorem missingCode_iff (s d : Frame.State) (r : Frame.CallRequest)
    : prepare s r = .tooling d .missingCode ↔
    (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
      (if r.value == 0 then 0 else 11300) +
      Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat ≤ s.gas ∧
    (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
      (Frame.balanceAddress r.address)).codeHash ≠ World.emptyCodeHash ∧
    (TransactionState.Reference.observe s.tracker).writes.code
      (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
      (Frame.balanceAddress r.address)).codeHash = none ∧
    (TransactionState.Reference.observe s.tracker).parentCode
      (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
      (Frame.balanceAddress r.address)).codeHash = none ∧
    d = { s with warmAddresses := if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses
        else Frame.balanceAddress r.address :: s.warmAddresses, tracker := { s.tracker with accountReads := Frame.balanceAddress r.address :: s.tracker.accountReads } } := by
  constructor
  · exact missingCode_converse s d r
  · rintro ⟨hg, hh, hw, hp, hd⟩
    rw [hd]
    exact first_missing_forward s r hg hh hw hp

/-- The account overlay observation before any reads. -/
def ReferenceAccount (s : Frame.State) (a : World.Address) : Option World.Account :=
  ((TransactionState.Reference.observe s.tracker).writes.accounts a).getD
    ((TransactionState.Reference.observe s.tracker).parentAccounts a)

def NewAccount (s : Frame.State) (r : Frame.CallRequest) : Prop :=
  r.value ≠ 0 ∧ (ReferenceAccount s (Frame.balanceAddress r.address) = none ∨
    ReferenceAccount s (Frame.balanceAddress r.address) = some World.emptyAccount)

theorem reference_optional (s : Frame.State) (a : World.Address) :
    ReferenceAccount s a = (TransactionTracker.getAccountOptional s.tracker a).1 := by
  unfold ReferenceAccount TransactionState.Reference.observe TransactionState.Reference.observeWrites
    TransactionTracker.getAccountOptional World.getAccountOptional
  cases h : s.tracker.writes.accountWrites.lookup a <;> simp [h]

theorem optional_after_reads (s : Frame.State) (a : World.Address) :
    (TransactionTracker.getAccountOptional
      (TransactionTracker.getAccount (TransactionTracker.getAccount s.tracker a).2 a).2 a).1 =
      ReferenceAccount s a := by
  rw [reference_optional]
  simp [TransactionTracker.getAccount, TransactionTracker.getAccountOptional]


def Cost (s : Frame.State) (r : Frame.CallRequest) : Nat :=
  (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
  (if r.value == 0 then 0 else 11300) +
  Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat

theorem state_gas_failure_forward (s : Frame.State) (r : Frame.CallRequest) (code : ByteArray)
    (hg : Cost s r ≤ s.gas) (hc : SelectedCode s r code) (hd : ¬ Designator code)
    (hn : NewAccount s r) (hf : s.stateGas.reservoir + (s.gas - Cost s r) < 183600) :
    prepare s r = .outOfGas { s with gas := s.gas - Cost s r, warmAddresses := if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses else Frame.balanceAddress r.address :: s.warmAddresses, tracker := { s.tracker with accountReads := Frame.balanceAddress r.address :: Frame.balanceAddress r.address :: Frame.balanceAddress r.address :: s.tracker.accountReads } } := by
  have hv : (r.value != 0) = true := by
    simp only [bne_iff_ne]
    exact hn.1
  have hcode := (code_reference s r code).mpr hc
  have hdeleg : isDelegation code = false := by
    simp [isDelegation, Designator] at hd ⊢
    exact hd
  unfold Cost at hg hf ⊢
  unfold prepare
  simp only [Nat.not_lt.mpr hg, ↓reduceIte, code_after_read, account_reread, hcode, hdeleg,
    Bool.false_eq_true, hv]
  rw [optional_after_reads]
  rcases hn.2 with ha | ha <;>
    simp [ha, Gas.StateMeter.chargeState, Frame.stateMeter, Frame.withStateMeter,
      TransactionTracker.getAccount, TransactionTracker.getAccountOptional] at hg hf ⊢
  all_goals
    have hres : s.stateGas.reservoir < 183600 := by omega
    simp [Nat.not_le_of_gt hres, Nat.not_le_of_gt hf]
/-- A later gas error determines the charged account and diagnostic. -/
theorem later_failure_converse (s d : Frame.State) (r : Frame.CallRequest)
    (hg : Cost s r ≤ s.gas) (h : prepare s r = .outOfGas d) :
    ∃ code, SelectedCode s r code ∧ ¬ Designator code ∧ NewAccount s r ∧
      s.stateGas.reservoir + (s.gas - Cost s r) < 183600 ∧
      d = { s with gas := s.gas - Cost s r, warmAddresses := if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses else Frame.balanceAddress r.address :: s.warmAddresses, tracker := { s.tracker with accountReads := Frame.balanceAddress r.address :: Frame.balanceAddress r.address :: Frame.balanceAddress r.address :: s.tracker.accountReads } } := by
  unfold Cost at hg
  cases hc : TransactionAccount.getCode s.tracker
      (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).1.codeHash with
  | none =>
    unfold prepare at h
    simp only [Nat.not_lt.mpr hg, ↓reduceIte, code_after_read, hc] at h
    contradiction
  | some code =>
    have hs := (code_reference s r code).mp hc
    unfold prepare at h
    simp only [Nat.not_lt.mpr hg, ↓reduceIte, code_after_read, account_reread, hc] at h
    split at h
    · contradiction
    next hdel =>
      have hd : ¬ Designator code := by
        intro hi
        have : isDelegation code = true := by simpa [isDelegation, Designator] using hi
        simp_all
      by_cases hv : r.value = 0
      · simp [hv] at h
      · have hvb : (r.value != 0) = true := by simpa using hv
        simp only [hvb, ↓reduceIte, optional_after_reads] at h
        cases ha : ReferenceAccount s (Frame.balanceAddress r.address) with
        | none =>
          simp only [ha, Bool.and_true, ↓reduceIte] at h
          split at h
          next err herr =>
            cases err
            have hf := (Gas.StateMeter.chargeState_error_iff _ 183600).mp herr
            simp only [Frame.stateMeter] at hf
            simp only [Result.outOfGas.injEq] at h
            refine ⟨code, hs, hd, ⟨hv, Or.inl ha⟩, ?_, ?_⟩
            · simpa [Cost] using hf
            · simpa [Cost, TransactionTracker.getAccount, TransactionTracker.getAccountOptional] using h.symm
          · contradiction
        | some account =>
          by_cases he : account = World.emptyAccount
          · subst account
            simp only [ha, beq_self_eq_true, Bool.and_true, ↓reduceIte] at h
            split at h
            next err herr =>
              cases err
              have hf := (Gas.StateMeter.chargeState_error_iff _ 183600).mp herr
              simp only [Frame.stateMeter] at hf
              simp only [Result.outOfGas.injEq] at h
              refine ⟨code, hs, hd, ⟨hv, Or.inr ha⟩, ?_, ?_⟩
              · simpa [Cost] using hf
              · simpa [Cost, TransactionTracker.getAccount, TransactionTracker.getAccountOptional] using h.symm
            · contradiction
          · have heb : (account == World.emptyAccount) = false := beq_eq_false_iff_ne.mpr he
            simp [ha, heb] at h
/-- Under initial affordability the later gas diagnostic is exact. -/
theorem later_failure_iff (s d : Frame.State) (r : Frame.CallRequest)
    (hg : Cost s r ≤ s.gas) : prepare s r = .outOfGas d ↔
    ∃ code, SelectedCode s r code ∧ ¬ Designator code ∧ NewAccount s r ∧
      s.stateGas.reservoir + (s.gas - Cost s r) < 183600 ∧
      d = { s with gas := s.gas - Cost s r, warmAddresses := if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses else Frame.balanceAddress r.address :: s.warmAddresses, tracker := { s.tracker with accountReads := Frame.balanceAddress r.address :: Frame.balanceAddress r.address :: Frame.balanceAddress r.address :: s.tracker.accountReads } } := by
  constructor
  · exact later_failure_converse s d r hg
  · rintro ⟨code, hc, hd, hn, hf, hframe⟩
    rw [hframe]
    exact state_gas_failure_forward s r code hg hc hd hn hf

/-- The compatibility constructor is never produced by preparation. -/
theorem valueTransfer_unreachable (s d : Frame.State) (r : Frame.CallRequest) :
    prepare s r ≠ .tooling d .valueTransfer := by
  intro h
  by_cases hg : Cost s r ≤ s.gas
  · cases hc : TransactionAccount.getCode s.tracker
        (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).1.codeHash with
    | none =>
      unfold Cost at hg
      unfold prepare at h
      simp only [Nat.not_lt.mpr hg, ↓reduceIte] at h
      have hc' : TransactionAccount.getCode (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).2
          (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).1.codeHash = none := by
        simpa [TransactionTracker.getAccount, TransactionTracker.getAccountOptional, TransactionAccount.getCode] using hc
      rw [hc'] at h
      simp at h
    | some code =>
      have hc' : TransactionAccount.getCode (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).2
          (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).1.codeHash = some code := by
        simpa [TransactionTracker.getAccount, TransactionTracker.getAccountOptional, TransactionAccount.getCode] using hc
      have hc'' : TransactionAccount.getCode
          (TransactionTracker.getAccount (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).2 (Frame.balanceAddress r.address)).2
          (TransactionTracker.getAccount (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).2 (Frame.balanceAddress r.address)).1.codeHash = some code := by
        simpa [TransactionTracker.getAccount, TransactionTracker.getAccountOptional, TransactionAccount.getCode] using hc
      unfold Cost at hg
      unfold prepare at h
      simp only [Nat.not_lt.mpr hg, ↓reduceIte, hc', hc''] at h
      split at h
      · simp at h
      · split at h <;> contradiction
  · have hh : s.gas < Cost s r := Nat.lt_of_not_ge hg
    unfold Cost at hh
    rw [initial_gas_failure s r hh] at h
    contradiction
/-- A ready request has affordable execution gas and selected nondelegated code. -/
theorem ready_conditions (s : Frame.State) (r : Frame.CallRequest) (p : Prepared)
    (h : prepare s r = .ready p) :
    Cost s r ≤ s.gas ∧ SelectedCode s r p.code ∧ ¬ Designator p.code := by
  by_cases hg : Cost s r ≤ s.gas
  · cases hc : TransactionAccount.getCode s.tracker
      (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).1.codeHash with
    | none =>
      unfold Cost at hg
      unfold prepare at h
      simp only [Nat.not_lt.mpr hg, ↓reduceIte, code_after_read, hc] at h
      contradiction
    | some code =>
      have hs := (code_reference s r code).mp hc
      have hg' := hg
      unfold Cost at hg'
      unfold prepare at h
      simp only [Nat.not_lt.mpr hg', ↓reduceIte, code_after_read, account_reread, hc] at h
      split at h
      · contradiction
      next hd =>
        have hnd : ¬ Designator code := by
          intro hd'
          have ht : isDelegation code = true := by simpa [isDelegation, Designator] using hd'
          contradiction
        split at h
        · contradiction
        next meter hm =>
          simp only [Result.ready.injEq] at h
          have heq := congrArg Prepared.code h
          simp only at heq
          rw [← heq]
          exact ⟨hg, hs, hnd⟩
  · have hh : s.gas < Cost s r := Nat.lt_of_not_ge hg
    unfold Cost at hh
    rw [initial_gas_failure s r hh] at h
    contradiction
/-- Ready preparation retains frame context, tracker metadata and sparse bytes. -/
theorem ready_retained (s : Frame.State) (r : Frame.CallRequest) (p : Prepared)
    (h : prepare s r = .ready p) :
    p.parent.code = s.code ∧ p.parent.pc = s.pc ∧ p.parent.stack = s.stack ∧
    p.parent.memory.store = s.memory.store ∧
    p.parent.memory.words = max (max s.memory.words (Memory.Allocation.requiredWords r.inputOffset.toNat r.inputSize.toNat))
      (Memory.Allocation.requiredWords r.outputOffset.toNat r.outputSize.toNat) ∧
    p.parent.context = s.context ∧ p.parent.returnData = ByteArray.empty ∧
    p.parent.tracker.parent = s.tracker.parent ∧ p.parent.tracker.writes = s.tracker.writes ∧
    p.parent.tracker.storageReads = s.tracker.storageReads ∧
    p.parent.tracker.createdAccounts = s.tracker.createdAccounts ∧
    p.parent.tracker.snapshots = s.tracker.snapshots ∧ p.parent.warmSlots = s.warmSlots ∧
    p.parent.isStatic = s.isStatic ∧ p.parent.logs = s.logs ∧ p.request = r := by
  by_cases hg : Cost s r ≤ s.gas
  · cases hc : TransactionAccount.getCode s.tracker
      (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).1.codeHash with
    | none =>
      unfold Cost at hg
      unfold prepare at h
      simp only [Nat.not_lt.mpr hg, ↓reduceIte, code_after_read, hc] at h
      contradiction
    | some code =>
      have hg' := hg
      unfold Cost at hg'
      unfold prepare at h
      simp only [Nat.not_lt.mpr hg', ↓reduceIte, code_after_read, account_reread, hc] at h
      split at h
      · contradiction
      next hd =>
        split at h
        · contradiction
        next meter hm =>
          simp only [Result.ready.injEq] at h
          subst p
          simp [Frame.withStateMeter, Memory.Allocation.expand, TransactionTracker.getAccount,
            TransactionTracker.getAccountOptional]
          split <;> simp
  · have hh : s.gas < Cost s r := Nat.lt_of_not_ge hg
    unfold Cost at hh
    rw [initial_gas_failure s r hh] at h
    contradiction
/-- The mathematical new-account flag selects the reference account map. -/
def ReferenceNewFlag (s : Frame.State) (r : Frame.CallRequest) : Bool :=
  r.value != 0 && match ReferenceAccount s (Frame.balanceAddress r.address) with
    | none => true
    | some account => account == World.emptyAccount

theorem referenceNewFlag_iff (s : Frame.State) (r : Frame.CallRequest) :
    ReferenceNewFlag s r = true ↔ NewAccount s r := by
  unfold ReferenceNewFlag NewAccount
  cases ReferenceAccount s (Frame.balanceAddress r.address) <;> simp [bne_iff_ne]

def InitialMeter (s : Frame.State) (r : Frame.CallRequest) : Gas.StateMeter.Meter :=
  ⟨s.gas - Cost s r, s.stateGas.reservoir, s.stateGas.baseline,
    s.stateGas.refundCounter, s.stateGas.spilled, s.stateGas.committedSpill⟩

def MeterEffect (s : Frame.State) (r : Frame.CallRequest) (meter : Gas.StateMeter.Meter) : Prop :=
  (NewAccount s r ∧ Gas.StateMeter.ChargeEffect (InitialMeter s r) meter 183600) ∨
    (¬ NewAccount s r ∧ meter = InitialMeter s r)

theorem meter_effect_iff (s : Frame.State) (r : Frame.CallRequest) (meter : Gas.StateMeter.Meter) :
    (if ReferenceNewFlag s r then Gas.StateMeter.chargeState (InitialMeter s r) 183600
      else .ok (InitialMeter s r)) = .ok meter ↔ MeterEffect s r meter := by
  by_cases hn : NewAccount s r
  · have hb := (referenceNewFlag_iff s r).mpr hn
    simp [hb, MeterEffect, hn, Gas.StateMeter.chargeState_ok_iff]
  · have hb : ReferenceNewFlag s r = false := by
      cases he : ReferenceNewFlag s r <;> simp_all [referenceNewFlag_iff]
    simp [hb, MeterEffect, hn, eq_comm]
private theorem source_new_flag (s : Frame.State) (r : Frame.CallRequest) :
    (r.value != 0 && match (if r.value != 0 then
      TransactionTracker.getAccountOptional
        (TransactionTracker.getAccount (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).2
          (Frame.balanceAddress r.address)).2 (Frame.balanceAddress r.address)
      else (none, (TransactionTracker.getAccount (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).2
        (Frame.balanceAddress r.address)).2)).1 with
      | none => true
      | some account => account == World.emptyAccount) = ReferenceNewFlag s r := by
  by_cases h : r.value = 0
  · simp [ReferenceNewFlag, h]
  · have hb : (r.value != 0) = true := by simpa using h
    simp only [hb, ↓reduceIte, Bool.true_and, optional_after_reads, ReferenceNewFlag]
/-- The independent full-field ready relation, including grants and tracker reads. -/
def ReadySpec (s : Frame.State) (r : Frame.CallRequest) (p : Prepared) : Prop :=
  ∃ code : ByteArray, ∃ meter : Gas.StateMeter.Meter, ∃ forwarded : Nat,
    Cost s r ≤ s.gas ∧ SelectedCode s r code ∧ ¬ Designator code ∧
    ((NewAccount s r ∧ Gas.StateMeter.ChargeEffect (InitialMeter s r) meter 183600) ∨
      (¬ NewAccount s r ∧ meter = InitialMeter s r)) ∧
    forwarded = min r.gas.toNat (meter.executionGas - meter.executionGas / 64) ∧
    p.request = r ∧ p.address = Frame.balanceAddress r.address ∧ p.code = code ∧
    p.childGas = forwarded + (if r.value.toNat = 0 then 0 else 2300) ∧
    p.stateGrant = meter.stateGas ∧ (p.newAccountCharged = true ↔ NewAccount s r) ∧
    (p.insufficientBalance = true ↔
      (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
        s.context.environment.currentTarget).balance.toNat < r.value.toNat) ∧
    p.parent.code = s.code ∧ p.parent.pc = s.pc ∧ p.parent.stack = s.stack ∧
    p.parent.gas = meter.executionGas - forwarded ∧
    p.parent.memory.store = s.memory.store ∧
    p.parent.memory.words = max (max s.memory.words (Memory.Allocation.requiredWords r.inputOffset.toNat r.inputSize.toNat))
      (Memory.Allocation.requiredWords r.outputOffset.toNat r.outputSize.toNat) ∧
    p.parent.context = s.context ∧ p.parent.returnData = ByteArray.empty ∧
    p.parent.tracker = { s.tracker with accountReads := s.context.environment.currentTarget ::
      (if r.value = 0 then [Frame.balanceAddress r.address, Frame.balanceAddress r.address] ++ s.tracker.accountReads
      else [Frame.balanceAddress r.address, Frame.balanceAddress r.address, Frame.balanceAddress r.address] ++ s.tracker.accountReads) } ∧
    p.parent.warmAddresses = (if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses
      else Frame.balanceAddress r.address :: s.warmAddresses) ∧
    p.parent.warmSlots = s.warmSlots ∧ p.parent.isStatic = s.isStatic ∧
    p.parent.stateGas = ⟨0, meter.baseline, meter.refundCounter, meter.spilled, meter.committedSpill⟩ ∧
    p.parent.logs = s.logs

theorem ready_refines (s : Frame.State) (r : Frame.CallRequest) (p : Prepared)
    (h : prepare s r = .ready p) : ReadySpec s r p := by
  have hg := (ready_conditions s r p h).1
  cases hc : TransactionAccount.getCode s.tracker
      (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).1.codeHash with
  | none =>
    unfold Cost at hg
    unfold prepare at h
    simp only [Nat.not_lt.mpr hg, ↓reduceIte, code_after_read, hc] at h
    contradiction
  | some code =>
    have hs := (code_reference s r code).mp hc
    have hg' := hg
    unfold Cost at hg'
    unfold prepare at h
    simp only [Nat.not_lt.mpr hg', ↓reduceIte, code_after_read, account_reread, hc] at h
    split at h
    · contradiction
    next hd =>
      have hnd : ¬ Designator code := by
        intro hd'
        have ht : isDelegation code = true := by simpa [isDelegation, Designator] using hd'
        contradiction
      split at h
      · contradiction
      next meter hm =>
        simp only [Result.ready.injEq] at h
        have hm' : (if ReferenceNewFlag s r then Gas.StateMeter.chargeState (InitialMeter s r) 183600
          else .ok (InitialMeter s r)) = .ok meter := by
          by_cases hv : r.value = 0
          · simpa [ReferenceNewFlag, hv, Frame.stateMeter, InitialMeter, Cost] using hm
          · have hb : (r.value != 0) = true := by simpa using hv
            simp only [hb, ↓reduceIte, optional_after_reads] at hm
            have hz : r.value ≠ 0#256 := by simpa using hv
            cases ha : ReferenceAccount s (Frame.balanceAddress r.address) <;>
              simpa [ReferenceNewFlag, hb, hv, hz, Frame.stateMeter, InitialMeter, Cost, ha] using hm
        have heffect := (meter_effect_iff s r meter).mp hm'
        subst p
        unfold ReadySpec
        refine ⟨code, meter, min r.gas.toNat (meter.executionGas - meter.executionGas / 64), hg, hs, hnd, heffect, rfl, ?_⟩
        simp [Frame.withStateMeter, Memory.Allocation.expand, Gas.Call.calculate, Gas.Call.cap,
          TransactionTracker.getAccount, TransactionTracker.getAccountOptional,
          NewAccount, ReferenceAccount, TransactionState.Reference.observe,
          TransactionState.Reference.observeWrites, TransactionAccount.selectedAccount,
          World.getAccountOptional]
        by_cases hv : r.value = 0#256 <;> simp [hv] at *
        all_goals
          cases htarget : s.tracker.writes.accountWrites.lookup (Frame.balanceAddress r.address) <;>
            cases hsender : s.tracker.writes.accountWrites.lookup s.context.environment.currentTarget <;>
            simp_all
        all_goals split <;> simp_all
        all_goals
          first
          | exact Or.inl (by assumption)
          | intro hn
            have hn' : s.tracker.parent.accounts.lookup (Frame.balanceAddress r.address) = none := by simpa using hn
            simp_all
/-- The independent ready observations determine the entire result. -/
theorem readySpec_unique (s : Frame.State) (r : Frame.CallRequest) (p q : Prepared)
    (hp : ReadySpec s r p) (hq : ReadySpec s r q) : p = q := by
  obtain ⟨c, m, f, hg, hc, hd, hm, hf, hp⟩ := hp
  obtain ⟨c', m', f', hg', hc', hd', hm', hf', hq⟩ := hq
  have heq : c = c' := by
    have h1 := (code_reference s r c).mpr hc
    have h2 := (code_reference s r c').mpr hc'
    rw [h1] at h2
    exact Option.some.inj h2
  subst c'
  have heq : m = m' := by
    have h1 := (meter_effect_iff s r m).mpr hm
    have h2 := (meter_effect_iff s r m').mpr hm'
    rw [h1] at h2
    exact Except.ok.inj h2
  subst m'
  have heq : f = f' := hf.trans hf'.symm
  subst f'
  have hn : p.newAccountCharged = q.newAccountCharged := by
    have h1 := hp.2.2.2.2.2.1
    have h2 := hq.2.2.2.2.2.1
    cases hpa : p.newAccountCharged <;> cases hqa : q.newAccountCharged <;> simp_all
  have hb : p.insufficientBalance = q.insufficientBalance := by
    have h1 := hp.2.2.2.2.2.2.1
    have h2 := hq.2.2.2.2.2.2.1
    cases hpa : p.insufficientBalance <;> cases hqa : q.insufficientBalance <;> simp_all
  cases p with
  | mk ps pr pa pc pg psg pn pb =>
    cases q with
    | mk qs qr qa qc qg qsg qn qb =>
      cases ps with
      | mk pcode ppc pst pgas pmem pvalid pctx pdata ptracker pwa pws pstatic pstate plogs =>
        cases qs with
        | mk qcode qpc qst qgas qmem qvalid qctx qdata qtracker qwa qws qstatic qstate qlogs =>
          cases pmem
          cases qmem
          simp_all
/-- The independent ready relation determines the executable result. -/
theorem ready_complete (s : Frame.State) (r : Frame.CallRequest) (p : Prepared)
    (spec : ReadySpec s r p) : prepare s r = .ready p := by
  obtain ⟨code, meter, forwarded, hg, hc, hd, hm, rest⟩ := spec
  have spec : ReadySpec s r p := ⟨code, meter, forwarded, hg, hc, hd, hm, rest⟩
  cases h : prepare s r with
  | ready q =>
    have hq := ready_refines s r q h
    have heq := readySpec_unique s r q p hq spec
    simp [heq] at h ⊢
  | outOfGas d =>
    have ⟨other, hother, hothernd, hn, hf, hfstate⟩ := later_failure_converse s d r hg h
    rcases hm with ⟨_, hm⟩ | ⟨hm, _⟩
    · have hok := (Gas.StateMeter.chargeState_ok_iff (InitialMeter s r) meter 183600).mpr hm
      have herr : Gas.StateMeter.chargeState (InitialMeter s r) 183600 = .error .outOfGas :=
        (Gas.StateMeter.chargeState_error_iff (InitialMeter s r) 183600).mpr (by simpa [InitialMeter] using hf)
      rw [hok] at herr
      contradiction
    · exact False.elim (hm hn)
  | tooling d reason =>
    cases reason with
    | valueTransfer => exact False.elim (valueTransfer_unreachable s d r h)
    | missingCode =>
      have ⟨_, hhash, hwrite, hparent, _⟩ := missingCode_converse s d r h
      unfold SelectedCode at hc
      simp [hhash, hwrite, hparent] at hc
    | delegation =>
      have ⟨_, code', hc', hd', _⟩ := (delegation_iff s d r).mp h
      have h1 := (code_reference s r code).mpr hc
      have h2 := (code_reference s r code').mpr hc'
      rw [h1] at h2
      have heq : code = code' := Option.some.inj h2
      subst code'
      exact False.elim (hd hd')
/-- Ready results are exactly the independent full-field relation. -/
theorem ready_iff (s : Frame.State) (r : Frame.CallRequest) (p : Prepared) :
    prepare s r = .ready p ↔ ReadySpec s r p :=
  ⟨ready_refines s r p, ready_complete s r p⟩

/-- Independent outcome conditions, ordered by the initial gas check. -/
def AccessDiagnostic (s : Frame.State) (r : Frame.CallRequest) (d : Frame.State) : Prop :=
  d = { s with warmAddresses := if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses else Frame.balanceAddress r.address :: s.warmAddresses, tracker := { s.tracker with accountReads := Frame.balanceAddress r.address :: s.tracker.accountReads } }

def MissingSpec (s : Frame.State) (r : Frame.CallRequest) (d : Frame.State) : Prop :=
  let hash := (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
    (Frame.balanceAddress r.address)).codeHash
  Cost s r ≤ s.gas ∧ hash ≠ World.emptyCodeHash ∧
    (TransactionState.Reference.observe s.tracker).writes.code hash = none ∧
    (TransactionState.Reference.observe s.tracker).parentCode hash = none ∧ AccessDiagnostic s r d

def DelegationSpec (s : Frame.State) (r : Frame.CallRequest) (d : Frame.State) : Prop :=
  Cost s r ≤ s.gas ∧ ∃ code, SelectedCode s r code ∧ Designator code ∧ AccessDiagnostic s r d

def LaterGasSpec (s : Frame.State) (r : Frame.CallRequest) (d : Frame.State) : Prop :=
  Cost s r ≤ s.gas ∧ ∃ code, SelectedCode s r code ∧ ¬ Designator code ∧ NewAccount s r ∧
    s.stateGas.reservoir + (s.gas - Cost s r) < 183600 ∧
    d = { s with gas := s.gas - Cost s r, warmAddresses := if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses else Frame.balanceAddress r.address :: s.warmAddresses, tracker := { s.tracker with accountReads := Frame.balanceAddress r.address :: Frame.balanceAddress r.address :: Frame.balanceAddress r.address :: s.tracker.accountReads } }

def OutcomeSpec (s : Frame.State) (r : Frame.CallRequest) : Result → Prop
  | .outOfGas d => (s.gas < Cost s r ∧ d = s) ∨ LaterGasSpec s r d
  | .tooling d .missingCode => MissingSpec s r d
  | .tooling d .delegation => DelegationSpec s r d
  | .tooling _ .valueTransfer => False
  | .ready p => ReadySpec s r p

theorem prepare_iff (s : Frame.State) (r : Frame.CallRequest) (result : Result) :
    prepare s r = result ↔ OutcomeSpec s r result := by
  cases result with
  | ready p => exact ready_iff s r p
  | tooling d reason =>
    cases reason with
    | valueTransfer => simp [OutcomeSpec, valueTransfer_unreachable]
    | missingCode => simpa [OutcomeSpec, MissingSpec, AccessDiagnostic, Cost] using missingCode_iff s d r
    | delegation => simpa [OutcomeSpec, DelegationSpec, AccessDiagnostic, Cost] using delegation_iff s d r
  | outOfGas d =>
    by_cases hg : Cost s r ≤ s.gas
    · simpa [OutcomeSpec, LaterGasSpec, Nat.not_lt_of_ge hg, hg] using later_failure_iff s d r hg
    · have hh : s.gas < Cost s r := Nat.lt_of_not_ge hg
      have hh' := hh
      unfold Cost at hh'
      rw [initial_gas_failure s r hh']
      simp [OutcomeSpec, LaterGasSpec, hh, hg, eq_comm]
end EthLib.EVM.CallPreparation
