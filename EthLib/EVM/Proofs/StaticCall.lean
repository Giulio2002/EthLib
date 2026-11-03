module

public import EthLib.EVM.StaticCall
public import EthLib.EVM.Proofs.CallPreparation

/-!
# STATICCALL preparation proofs

Every preparation result is characterized by independent field equations.
The code selection and designator predicates are shared with CALL, because both opcodes read the callee code the same way.
The gas, grant and tracker equations are specific to STATICCALL.
-/

@[expose] public section
namespace EthLib.EVM.StaticCall

open CallPreparation (SelectedCode Designator AccessDiagnostic)

private theorem account_reread (t : TransactionState.State) (a : World.Address) :
    (TransactionTracker.getAccount (TransactionTracker.getAccount t a).2 a).1 =
      (TransactionTracker.getAccount t a).1 := by
  simp [TransactionTracker.getAccount, TransactionTracker.getAccountOptional]

private theorem code_after_read (t : TransactionState.State) (a : World.Address) (hash : Word) :
    TransactionAccount.getCode (TransactionTracker.getAccount t a).2 hash =
      TransactionAccount.getCode t hash := by
  simp [TransactionTracker.getAccount, TransactionTracker.getAccountOptional,
    TransactionAccount.getCode]

/-- Execution gas forwarded to the child: the request, capped at all but one 64th of what is left. -/
def Forwarded (s : Frame.State) (r : Frame.CallRequest) : Nat :=
  min r.gas.toNat ((s.gas - initialCost s r) - (s.gas - initialCost s r) / 64)

/-- Under the initial check the source grant is the forwarded gas plus the access charge.

The unaffordable branch of `calculate_message_call_gas` is not taken.
-/
theorem grant_eq (s : Frame.State) (r : Frame.CallRequest) (hg : initialCost s r ≤ s.gas) :
    Gas.Call.calculate 0 r.gas.toNat s.gas
      (Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat)
      (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) 2300 =
      ⟨Forwarded s r + (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000),
        Forwarded s r⟩ := by
  unfold initialCost at hg
  unfold Gas.Call.calculate Gas.Call.cap Forwarded initialCost
  have hn : ¬ s.gas < (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
      Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat :=
    Nat.not_lt.mpr hg
  simp only [hn, ↓reduceIte, Nat.sub_sub, Nat.add_comm (Gas.pairCost _ _ _ _ _), Nat.add_zero]

/-- The source's second gas charge never fails after the initial check. -/
theorem charge_affordable (s : Frame.State) (r : Frame.CallRequest) (hg : initialCost s r ≤ s.gas) :
    (Gas.Call.calculate 0 r.gas.toNat s.gas
      (Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat)
      (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) 2300).cost +
      Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat ≤ s.gas := by
  rw [grant_eq s r hg]
  have hf : Forwarded s r ≤ s.gas - initialCost s r := by
    unfold Forwarded; omega
  unfold initialCost at hg hf
  simp only
  omega

/-- An unaffordable initial cost fails before any state access, with the frame unchanged. -/
theorem initial_gas_failure (s : Frame.State) (r : Frame.CallRequest) (hg : s.gas < initialCost s r) :
    prepare s r = .outOfGas s := by
  unfold initialCost at hg
  unfold prepare
  simp only [hg, ↓reduceIte]

/-- After the initial check the result is determined by the selected code. -/
private theorem prepare_affordable (s : Frame.State) (r : Frame.CallRequest) (hg : initialCost s r ≤ s.gas) :
    prepare s r =
      match TransactionAccount.getCode s.tracker
          (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).1.codeHash with
      | none => .tooling { s with
          warmAddresses := if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses
            else Frame.balanceAddress r.address :: s.warmAddresses,
          tracker := (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).2 } .missingCode
      | some code =>
        if CallPreparation.isDelegation code then .tooling { s with
          warmAddresses := if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses
            else Frame.balanceAddress r.address :: s.warmAddresses,
          tracker := (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).2 } .delegation
        else prepare s r := by
  have hn : ¬ s.gas < (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
      Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat :=
    Nat.not_lt.mpr hg
  cases hc : TransactionAccount.getCode s.tracker
      (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).1.codeHash with
  | none =>
    unfold prepare
    simp only [hn, ↓reduceIte, code_after_read, hc]
  | some code =>
    by_cases hd : CallPreparation.isDelegation code = true
    · simp only [hd, ↓reduceIte]
      unfold prepare
      simp only [hn, ↓reduceIte, code_after_read, hc, hd]
    · simp only [hd, Bool.false_eq_true, ↓reduceIte]

/-- The initial gas diagnostic is the only gas failure, and it returns the input frame. -/
theorem outOfGas_iff (s d : Frame.State) (r : Frame.CallRequest) :
    prepare s r = .outOfGas d ↔ s.gas < initialCost s r ∧ d = s := by
  constructor
  · intro h
    by_cases hg : s.gas < initialCost s r
    · rw [initial_gas_failure s r hg] at h
      cases h
      exact ⟨hg, rfl⟩
    · have hle := Nat.le_of_not_gt hg
      have hcharge := Nat.not_lt.mpr (charge_affordable s r hle)
      have hn : ¬ s.gas < (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
          Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat :=
        Nat.not_lt.mpr hle
      unfold prepare at h
      simp only [hn, ↓reduceIte, code_after_read, account_reread] at h
      split at h
      · contradiction
      · split at h
        · contradiction
        · simp at h
  · rintro ⟨hg, hd⟩
    rw [hd]
    exact initial_gas_failure s r hg

/-- Missing callee code stops at the access diagnostic of the first read. -/
def MissingSpec (s : Frame.State) (r : Frame.CallRequest) (d : Frame.State) : Prop :=
  let hash := (TransactionAccount.selectedAccount (TransactionState.Reference.observe s.tracker)
    (Frame.balanceAddress r.address)).codeHash
  initialCost s r ≤ s.gas ∧ hash ≠ World.emptyCodeHash ∧
    (TransactionState.Reference.observe s.tracker).writes.code hash = none ∧
    (TransactionState.Reference.observe s.tracker).parentCode hash = none ∧ AccessDiagnostic s r d

/-- A delegation designator stops at the same access diagnostic. -/
def DelegationSpec (s : Frame.State) (r : Frame.CallRequest) (d : Frame.State) : Prop :=
  initialCost s r ≤ s.gas ∧ ∃ code, SelectedCode s r code ∧ Designator code ∧ AccessDiagnostic s r d

private theorem access_diagnostic (s : Frame.State) (r : Frame.CallRequest) (d : Frame.State) :
    { s with
      warmAddresses := if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses
        else Frame.balanceAddress r.address :: s.warmAddresses,
      tracker := (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).2 } = d ↔
    AccessDiagnostic s r d := by
  simp [AccessDiagnostic, TransactionTracker.getAccount, TransactionTracker.getAccountOptional, eq_comm]

theorem missingCode_iff (s d : Frame.State) (r : Frame.CallRequest) :
    prepare s r = .tooling d .missingCode ↔ MissingSpec s r d := by
  by_cases hg : s.gas < initialCost s r
  · rw [initial_gas_failure s r hg]
    simp only [MissingSpec, reduceCtorEq, false_iff, not_and]
    intro hle
    omega
  · have hle := Nat.le_of_not_gt hg
    rw [prepare_affordable s r hle]
    cases hc : TransactionAccount.getCode s.tracker
        (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).1.codeHash with
    | none =>
      have miss := (TransactionAccount.getCode_none_iff s.tracker _).mp hc
      rw [← TransactionAccount.selectedAccount_eq] at miss
      simp only [CallPreparation.Result.tooling.injEq, and_true, MissingSpec]
      rw [access_diagnostic]
      exact ⟨fun h => ⟨hle, miss.1, miss.2.1, miss.2.2, h⟩, fun h => h.2.2.2.2⟩
    | some code =>
      have hsel := (CallPreparation.code_reference s r code).mp hc
      have hnot : ¬ MissingSpec s r d := by
        rintro ⟨_, hh, hw, hp, _⟩
        unfold SelectedCode at hsel
        simp_all
      simp only [hnot, iff_false]
      split
      · simp
      · rename_i hd
        intro h
        have hn : ¬ s.gas < (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
            Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat :=
          Nat.not_lt.mpr hle
        unfold prepare at h
        simp only [hn, ↓reduceIte, code_after_read, account_reread, hc, hd, Bool.false_eq_true] at h
        -- Every remaining branch is a different constructor.
        repeat' (first | contradiction | split at h)

theorem delegation_iff (s d : Frame.State) (r : Frame.CallRequest) :
    prepare s r = .tooling d .delegation ↔ DelegationSpec s r d := by
  have hdes (code : ByteArray) : CallPreparation.isDelegation code = true ↔ Designator code := by
    simp [CallPreparation.isDelegation, Designator]
  by_cases hg : s.gas < initialCost s r
  · rw [initial_gas_failure s r hg]
    simp only [DelegationSpec, reduceCtorEq, false_iff, not_and]
    intro hle
    omega
  · have hle := Nat.le_of_not_gt hg
    cases hc : TransactionAccount.getCode s.tracker
        (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).1.codeHash with
    | none =>
      rw [prepare_affordable s r hle, hc]
      simp only [CallPreparation.Result.tooling.injEq, reduceCtorEq, and_false, false_iff, DelegationSpec, not_and,
        not_exists]
      intro _ code hsel
      have := (CallPreparation.code_reference s r code).mpr hsel
      rw [hc] at this
      contradiction
    | some code =>
      have hsel := (CallPreparation.code_reference s r code).mp hc
      have hunique (other : ByteArray) (ho : SelectedCode s r other) : other = code := by
        have := (CallPreparation.code_reference s r other).mpr ho
        rw [hc] at this
        exact (Option.some.inj this).symm
      by_cases hd : CallPreparation.isDelegation code = true
      · rw [prepare_affordable s r hle, hc]
        simp only [hd, ↓reduceIte, CallPreparation.Result.tooling.injEq, and_true]
        rw [access_diagnostic]
        constructor
        · intro h
          exact ⟨hle, code, hsel, (hdes code).mp hd, h⟩
        · rintro ⟨_, other, ho, _, h⟩
          exact h
      · have hnot : ¬ DelegationSpec s r d := by
          rintro ⟨_, other, ho, hdo, _⟩
          rw [hunique other ho] at hdo
          exact hd ((hdes code).mpr hdo)
        simp only [hnot, iff_false]
        intro h
        have h' := h
        rw [prepare_affordable s r hle, hc] at h'
        simp only [hd, Bool.false_eq_true, ↓reduceIte] at h'
        unfold prepare at h
        have hn : ¬ s.gas < (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
            Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat :=
          Nat.not_lt.mpr hle
        have hcharge := Nat.not_lt.mpr (charge_affordable s r hle)
        simp only [hn, ↓reduceIte, code_after_read, account_reread, hc, hd, Bool.false_eq_true, hcharge] at h
        contradiction

/-- The compatibility constructor is never produced by STATICCALL preparation. -/
theorem valueTransfer_unreachable (s d : Frame.State) (r : Frame.CallRequest) :
    prepare s r ≠ .tooling d .valueTransfer := by
  intro h
  by_cases hg : s.gas < initialCost s r
  · rw [initial_gas_failure s r hg] at h
    contradiction
  · have hle := Nat.le_of_not_gt hg
    have hn : ¬ s.gas < (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
        Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat :=
      Nat.not_lt.mpr hle
    have hcharge := Nat.not_lt.mpr (charge_affordable s r hle)
    unfold prepare at h
    simp only [hn, ↓reduceIte, code_after_read, account_reread, hcharge] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · contradiction

/-- The independent full-field ready relation.

The parent records two reads of the callee account and no sender read.
The child receives the forwarded gas without a stipend and the whole state-gas reservoir.
-/
def ReadySpec (s : Frame.State) (r : Frame.CallRequest) (p : CallPreparation.Prepared) : Prop :=
  initialCost s r ≤ s.gas ∧ SelectedCode s r p.code ∧ ¬ Designator p.code ∧
    p.request = r ∧ p.address = Frame.balanceAddress r.address ∧
    p.childGas = Forwarded s r ∧ p.stateGrant = s.stateGas.reservoir ∧
    p.newAccountCharged = false ∧ p.insufficientBalance = false ∧
    p.parent.code = s.code ∧ p.parent.pc = s.pc ∧ p.parent.stack = s.stack ∧
    p.parent.gas = s.gas - initialCost s r - Forwarded s r ∧
    p.parent.memory.store = s.memory.store ∧
    p.parent.memory.words = max (max s.memory.words (Memory.Allocation.requiredWords r.inputOffset.toNat r.inputSize.toNat))
      (Memory.Allocation.requiredWords r.outputOffset.toNat r.outputSize.toNat) ∧
    p.parent.context = s.context ∧ p.parent.returnData = ByteArray.empty ∧
    p.parent.tracker = { s.tracker with
      accountReads := Frame.balanceAddress r.address :: Frame.balanceAddress r.address :: s.tracker.accountReads } ∧
    p.parent.warmAddresses = (if s.warmAddresses.contains (Frame.balanceAddress r.address) then s.warmAddresses
      else Frame.balanceAddress r.address :: s.warmAddresses) ∧
    p.parent.warmSlots = s.warmSlots ∧ p.parent.isStatic = s.isStatic ∧
    p.parent.stateGas = { s.stateGas with reservoir := 0 } ∧ p.parent.logs = s.logs

theorem ready_refines (s : Frame.State) (r : Frame.CallRequest) (p : CallPreparation.Prepared)
    (h : prepare s r = .ready p) : ReadySpec s r p := by
  by_cases hg : s.gas < initialCost s r
  · rw [initial_gas_failure s r hg] at h
    contradiction
  have hle := Nat.le_of_not_gt hg
  have hn : ¬ s.gas < (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
      Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat :=
    Nat.not_lt.mpr hle
  have hcharge := Nat.not_lt.mpr (charge_affordable s r hle)
  cases hc : TransactionAccount.getCode s.tracker
      (TransactionTracker.getAccount s.tracker (Frame.balanceAddress r.address)).1.codeHash with
  | none =>
    unfold prepare at h
    simp only [hn, ↓reduceIte, code_after_read, hc] at h
    contradiction
  | some code =>
    have hsel := (CallPreparation.code_reference s r code).mp hc
    unfold prepare at h
    simp only [hn, ↓reduceIte, code_after_read, account_reread, hc, hcharge] at h
    split at h
    · contradiction
    next hd =>
      have hnd : ¬ Designator code := by
        intro hd'
        have ht : CallPreparation.isDelegation code = true := by
          simpa [CallPreparation.isDelegation, Designator] using hd'
        contradiction
      simp only [CallPreparation.Result.ready.injEq] at h
      subst p
      have hgrant := grant_eq s r hle
      have hf : Forwarded s r ≤ s.gas - initialCost s r := by unfold Forwarded; omega
      refine ⟨hle, hsel, hnd, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
      · simp only [hgrant]
      · simp only [hgrant]
        unfold initialCost at hf ⊢
        omega
      · simp [Memory.Allocation.expand, TransactionTracker.getAccount, TransactionTracker.getAccountOptional]

/-- The independent ready observations determine the entire preparation. -/
theorem readySpec_unique (s : Frame.State) (r : Frame.CallRequest) (p q : CallPreparation.Prepared)
    (hp : ReadySpec s r p) (hq : ReadySpec s r q) : p = q := by
  have hcode : p.code = q.code := by
    have h1 := (CallPreparation.code_reference s r p.code).mpr hp.2.1
    have h2 := (CallPreparation.code_reference s r q.code).mpr hq.2.1
    rw [h1] at h2
    exact Option.some.inj h2
  obtain ⟨_, _, _, pr, pa, pg, psg, pn, pb, pcode, ppc, pst, pgas, pstore, pwords, pctx, pdata, ptr, pwa, pws,
    pstatic, pstate, plogs⟩ := hp
  obtain ⟨_, _, _, qr, qa, qg, qsg, qn, qb, qcode, qpc, qst, qgas, qstore, qwords, qctx, qdata, qtr, qwa, qws,
    qstatic, qstate, qlogs⟩ := hq
  cases p with
  | mk ps pr' pa' pc pg' psg' pn' pb' =>
    cases q with
    | mk qs qr' qa' qc qg' qsg' qn' qb' =>
      cases ps with
      | mk pcode' ppc' pst' pgas' pmem pvalid pctx' pdata' ptracker pwa' pws' pstatic' pstate' plogs' =>
        cases qs with
        | mk qcode' qpc' qst' qgas' qmem qvalid qctx' qdata' qtracker qwa' qws' qstatic' qstate' qlogs' =>
          cases pmem
          cases qmem
          simp_all

theorem ready_complete (s : Frame.State) (r : Frame.CallRequest) (p : CallPreparation.Prepared)
    (spec : ReadySpec s r p) : prepare s r = .ready p := by
  cases h : prepare s r with
  | ready q => rw [readySpec_unique s r q p (ready_refines s r q h) spec]
  | outOfGas d =>
    have := (outOfGas_iff s d r).mp h
    have := spec.1
    omega
  | tooling d reason =>
    cases reason with
    | valueTransfer => exact False.elim (valueTransfer_unreachable s d r h)
    | missingCode =>
      obtain ⟨_, hhash, hwrite, hparent, _⟩ := (missingCode_iff s d r).mp h
      have hc := spec.2.1
      unfold SelectedCode at hc
      simp [hhash, hwrite, hparent] at hc
    | delegation =>
      obtain ⟨_, code, hc, hd, _⟩ := (delegation_iff s d r).mp h
      have h1 := (CallPreparation.code_reference s r code).mpr hc
      have h2 := (CallPreparation.code_reference s r p.code).mpr spec.2.1
      rw [h1] at h2
      have heq : code = p.code := Option.some.inj h2
      subst heq
      exact False.elim (spec.2.2.1 hd)

theorem ready_iff (s : Frame.State) (r : Frame.CallRequest) (p : CallPreparation.Prepared) :
    prepare s r = .ready p ↔ ReadySpec s r p :=
  ⟨ready_refines s r p, ready_complete s r p⟩

/-- Independent conditions for every preparation result. -/
def OutcomeSpec (s : Frame.State) (r : Frame.CallRequest) : CallPreparation.Result → Prop
  | .outOfGas d => s.gas < initialCost s r ∧ d = s
  | .tooling d .missingCode => MissingSpec s r d
  | .tooling d .delegation => DelegationSpec s r d
  | .tooling _ .valueTransfer => False
  | .ready p => ReadySpec s r p

theorem prepare_iff (s : Frame.State) (r : Frame.CallRequest) (result : CallPreparation.Result) :
    prepare s r = result ↔ OutcomeSpec s r result := by
  cases result with
  | ready p => exact ready_iff s r p
  | outOfGas d => exact outOfGas_iff s d r
  | tooling d reason =>
    cases reason with
    | valueTransfer => simp [OutcomeSpec, valueTransfer_unreachable]
    | missingCode => exact missingCode_iff s d r
    | delegation => exact delegation_iff s d r

/-- A ready STATICCALL never reports a balance or new-account flag. -/
theorem ready_flags (s : Frame.State) (r : Frame.CallRequest) (p : CallPreparation.Prepared)
    (h : prepare s r = .ready p) : p.newAccountCharged = false ∧ p.insufficientBalance = false :=
  have spec := ready_refines s r p h
  ⟨spec.2.2.2.2.2.2.2.1, spec.2.2.2.2.2.2.2.2.1⟩

end EthLib.EVM.StaticCall
