module

public import EthLib.EVM.Proofs.Frame
public import EthLib.EVM.Proofs.TransactionTracker
import Aesop

/-!
# SELFBALANCE

Amsterdam `vm/instructions/environment.py`, `self_balance`, charges five gas,
records the current target account read, then pushes the balance.
-/

@[expose] public section
namespace EthLib.EVM.Frame

/-- Insufficient gas fails before the tracker is read. -/
theorem selfBalance_gas (s : State) (gas : s.gas < 5) :
    selfBalance s = .exception s .outOfGas := by
  simp [selfBalance, charge, Gas.charge, Nat.not_le_of_gt gas]

/-- A full stack fails after the target account has been read. -/
theorem selfBalance_full (s : State) (gas : 5 ≤ s.gas)
    (full : s.stack.val.length = 1024) :
    selfBalance s = .exception { s with tracker := SelfBalanceRead s } .stackOverflow := by
  have push : s.stack.push (SelfBalanceAccount s).balance = .error .overflow :=
    (Proofs.Stack.push_overflow_iff _ _).mpr full
  have value : (TransactionTracker.getAccount s.tracker s.context.environment.currentTarget).1 =
      SelfBalanceAccount s := rfl
  have read : (TransactionTracker.getAccount s.tracker s.context.environment.currentTarget).2 =
      SelfBalanceRead s := rfl
  simp only [selfBalance, charge, Gas.charge, ite_eq_left gas, value, read, push, failStack]

/-- The success rule fixes every frame field and the exact read. -/
theorem selfBalance_success (s t : State) (gas : 5 ≤ s.gas)
    (room : s.stack.val.length < 1024)
    (fields : Advances { s with tracker := SelfBalanceRead s } t (s.pc + 1) (s.gas - 5)
      ((SelfBalanceAccount s).balance :: s.stack.val)) :
    selfBalance s = .continue t := by
  let stack : Stack := ⟨(SelfBalanceAccount s).balance :: s.stack.val, by simp; omega⟩
  have push : s.stack.push (SelfBalanceAccount s).balance = .ok stack :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨room, rfl⟩
  have eq := advances_eq { s with tracker := SelfBalanceRead s } t (s.pc + 1)
    (s.gas - 5) stack fields
  subst t
  have value : (TransactionTracker.getAccount s.tracker s.context.environment.currentTarget).1 =
      SelfBalanceAccount s := rfl
  have read : (TransactionTracker.getAccount s.tracker s.context.environment.currentTarget).2 =
      SelfBalanceRead s := rfl
  simp only [selfBalance, charge, Gas.charge, ite_eq_left gas, value, read, push]

/-- Success is equivalent to the gas, capacity and full-field conditions. -/
theorem selfBalance_success_iff (s t : State) :
    selfBalance s = .continue t ↔
      5 ≤ s.gas ∧ s.stack.val.length < 1024 ∧
      Advances { s with tracker := SelfBalanceRead s } t (s.pc + 1) (s.gas - 5)
        ((SelfBalanceAccount s).balance :: s.stack.val) := by
  constructor
  · intro run
    by_cases gas : 5 ≤ s.gas
    · by_cases room : s.stack.val.length < 1024
      · let stack : Stack := ⟨(SelfBalanceAccount s).balance :: s.stack.val, by simp; omega⟩
        let target : State := { s with tracker := SelfBalanceRead s, stack, pc := s.pc + 1, gas := s.gas - 5 }
        have fields : Advances { s with tracker := SelfBalanceRead s } target
            (s.pc + 1) (s.gas - 5) ((SelfBalanceAccount s).balance :: s.stack.val) := by
          simp [Advances, target, stack]
        have eq := selfBalance_success s target gas room fields
        rw [run] at eq
        have eqTarget : t = target := Outcome.continue.inj eq
        subst t
        exact ⟨gas, room, fields⟩
      · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
        have bad := selfBalance_full s gas full
        rw [run] at bad
        cases bad
    · have bad := selfBalance_gas s (Nat.lt_of_not_ge gas)
      rw [run] at bad
      cases bad
  · rintro ⟨gas, room, fields⟩
    exact selfBalance_success s t gas room fields

/-- Every exceptional result has exactly the source check and diagnostic state. -/
theorem selfBalance_exception_iff (s input : State) (reason : Exception) :
    selfBalance s = .exception input reason ↔
      (s.gas < 5 ∧ input = s ∧ reason = .outOfGas) ∨
      (5 ≤ s.gas ∧ s.stack.val.length = 1024 ∧
        input = { s with tracker := SelfBalanceRead s } ∧ reason = .stackOverflow) := by
  by_cases gas : 5 ≤ s.gas
  · by_cases room : s.stack.val.length < 1024
    · let stack : Stack := ⟨(SelfBalanceAccount s).balance :: s.stack.val, by simp; omega⟩
      let target : State := { s with tracker := SelfBalanceRead s, stack, pc := s.pc + 1, gas := s.gas - 5 }
      have fields : Advances { s with tracker := SelfBalanceRead s } target
          (s.pc + 1) (s.gas - 5) ((SelfBalanceAccount s).balance :: s.stack.val) := by
        simp [Advances, target, stack]
      rw [selfBalance_success s target gas room fields]
      simp [Nat.not_lt_of_ge gas, Nat.ne_of_lt room]
    · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
      rw [selfBalance_full s gas full]
      simp [Nat.not_lt_of_ge gas, gas, full, eq_comm]
  · have low : s.gas < 5 := Nat.lt_of_not_ge gas
    rw [selfBalance_gas s low]
    simp [low, gas, eq_comm]

/-- Every rule retains the immutable parent, created markers, and snapshot stack. -/
theorem outcome_tracker_metadata_retained {s : State} {out : Outcome} (rule : Rule s out) :
    out.frame.tracker.parent = s.tracker.parent ∧
    out.frame.tracker.createdAccounts = s.tracker.createdAccounts ∧
    out.frame.tracker.snapshots = s.tracker.snapshots := by
  cases rule <;> simp_all [Outcome.frame, Advances, AdvancesMemory, SelfBalanceRead, BalanceRead, SloadRead,
    SstoreReady, SstoreReadFields, SstoreCreditFields, SstoreExecutionFields, SstoreChargeFields,
    SstoreMeterRetained, SstoreWriteFields, TransientWriteFields] <;> aesop

/-- Every rule retains the static-context flag. -/
theorem outcome_static_retained {s : State} {out : Outcome} (rule : Rule s out) :
    out.frame.isStatic = s.isStatic := by
  cases rule <;> simp_all [Outcome.frame, Advances, AdvancesMemory, SstoreReady, SstoreReadFields,
    SstoreCreditFields, SstoreExecutionFields, SstoreChargeFields, SstoreMeterRetained, SstoreWriteFields] <;> aesop

/-- State-gas bookkeeping is unchanged when the current instruction is not SSTORE. -/
theorem outcome_stateGas_unchanged_of_not_sstore {s : State} {out : Outcome}
    (notSstore : ¬ At s (some .sstore)) (rule : Rule s out) :
    out.frame.stateGas = s.stateGas := by
  cases rule <;> simp_all [Outcome.frame, Advances, AdvancesMemory]

/-- Every rule except SSTORE retains all persistent write components. -/
theorem outcome_persistent_writes_unchanged_of_not_sstore {s : State} {out : Outcome}
    (notSstore : ¬ At s (some .sstore)) (rule : Rule s out) :
    out.frame.tracker.writes.accountWrites = s.tracker.writes.accountWrites ∧
    out.frame.tracker.writes.storageWrites = s.tracker.writes.storageWrites ∧
    out.frame.tracker.writes.codeWrites = s.tracker.writes.codeWrites ∧
    out.frame.tracker.writes.storageClears = s.tracker.writes.storageClears := by
  cases rule <;> simp_all [Outcome.frame, Advances, AdvancesMemory, SelfBalanceRead,
    BalanceRead, SloadRead, TransientWriteFields]

/-- Every step except SSTORE retains all persistent write components. -/
theorem step_persistent_writes_unchanged_of_not_sstore (s : State)
    (notSstore : ¬ At s (some .sstore)) :
    (step s).frame.tracker.writes.accountWrites = s.tracker.writes.accountWrites ∧
    (step s).frame.tracker.writes.storageWrites = s.tracker.writes.storageWrites ∧
    (step s).frame.tracker.writes.codeWrites = s.tracker.writes.codeWrites ∧
    (step s).frame.tracker.writes.storageClears = s.tracker.writes.storageClears :=
  outcome_persistent_writes_unchanged_of_not_sstore notSstore ((step_iff_rule s _).mp rfl)

/-- Rules other than SSTORE and TSTORE preserve the tracker parent, writes, created accounts and snapshots. -/
theorem outcome_tracker_retained {s : State} {out : Outcome}
    (notSstore : ¬ At s (some .sstore)) (notTstore : ¬ At s (some .tstore)) (rule : Rule s out) :
    out.frame.tracker.parent = s.tracker.parent ∧
    out.frame.tracker.writes = s.tracker.writes ∧
    out.frame.tracker.createdAccounts = s.tracker.createdAccounts ∧
    out.frame.tracker.snapshots = s.tracker.snapshots := by
  cases rule <;> simp_all [Outcome.frame, Advances, AdvancesMemory, SelfBalanceRead, BalanceRead, SloadRead]

/-- Rules other than SSTORE and TSTORE preserve the tracker or record one account or storage read. -/
theorem outcome_tracker_read {s : State} {out : Outcome}
    (notSstore : ¬ At s (some .sstore)) (notTstore : ¬ At s (some .tstore)) (rule : Rule s out) :
    out.frame.tracker = s.tracker ∨ (∃ a, out.frame.tracker = BalanceRead s a) ∨ ∃ key, out.frame.tracker = SloadRead s key := by
  cases rule <;> simp_all [Outcome.frame, Advances, AdvancesMemory, SelfBalanceRead, BalanceRead, SloadRead]

/-- A rule at any other instruction preserves the whole transaction tracker. -/
theorem outcome_tracker_unchanged_of_not_selfBalance {s : State} {out : Outcome}
    (notSelf : ¬ At s (some .selfbalance)) (notBalance : ¬ At s (some .balance)) (notSload : ¬ At s (some .sload))
    (notSstore : ¬ At s (some .sstore)) (notTstore : ¬ At s (some .tstore))
    (notSize : ¬ At s (some .extcodesize)) (notHash : ¬ At s (some .extcodehash)) (rule : Rule s out) :
    out.frame.tracker = s.tracker := by
  cases rule <;> simp_all [Outcome.frame, Advances, AdvancesMemory]

/-- Every rule other than SLOAD and SSTORE preserves the storage-read list. -/
theorem outcome_storageReads_unchanged_of_not_sload {s : State} {out : Outcome}
    (notSload : ¬ At s (some .sload)) (notSstore : ¬ At s (some .sstore)) (rule : Rule s out) :
    out.frame.tracker.storageReads = s.tracker.storageReads := by
  cases rule <;> simp_all [Outcome.frame, Advances, AdvancesMemory, SelfBalanceRead, BalanceRead, TransientWriteFields]

/-- Every step other than SLOAD and SSTORE preserves the storage-read list. -/
theorem step_storageReads_unchanged_of_not_sload (s : State)
    (notSload : ¬ At s (some .sload)) (notSstore : ¬ At s (some .sstore)) :
    (step s).frame.tracker.storageReads = s.tracker.storageReads :=
  outcome_storageReads_unchanged_of_not_sload notSload notSstore ((step_iff_rule s _).mp rfl)

/-- The selected account follows the independent overlay and parent map observations. -/
theorem selfBalance_account_value (s : State) :
    (∀ x, (TransactionState.Reference.observe s.tracker).writes.accounts
      s.context.environment.currentTarget = some x →
      SelfBalanceAccount s = x.getD World.emptyAccount) ∧
    ((TransactionState.Reference.observe s.tracker).writes.accounts
      s.context.environment.currentTarget = none →
      SelfBalanceAccount s = ((TransactionState.Reference.observe s.tracker).parentAccounts
        s.context.environment.currentTarget).getD World.emptyAccount) := by
  exact TransactionTracker.getAccount_value s.tracker s.context.environment.currentTarget

/-- The dispatcher invokes exactly the same instruction at opcode 0x47. -/
theorem step_selfBalance (s : State) (at_ : At s (some .selfbalance)) :
    step s = selfBalance s := by
  obtain ⟨bounds, decoded⟩ := at_
  simp only [step, dite_eq_left bounds, decoded]

end EthLib.EVM.Frame
