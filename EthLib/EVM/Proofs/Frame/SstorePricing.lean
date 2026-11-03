module

public import EthLib.EVM.Frame.Rules
public import EthLib.EVM.Proofs.Gas.StateMeter
public import EthLib.EVM.Proofs.Stack
import Mathlib.Tactic

/-! Independent state-dependent pricing conditions for Amsterdam `storage.py`, `sstore`. -/

@[expose] public section
namespace EthLib.EVM.Frame

/-- The executable arithmetic satisfies each independent pricing condition. -/
theorem sstore_pricing (original current value : Word) :
    SstorePricing original current value
      (if original == current && current != value then 10000 else 0)
      (if original == current && current != value && original == 0 then 97920 else 0)
      (if current != value && original != 0 && current != 0 && value == 0 then 11616 else 0)
      (if current != value && original != 0 && current == 0 then 11616 else 0)
      (if current != value && original == value then 10000 else 0)
      (current != value && original == value && original == 0) := by
  simp [SstorePricing, and_assoc]

/-- The independent conditions determine every price and refund component. -/
theorem sstore_pricing_unique (original current value : Word)
    (writeCost stateCost : Nat) (clearRefund reverseRefund restoreRefund : Int) (credit : Bool)
    (h : SstorePricing original current value writeCost stateCost clearRefund reverseRefund restoreRefund credit) :
    writeCost = (if original == current && current != value then 10000 else 0) ∧
    stateCost = (if original == current && current != value && original == 0 then 97920 else 0) ∧
    clearRefund = (if current != value && original != 0 && current != 0 && value == 0 then 11616 else 0) ∧
    reverseRefund = (if current != value && original != 0 && current == 0 then 11616 else 0) ∧
    restoreRefund = (if current != value && original == value then 10000 else 0) ∧
    credit = (current != value && original == value && original == 0) := by
  unfold SstorePricing at h
  by_cases oc : original = current <;> by_cases cv : current = value <;>
    by_cases oz : original = 0 <;> by_cases cz : current = 0 <;>
    by_cases vz : value = 0 <;> by_cases ov : original = value <;>
    cases credit <;> simp_all

/-- Warming and reading the slot have the stated full-field effect. -/
theorem sstore_read_fields (s : State) (rest : Stack) (key : Word) :
    SstoreReadFields s
      { s with stack := rest, warmSlots := SloadWarm s key, tracker := (TransactionTracker.getStorage s.tracker s.context.environment.currentTarget key).2 }
      rest key := by
  simp [SstoreReadFields, TransactionTracker.getStorage]

/-- The read observation determines the complete post-read frame. -/
theorem sstore_read_unique (s t : State) (rest : Stack) (key : Word)
    (h : SstoreReadFields s t rest key) :
    t = { s with stack := rest, warmSlots := SloadWarm s key, tracker := SloadRead s key } := by
  rcases h with ⟨code, pc, stack, gas, memory, context, data, addresses, slots, static, meter,
    parent, writes, accounts, reads, created, snapshots⟩
  have tracker : t.tracker = SloadRead s key := by
    cases hs : s.tracker
    cases ht : t.tracker
    simp_all [SloadRead]
  cases s
  cases t
  simp_all

/-- Signed refund adjustment and optional credit refine the meter relation. -/
theorem sstore_credit_fields (s : State) (delta : Int) (credit : Bool) :
    SstoreCreditFields s
      (withStateMeter s (if credit then Gas.StateMeter.creditState
        (Gas.StateMeter.adjustRefund (stateMeter s) delta) 97920
        else Gas.StateMeter.adjustRefund (stateMeter s) delta)) delta credit := by
  cases credit
  · simp [SstoreCreditFields, SstoreMeterRetained, withStateMeter, stateMeter,
      Gas.StateMeter.adjustRefund]
  · by_cases h : 97920 ≤ s.stateGas.spilled
    · simp [SstoreCreditFields, SstoreMeterRetained, withStateMeter, stateMeter,
        Gas.StateMeter.adjustRefund, Gas.StateMeter.creditState, h]
    · have h' : s.stateGas.spilled ≤ 97920 := by omega
      simp [SstoreCreditFields, SstoreMeterRetained, withStateMeter, stateMeter,
        Gas.StateMeter.adjustRefund, Gas.StateMeter.creditState, Nat.min_eq_right h', h]
      omega

/-- The independent credit relation determines the post-credit frame. -/
theorem sstore_credit_unique (s t : State) (delta : Int) (credit : Bool)
    (h : SstoreCreditFields s t delta credit) :
    t = withStateMeter s (if credit then Gas.StateMeter.creditState
      (Gas.StateMeter.adjustRefund (stateMeter s) delta) 97920
      else Gas.StateMeter.adjustRefund (stateMeter s) delta) := by
  rcases s with ⟨code, pc, stack, gas, memory, valid, context, data, tracker, addresses, slots, static, meter⟩
  rcases t with ⟨code', pc', stack', gas', memory', valid', context', data', tracker', addresses', slots', static', meter'⟩
  rcases meter with ⟨reservoir, baseline, refund, spilled, committed⟩
  rcases meter' with ⟨reservoir', baseline', refund', spilled', committed'⟩
  cases credit <;>
    simp [SstoreCreditFields, SstoreMeterRetained, withStateMeter, stateMeter,
      Gas.StateMeter.adjustRefund, Gas.StateMeter.creditState, Nat.min_def] at h ⊢
  all_goals try split_ifs at h ⊢
  all_goals simp_all
  all_goals omega

/-- A successful state-gas charge refines the independent field relation. -/
theorem sstore_charge_fields (s : State) (amount : Nat) (meter : Gas.StateMeter.Meter)
    (run : Gas.StateMeter.chargeState (stateMeter s) amount = .ok meter) :
    SstoreChargeFields s (withStateMeter s meter) amount := by
  have effect := (Gas.StateMeter.chargeState_ok_iff (stateMeter s) meter amount).mp run
  simp [SstoreChargeFields, SstoreMeterRetained, withStateMeter, stateMeter,
    Gas.StateMeter.ChargeEffect, Gas.StateMeter.Retained] at effect ⊢
  tauto

/-- Every independent successful charge comes from the accepted meter operation. -/
theorem sstore_charge_converse (s t : State) (amount : Nat)
    (h : SstoreChargeFields s t amount) :
    ∃ meter, Gas.StateMeter.chargeState (stateMeter s) amount = .ok meter ∧
      t = withStateMeter s meter := by
  have effect : Gas.StateMeter.ChargeEffect (stateMeter s) (stateMeter t) amount := by
    simp [SstoreChargeFields, SstoreMeterRetained, stateMeter,
      Gas.StateMeter.ChargeEffect, Gas.StateMeter.Retained] at h ⊢
    tauto
  refine ⟨stateMeter t, (Gas.StateMeter.chargeState_ok_iff _ _ _).mpr effect, ?_⟩
  rcases h with ⟨retained, _, _⟩
  rcases retained with ⟨code, pc, stack, memory, context, data, tracker, addresses, slots, static, _, _⟩
  cases hm : t.stateGas
  cases s
  cases t
  simp_all [withStateMeter, stateMeter]

/-- The independent execution-gas relation has a unique resulting frame. -/
theorem sstore_execution_unique (s t : State) (cost : Nat)
    (h : SstoreExecutionFields s t cost) :
    t = { s with gas := s.gas - cost } := by
  rcases h with ⟨retained, meter, gas⟩
  rcases retained with ⟨code, pc, stack, memory, context, data, tracker, addresses, slots, static, _, _⟩
  have gas' : t.gas = s.gas - cost := by omega
  cases s
  cases t
  simp_all

/-- A successful execution-gas charge has the independent field effect. -/
theorem sstore_execution_fields (s : State) (cost : Nat) (gas : cost ≤ s.gas) :
    SstoreExecutionFields s { s with gas := s.gas - cost } cost := by
  simp [SstoreExecutionFields, SstoreMeterRetained, Nat.sub_add_cancel gas]

/-- A successful tracker write has the stated complete frame effect. -/
theorem sstore_write_success_fields (s : State) (key value : Word) (tracker : TransactionState.State)
    (run : TransactionTracker.setStorage s.tracker s.context.environment.currentTarget key value = .ok tracker) :
    SstoreWriteFields s { s with tracker, pc := s.pc + 1 } key value true := by
  unfold TransactionTracker.setStorage at run
  cases account : (TransactionTracker.getAccountOptional s.tracker s.context.environment.currentTarget).1 with
  | none => simp [account] at run
  | some a =>
    simp [account] at run
    subst tracker
    simp [SstoreWriteFields, TransactionTracker.getAccountOptional]

/-- The independent account observation equals the tracker lookup result. -/
theorem sstore_account_value (s : State) :
    SstoreAccount s = (TransactionTracker.getAccountOptional s.tracker s.context.environment.currentTarget).1 := by
  rfl

/-- A failed tracker write records the account read and preserves the other fields. -/
theorem sstore_write_error_fields (s : State) (key value : Word) (tracker : TransactionState.State)
    (run : TransactionTracker.setStorage s.tracker s.context.environment.currentTarget key value =
      .error (.missingAccount, tracker)) :
    SstoreWriteFields s { s with tracker } key value false := by
  unfold TransactionTracker.setStorage at run
  cases account : (TransactionTracker.getAccountOptional s.tracker s.context.environment.currentTarget).1 with
  | none =>
    simp [account] at run
    subst tracker
    simp [SstoreWriteFields, TransactionTracker.getAccountOptional]
  | some a => simp [account] at run

/-- A witness used to reconstruct a frame from the write-field relation. -/
def sstoreWriteWitness (s : State) (key value : Word) (success : Bool) : State :=
  let writes := { s.tracker.writes with storageWrites :=
    if success then ((s.context.environment.currentTarget, key), value) :: s.tracker.writes.storageWrites
    else s.tracker.writes.storageWrites }
  let tracker := { s.tracker with writes, accountReads := s.context.environment.currentTarget :: s.tracker.accountReads }
  { s with pc := if success then s.pc + 1 else s.pc, tracker }

/-- The independent storage-write fields determine the complete resulting frame. -/
theorem sstore_write_unique (s t : State) (key value : Word) (success : Bool)
    (h : SstoreWriteFields s t key value success) : t = sstoreWriteWitness s key value success := by
  rcases h with ⟨code, pc, stack, gas, memory, context, data, addresses, slots, static, meter,
    parent, accounts, storage, codes, clears, transient, reads, storageReads, created, snapshots⟩
  have writes : t.tracker.writes = { s.tracker.writes with storageWrites :=
      if success then ((s.context.environment.currentTarget, key), value) :: s.tracker.writes.storageWrites
      else s.tracker.writes.storageWrites } := by
    cases hs : s.tracker.writes
    cases ht : t.tracker.writes
    simp_all
  have tracker : t.tracker = { s.tracker with writes := t.tracker.writes, accountReads := s.context.environment.currentTarget :: s.tracker.accountReads } := by
    cases hs : s.tracker
    cases ht : t.tracker
    simp_all
  cases s
  cases t
  simp_all [sstoreWriteWitness]

/-- An existing effective account produces the write witness. -/
theorem sstore_write_witness_success (s : State) (key value : Word) (present : SstoreAccount s ≠ none) :
    TransactionTracker.setStorage s.tracker s.context.environment.currentTarget key value =
      .ok (sstoreWriteWitness s key value true).tracker := by
  rw [sstore_account_value] at present
  cases account : (TransactionTracker.getAccountOptional s.tracker s.context.environment.currentTarget).1 with
  | none => exact False.elim (present account)
  | some a =>
    simp only [TransactionTracker.setStorage, account]
    simp [sstoreWriteWitness, TransactionTracker.getAccountOptional]

/-- An absent effective account returns the read-only error witness. -/
theorem sstore_write_witness_missing (s : State) (key value : Word) (absent : SstoreAccount s = none) :
    TransactionTracker.setStorage s.tracker s.context.environment.currentTarget key value =
      .error (.missingAccount, (sstoreWriteWitness s key value false).tracker) := by
  rw [sstore_account_value] at absent
  simp only [TransactionTracker.setStorage, absent]
  simp [sstoreWriteWitness, TransactionTracker.getAccountOptional]

/-- The post-read frame used to witness the independent relation. -/
def sstoreReadWitness (s : State) (rest : Stack) (key : Word) : State :=
  { s with stack := rest, warmSlots := SloadWarm s key, tracker := SloadRead s key }

/-- The conditional write charge from the Amsterdam pricing rule. -/
def sstoreWriteCost (original current value : Word) : Nat :=
  if original == current && current != value then 10000 else 0

/-- The conditional state charge from the Amsterdam pricing rule. -/
def sstoreStateCost (original current value : Word) : Nat :=
  if original == current && current != value && original == 0 then 97920 else 0

/-- The signed refund change from the Amsterdam pricing rule. -/
def sstoreRefundDelta (original current value : Word) : Int :=
  (if current != value && original != 0 && current != 0 && value == 0 then 11616 else 0) -
  (if current != value && original != 0 && current == 0 then 11616 else 0) +
  (if current != value && original == value then 10000 else 0)

/-- Whether restoring a zero slot credits state gas. -/
def sstoreCredit (original current value : Word) : Bool :=
  current != value && original == value && original == 0

/-- A post-credit witness for the independent state-dependent relation. -/
def sstoreReadyWitness (s : State) (rest : Stack) (key value : Word) : State :=
  let original := SstoreOriginal s key
  let current := SloadValue s key
  let read := sstoreReadWitness s rest key
  let adjusted := Gas.StateMeter.adjustRefund (stateMeter read) (sstoreRefundDelta original current value)
  withStateMeter read (if sstoreCredit original current value then Gas.StateMeter.creditState adjusted 97920 else adjusted)

/-- The constructed witness meets all independent state-dependent conditions. -/
theorem sstore_ready_fields (s : State) (rest : Stack) (key value : Word) :
    SstoreReady s (sstoreReadyWitness s rest key value) rest key value
      (SloadCost s key + sstoreWriteCost (SstoreOriginal s key) (SloadValue s key) value)
      (sstoreStateCost (SstoreOriginal s key) (SloadValue s key) value) := by
  let original := SstoreOriginal s key
  let current := SloadValue s key
  refine ⟨sstoreReadWitness s rest key, sstoreWriteCost original current value,
    (if current != value && original != 0 && current != 0 && value == 0 then 11616 else 0),
    (if current != value && original != 0 && current == 0 then 11616 else 0),
    (if current != value && original == value then 10000 else 0),
    sstoreCredit original current value, ?_, ?_, ?_, rfl⟩
  · simpa [sstoreReadWitness, SloadRead, TransactionTracker.getStorage] using sstore_read_fields s rest key
  · simpa [sstoreWriteCost, sstoreStateCost, sstoreCredit] using sstore_pricing original current value
  · simpa [sstoreReadyWitness, sstoreRefundDelta, original, current] using
      sstore_credit_fields (sstoreReadWitness s rest key) (sstoreRefundDelta original current value)
        (sstoreCredit original current value)

/-- The independent post-sentry conditions determine the frame and both prices. -/
theorem sstore_ready_unique (s ready : State) (rest : Stack) (key value : Word)
    (cost stateCost : Nat) (h : SstoreReady s ready rest key value cost stateCost) :
    ready = sstoreReadyWitness s rest key value ∧
    cost = SloadCost s key + sstoreWriteCost (SstoreOriginal s key) (SloadValue s key) value ∧
    stateCost = sstoreStateCost (SstoreOriginal s key) (SloadValue s key) value := by
  rcases h with ⟨read, writeCost, clear, reverse, restore, credit, readFields, pricing, creditFields, costEq⟩
  have readEq := sstore_read_unique s read rest key readFields
  have prices := sstore_pricing_unique (SstoreOriginal s key) (SloadValue s key) value
    writeCost stateCost clear reverse restore credit pricing
  rcases prices with ⟨writeEq, stateEq, clearEq, reverseEq, restoreEq, creditEq⟩
  have readyEq := sstore_credit_unique read ready (clear - reverse + restore) credit creditFields
  simp [readEq, writeEq, stateEq, clearEq, reverseEq, restoreEq, creditEq,
    sstoreReadWitness, sstoreReadyWitness, sstoreWriteCost, sstoreStateCost,
    sstoreRefundDelta, sstoreCredit] at readyEq costEq ⊢
  exact ⟨readyEq, costEq⟩

/-- After the sentry, the helper reaches the witness and performs the two charges. -/
theorem sstore_after_sentry (s : State) (first rest : Stack) (key value : Word)
    (static : s.isStatic = false) (items : s.stack.val = key :: first.val)
    (items' : first.val = value :: rest.val) (gas : 2301 ≤ s.gas) :
    sstore s =
      let ready := sstoreReadyWitness s rest key value
      let cost := SloadCost s key + sstoreWriteCost (SstoreOriginal s key) (SloadValue s key) value
      let stateCost := sstoreStateCost (SstoreOriginal s key) (SloadValue s key) value
      if ready.gas < cost then .exception ready .outOfGas else
      let charged := { ready with gas := ready.gas - cost }
      match Gas.StateMeter.chargeState (stateMeter charged) stateCost with
      | .error _ => .exception charged .outOfGas
      | .ok meter =>
        let paid := withStateMeter charged meter
        match TransactionTracker.setStorage paid.tracker s.context.environment.currentTarget key value with
        | .error (_, tracker) => .exception { paid with tracker } .missingStorageAccount
        | .ok tracker => .continue { paid with tracker, pc := s.pc + 1 } := by
  have pop : s.stack.pop = .ok (key, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have pop' : first.pop = .ok (value, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items'
  have notGas : ¬ s.gas < 2301 := Nat.not_lt.mpr gas
  have original : TransactionState.getStorageOriginal s.tracker s.context.environment.currentTarget key =
      SstoreOriginal s key := by simp [TransactionState.getStorageOriginal, SstoreOriginal]
  have current : (TransactionTracker.getStorage s.tracker s.context.environment.currentTarget key).1 =
      SloadValue s key := by
    unfold TransactionTracker.getStorage SloadValue
    cases h : s.tracker.writes.storageWrites.lookup (s.context.environment.currentTarget, key) <;> simp [h]
  have read : (TransactionTracker.getStorage s.tracker s.context.environment.currentTarget key).2 =
      SloadRead s key := rfl
  by_cases warm : (s.context.environment.currentTarget, key) ∈ s.warmSlots <;>
    simp [sstore, static, pop, pop', warm, notGas, original, current, read,
      SloadWarm, SloadCost, sstoreReadyWitness, sstoreReadWitness, sstoreWriteCost,
      sstoreStateCost, sstoreRefundDelta, sstoreCredit, and_assoc] <;> congr 1

/-- The post-sentry stages do not advance the program counter. -/
theorem sstore_paid_pc (s ready charged paid : State) (rest : Stack) (key value : Word)
    (cost stateCost : Nat) (h : SstoreReady s ready rest key value cost stateCost)
    (exec : SstoreExecutionFields ready charged cost)
    (charge : SstoreChargeFields charged paid stateCost) : paid.pc = s.pc := by
  rcases h with ⟨read, _, _, _, _, _, readFields, _, creditFields, _⟩
  exact charge.1.2.1.trans (exec.1.2.1.trans (creditFields.1.2.1.trans readFields.2.1))

/-- The post-sentry stages retain the immutable context. -/
theorem sstore_paid_context (s ready charged paid : State) (rest : Stack) (key value : Word)
    (cost stateCost : Nat) (h : SstoreReady s ready rest key value cost stateCost)
    (exec : SstoreExecutionFields ready charged cost)
    (charge : SstoreChargeFields charged paid stateCost) : paid.context = s.context := by
  rcases h with ⟨read, _, _, _, _, _, readFields, _, creditFields, _⟩
  exact charge.1.2.2.2.2.1.trans (exec.1.2.2.2.2.1.trans
    (creditFields.1.2.2.2.2.1.trans readFields.2.2.2.2.2.1))

end EthLib.EVM.Frame
