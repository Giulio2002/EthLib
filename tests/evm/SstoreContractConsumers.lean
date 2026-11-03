import EthLib.EVM.Proofs.Frame.SstoreLocal

open EthLib.EVM
namespace SstoreContractConsumers

-- Each pair applies both the forward and converse contract to arbitrary fields.
theorem pricing_both (original current value : Word) (writeCost stateCost : Nat)
    (clear reverse restore : Int) (credit : Bool)
    (h : Frame.SstorePricing original current value writeCost stateCost clear reverse restore credit) :
    Frame.SstorePricing original current value
      (if original == current && current != value then 10000 else 0)
      (if original == current && current != value && original == 0 then 97920 else 0)
      (if current != value && original != 0 && current != 0 && value == 0 then 11616 else 0)
      (if current != value && original != 0 && current == 0 then 11616 else 0)
      (if current != value && original == value then 10000 else 0)
      (current != value && original == value && original == 0) ∧
    writeCost = (if original == current && current != value then 10000 else 0) ∧
    stateCost = (if original == current && current != value && original == 0 then 97920 else 0) ∧
    clear = (if current != value && original != 0 && current != 0 && value == 0 then 11616 else 0) ∧
    reverse = (if current != value && original != 0 && current == 0 then 11616 else 0) ∧
    restore = (if current != value && original == value then 10000 else 0) ∧
    credit = (current != value && original == value && original == 0) :=
  ⟨Frame.sstore_pricing original current value,
    Frame.sstore_pricing_unique original current value writeCost stateCost clear reverse restore credit h⟩

theorem read_both (s t : Frame.State) (rest : Stack) (key : Word)
    (h : Frame.SstoreReadFields s t rest key) :
    Frame.SstoreReadFields s
      { s with stack := rest, warmSlots := Frame.SloadWarm s key, tracker := (TransactionTracker.getStorage s.tracker s.context.environment.currentTarget key).2 } rest key ∧
    t = { s with stack := rest, warmSlots := Frame.SloadWarm s key, tracker := Frame.SloadRead s key } :=
  ⟨Frame.sstore_read_fields s rest key, Frame.sstore_read_unique s t rest key h⟩

theorem credit_both (s t : Frame.State) (delta : Int) (credit : Bool)
    (h : Frame.SstoreCreditFields s t delta credit) :
    Frame.SstoreCreditFields s
      (Frame.withStateMeter s (if credit then Gas.StateMeter.creditState
        (Gas.StateMeter.adjustRefund (Frame.stateMeter s) delta) 97920
        else Gas.StateMeter.adjustRefund (Frame.stateMeter s) delta)) delta credit ∧
    t = Frame.withStateMeter s (if credit then Gas.StateMeter.creditState
      (Gas.StateMeter.adjustRefund (Frame.stateMeter s) delta) 97920
      else Gas.StateMeter.adjustRefund (Frame.stateMeter s) delta) :=
  ⟨Frame.sstore_credit_fields s delta credit, Frame.sstore_credit_unique s t delta credit h⟩

theorem charge_both (s t : Frame.State) (amount : Nat) (meter : Gas.StateMeter.Meter)
    (run : Gas.StateMeter.chargeState (Frame.stateMeter s) amount = .ok meter)
    (h : Frame.SstoreChargeFields s t amount) :
    Frame.SstoreChargeFields s (Frame.withStateMeter s meter) amount ∧
    ∃ m, Gas.StateMeter.chargeState (Frame.stateMeter s) amount = .ok m ∧ t = Frame.withStateMeter s m :=
  ⟨Frame.sstore_charge_fields s amount meter run, Frame.sstore_charge_converse s t amount h⟩

theorem execution_both (s t : Frame.State) (cost : Nat) (enough : cost ≤ s.gas)
    (h : Frame.SstoreExecutionFields s t cost) :
    Frame.SstoreExecutionFields s { s with gas := s.gas - cost } cost ∧
    t = { s with gas := s.gas - cost } :=
  ⟨Frame.sstore_execution_fields s cost enough, Frame.sstore_execution_unique s t cost h⟩

theorem ready_both (s t : Frame.State) (rest : Stack) (key value : Word) (cost stateCost : Nat)
    (h : Frame.SstoreReady s t rest key value cost stateCost) :
    Frame.SstoreReady s (Frame.sstoreReadyWitness s rest key value) rest key value
      (Frame.SloadCost s key + Frame.sstoreWriteCost (Frame.SstoreOriginal s key) (Frame.SloadValue s key) value)
      (Frame.sstoreStateCost (Frame.SstoreOriginal s key) (Frame.SloadValue s key) value) ∧
    t = Frame.sstoreReadyWitness s rest key value ∧
    cost = Frame.SloadCost s key + Frame.sstoreWriteCost (Frame.SstoreOriginal s key) (Frame.SloadValue s key) value ∧
    stateCost = Frame.sstoreStateCost (Frame.SstoreOriginal s key) (Frame.SloadValue s key) value :=
  ⟨Frame.sstore_ready_fields s rest key value, Frame.sstore_ready_unique s t rest key value cost stateCost h⟩

theorem write_success_both (s t : Frame.State) (key value : Word) (present : Frame.SstoreAccount s ≠ none)
    (h : Frame.SstoreWriteFields s t key value true) :
    TransactionTracker.setStorage s.tracker s.context.environment.currentTarget key value =
      .ok (Frame.sstoreWriteWitness s key value true).tracker ∧ t = Frame.sstoreWriteWitness s key value true :=
  ⟨Frame.sstore_write_witness_success s key value present, Frame.sstore_write_unique s t key value true h⟩

theorem write_error_both (s t : Frame.State) (key value : Word) (absent : Frame.SstoreAccount s = none)
    (h : Frame.SstoreWriteFields s t key value false) :
    TransactionTracker.setStorage s.tracker s.context.environment.currentTarget key value =
      .error (.missingAccount, (Frame.sstoreWriteWitness s key value false).tracker) ∧
    t = Frame.sstoreWriteWitness s key value false :=
  ⟨Frame.sstore_write_witness_missing s key value absent, Frame.sstore_write_unique s t key value false h⟩

theorem observed_success (s : Frame.State) (key value : Word) (tracker : TransactionState.State)
    (run : TransactionTracker.setStorage s.tracker s.context.environment.currentTarget key value = .ok tracker) :
    Frame.SstoreWriteFields s { s with tracker, pc := s.pc + 1 } key value true ∧
    { s with tracker, pc := s.pc + 1 } = Frame.sstoreWriteWitness s key value true := by
  have effect := Frame.sstore_write_success_fields s key value tracker run
  exact ⟨effect, Frame.sstore_write_unique s _ key value true effect⟩

theorem observed_error (s : Frame.State) (key value : Word) (tracker : TransactionState.State)
    (run : TransactionTracker.setStorage s.tracker s.context.environment.currentTarget key value =
      .error (.missingAccount, tracker)) :
    Frame.SstoreWriteFields s { s with tracker } key value false ∧
    { s with tracker } = Frame.sstoreWriteWitness s key value false := by
  have effect := Frame.sstore_write_error_fields s key value tracker run
  exact ⟨effect, Frame.sstore_write_unique s _ key value false effect⟩

theorem account_observation (s : Frame.State) :
    Frame.SstoreAccount s = (TransactionTracker.getAccountOptional s.tracker s.context.environment.currentTarget).1 :=
  Frame.sstore_account_value s

theorem after_sentry_failure (s : Frame.State) (first rest : Stack) (key value : Word)
    (static : s.isStatic = false) (items : s.stack.val = key :: first.val)
    (items' : first.val = value :: rest.val) (gas : 2301 ≤ s.gas)
    (low : (Frame.sstoreReadyWitness s rest key value).gas <
      Frame.SloadCost s key + Frame.sstoreWriteCost (Frame.SstoreOriginal s key) (Frame.SloadValue s key) value) :
    Frame.sstore s = .exception (Frame.sstoreReadyWitness s rest key value) .outOfGas := by
  rw [Frame.sstore_after_sentry s first rest key value static items items' gas]
  simp [low]

theorem stage_pc_context (s ready charged paid : Frame.State) (rest : Stack) (key value : Word)
    (cost stateCost : Nat) (h : Frame.SstoreReady s ready rest key value cost stateCost)
    (exec : Frame.SstoreExecutionFields ready charged cost)
    (charge : Frame.SstoreChargeFields charged paid stateCost) :
    paid.pc = s.pc ∧ paid.context = s.context :=
  ⟨Frame.sstore_paid_pc s ready charged paid rest key value cost stateCost h exec charge,
   Frame.sstore_paid_context s ready charged paid rest key value cost stateCost h exec charge⟩

theorem local_constructed (s : Frame.State) :
    ∃ out, Frame.SstoreLocal s out ∧ Frame.sstore s = out := by
  obtain ⟨out, rule⟩ := Frame.sstore_local_total s
  exact ⟨out, rule, Frame.sstore_local_sound rule⟩

#print axioms pricing_both
#print axioms read_both
#print axioms credit_both
#print axioms charge_both
#print axioms execution_both
#print axioms ready_both
#print axioms write_success_both
#print axioms write_error_both
#print axioms observed_success
#print axioms observed_error
#print axioms account_observation
#print axioms after_sentry_failure
#print axioms stage_pc_context
#print axioms local_constructed
end SstoreContractConsumers
