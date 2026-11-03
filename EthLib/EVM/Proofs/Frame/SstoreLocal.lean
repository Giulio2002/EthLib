module

public import EthLib.EVM.Proofs.Frame.SstorePricing

/-! Independent SSTORE helper rules, valid for arbitrary frame code and program counter. -/

@[expose] public section
namespace EthLib.EVM.Frame

/-- Every independent local rule is executed by the helper. -/
theorem sstore_local_sound {s : State} {out : Outcome} (h : SstoreLocal s out) : sstore s = out := by
  cases h with
  | sstoreStatic static =>
    simp [sstore, static]
  | sstoreUnderflow static empty =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr empty
    simp [sstore, static, pop, failStack]
  | sstoreSecondUnderflow rest key static items empty =>
    have pop : s.stack.pop = .ok (key, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
    have pop' : rest.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr empty
    simp [sstore, static, pop, pop', failStack]
  | sstoreSentry first rest key value static items items' gas =>
    have pop : s.stack.pop = .ok (key, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
    have pop' : first.pop = .ok (value, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items'
    by_cases warm : (s.context.environment.currentTarget, key) ∈ s.warmSlots <;>
      simp [sstore, static, pop, pop', warm, gas]
  | sstoreExecutionGas ready first rest key value cost stateCost static items items' gas fields insufficient =>
    rcases sstore_ready_unique s ready rest key value cost stateCost fields with ⟨rfl, rfl, rfl⟩
    simp [sstore_after_sentry s first rest key value static items items' gas, insufficient]
  | sstoreStateGas ready charged first rest key value cost stateCost static items items' gas fields enough execution insufficient =>
    rcases sstore_ready_unique s ready rest key value cost stateCost fields with ⟨rfl, rfl, rfl⟩
    have chargedEq := sstore_execution_unique _ charged _ execution
    subst charged
    have fail : Gas.StateMeter.chargeState
        (stateMeter { (sstoreReadyWitness s rest key value) with gas :=
          (sstoreReadyWitness s rest key value).gas -
            (SloadCost s key + sstoreWriteCost (SstoreOriginal s key) (SloadValue s key) value) })
        (sstoreStateCost (SstoreOriginal s key) (SloadValue s key) value) = .error .outOfGas :=
      (Gas.StateMeter.chargeState_error_iff _ _).mpr (by simpa [stateMeter] using insufficient)
    simp [sstore_after_sentry s first rest key value static items items' gas,
      Nat.not_lt.mpr enough, fail]
  | sstoreMissing ready charged paid result first rest key value cost stateCost static items items' gas fields enough execution charge absent written =>
    have pcEq := sstore_paid_pc s ready charged paid rest key value cost stateCost fields execution charge
    have contextEq := sstore_paid_context s ready charged paid rest key value cost stateCost fields execution charge
    have ⟨meter, meterRun, paidEq⟩ := sstore_charge_converse charged paid stateCost charge
    have resultEq := sstore_write_unique paid result key value false written
    have writeRun := sstore_write_witness_missing paid key value absent
    rcases sstore_ready_unique s ready rest key value cost stateCost fields with ⟨rfl, rfl, rfl⟩
    have chargedEq := sstore_execution_unique _ charged _ execution
    subst charged
    rw [sstore_after_sentry s first rest key value static items items' gas]
    simp only [Nat.not_lt.mpr enough, ↓reduceIte, meterRun]
    rw [← paidEq, ← contextEq, writeRun]
    simp [resultEq, sstoreWriteWitness, pcEq]
  | sstoreSuccess ready charged paid result first rest key value cost stateCost static items items' gas fields enough execution charge present written =>
    have pcEq := sstore_paid_pc s ready charged paid rest key value cost stateCost fields execution charge
    have contextEq := sstore_paid_context s ready charged paid rest key value cost stateCost fields execution charge
    have ⟨meter, meterRun, paidEq⟩ := sstore_charge_converse charged paid stateCost charge
    have resultEq := sstore_write_unique paid result key value true written
    have writeRun := sstore_write_witness_success paid key value present
    rcases sstore_ready_unique s ready rest key value cost stateCost fields with ⟨rfl, rfl, rfl⟩
    have chargedEq := sstore_execution_unique _ charged _ execution
    subst charged
    rw [sstore_after_sentry s first rest key value static items items' gas]
    simp only [Nat.not_lt.mpr enough, ↓reduceIte, meterRun]
    rw [← paidEq, ← contextEq, writeRun]
    simp [resultEq, sstoreWriteWitness, pcEq]

/-- Every frame has an independent local SSTORE outcome. -/
theorem sstore_local_total (s : State) : ∃ out, SstoreLocal s out := by
  by_cases static : s.isStatic = true
  · exact ⟨_, .sstoreStatic s static⟩
  · have dynamic : s.isStatic = false := by cases h : s.isStatic <;> simp_all
    cases items : s.stack.val with
    | nil => exact ⟨_, .sstoreUnderflow s dynamic items⟩
    | cons key xs =>
      let first : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
      have items' : s.stack.val = key :: first.val := items
      cases second : first.val with
      | nil => exact ⟨_, .sstoreSecondUnderflow s first key dynamic items' second⟩
      | cons value ys =>
        let rest : Stack := ⟨ys, by have bound := first.property; rw [second] at bound; simp at bound; omega⟩
        have second' : first.val = value :: rest.val := second
        by_cases gas : 2301 ≤ s.gas
        · let ready := sstoreReadyWitness s rest key value
          let cost := SloadCost s key + sstoreWriteCost (SstoreOriginal s key) (SloadValue s key) value
          let stateCost := sstoreStateCost (SstoreOriginal s key) (SloadValue s key) value
          have fields : SstoreReady s ready rest key value cost stateCost := sstore_ready_fields s rest key value
          by_cases enough : cost ≤ ready.gas
          · let charged := { ready with gas := ready.gas - cost }
            have execution : SstoreExecutionFields ready charged cost := sstore_execution_fields ready cost enough
            cases metered : Gas.StateMeter.chargeState (stateMeter charged) stateCost with
            | error e =>
              cases e
              have insufficient : charged.stateGas.reservoir + charged.gas < stateCost := by
                exact (Gas.StateMeter.chargeState_error_iff _ _).mp metered
              exact ⟨_, .sstoreStateGas s ready charged first rest key value cost stateCost
                dynamic items' second' gas fields enough execution insufficient⟩
            | ok meter =>
              let paid := withStateMeter charged meter
              have charge : SstoreChargeFields charged paid stateCost := sstore_charge_fields charged stateCost meter metered
              cases account : SstoreAccount paid with
              | none =>
                let result := sstoreWriteWitness paid key value false
                have write := sstore_write_witness_missing paid key value account
                have writeFields : SstoreWriteFields paid result key value false := by
                  simpa [result, sstoreWriteWitness] using
                    sstore_write_error_fields paid key value result.tracker write
                exact ⟨_, .sstoreMissing s ready charged paid result first rest key value cost stateCost
                  dynamic items' second' gas fields enough execution charge account writeFields⟩
              | some accountValue =>
                let result := sstoreWriteWitness paid key value true
                have present : SstoreAccount paid ≠ none := by simp [account]
                have write := sstore_write_witness_success paid key value present
                have writeFields : SstoreWriteFields paid result key value true := by
                  simpa [result, sstoreWriteWitness] using
                    sstore_write_success_fields paid key value result.tracker write
                exact ⟨_, .sstoreSuccess s ready charged paid result first rest key value cost stateCost
                  dynamic items' second' gas fields enough execution charge present writeFields⟩
          · exact ⟨_, .sstoreExecutionGas s ready first rest key value cost stateCost
              dynamic items' second' gas fields (Nat.lt_of_not_ge enough)⟩
        · exact ⟨_, .sstoreSentry s first rest key value dynamic items' second' (Nat.lt_of_not_ge gas)⟩

/-- The helper is equivalent to the independent source cases on all frames. -/
theorem sstore_iff_local (s : State) (out : Outcome) : sstore s = out ↔ SstoreLocal s out := by
  constructor
  · intro eq
    obtain ⟨result, rule⟩ := sstore_local_total s
    have sound := sstore_local_sound rule
    rw [eq] at sound
    cases sound
    exact rule
  · exact sstore_local_sound

end EthLib.EVM.Frame
