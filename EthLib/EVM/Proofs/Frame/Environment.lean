module

public import EthLib.EVM.Proofs.Frame
public import EthLib.EVM.Proofs.Environment

/-! The observation rules select the message fields and preserve their values. -/

@[expose] public section
namespace EthLib.EVM.Frame

/-- The address observations use zero extension, with no reduction. -/
theorem environment_address_values (s : State) :
    observationWord (Observation.address.value s) = Environment.addressWord s.context.environment.currentTarget ∧
    observationWord (Observation.origin.value s) = Environment.addressWord s.context.environment.origin ∧
    observationWord (Observation.caller.value s) = Environment.addressWord s.context.environment.caller := by
  exact ⟨rfl, rfl, rfl⟩

/-- Value and gas price are already words and are preserved by observation. -/
theorem environment_word_values (s : State) :
    observationWord (Observation.callvalue.value s) = s.context.environment.value ∧
    observationWord (Observation.gasprice.value s) = s.context.environment.gasPrice := by
  simp [observationWord, Observation.value]

/-- A successful helper invocation determines all output fields for any value function. -/
theorem observe_actual (s t : State) (value : Nat → Nat)
    (run : observe s value = .continue t) :
    2 ≤ s.gas ∧ s.stack.val.length < 1024 ∧
      Advances s t (s.pc + 1) (s.gas - 2)
        (observationWord (value (s.gas - 2)) :: s.stack.val) := by
  have gas : 2 ≤ s.gas := by
    by_cases h : 2 ≤ s.gas
    · exact h
    have bad := observe_gas s value (by omega)
    rw [run] at bad
    cases bad
  have room : s.stack.val.length < 1024 := by
    by_cases h : s.stack.val.length < 1024
    · exact h
    have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
    have bad := observe_full s value gas full
    rw [run] at bad
    cases bad
  let stack : Stack := ⟨observationWord (value (s.gas - 2)) :: s.stack.val, by simp; omega⟩
  let target : State := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
  have fields : Advances s target (s.pc + 1) (s.gas - 2)
      (observationWord (value (s.gas - 2)) :: s.stack.val) := by simp [Advances, target, stack]
  have ok := observe_success s target value gas room fields
  rw [run] at ok
  have eq : t = target := Outcome.continue.inj ok
  exact ⟨gas, room, eq ▸ fields⟩

end EthLib.EVM.Frame
