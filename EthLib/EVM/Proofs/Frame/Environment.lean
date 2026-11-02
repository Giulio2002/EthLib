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

/-- Each block observation selects the supplied field. -/
theorem block_observation_values (s : State) :
    observationWord (Observation.coinbase.value s) = Environment.addressWord s.context.environment.coinbase ∧
    observationWord (Observation.timestamp.value s) = s.context.environment.timestamp ∧
    observationWord (Observation.number.value s) = s.context.environment.number ∧
    observationWord (Observation.prevrandao.value s) = s.context.environment.prevRandao ∧
    observationWord (Observation.gaslimit.value s) = s.context.environment.gasLimit ∧
    observationWord (Observation.chainid.value s) = BitVec.ofNat 256 s.context.environment.chainId.val ∧
    observationWord (Observation.basefee.value s) = s.context.environment.baseFee := by
  simp [observationWord, Observation.value, Environment.addressWord]

/-- The chain identifier is zero extended without reduction. -/
theorem chainId_word_toNat (id : Fin (2 ^ 64)) :
    (BitVec.ofNat 256 id.val).toNat = id.val := by
  simp only [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have bound := id.isLt
  have widths : 2 ^ 64 < 2 ^ 256 := by decide
  omega

/-- The word stored for PREVRANDAO has exactly the supplied big-endian bytes. -/
theorem prevRandao_codec (bytes : ByteArray) (s : State)
    (h : Word.ofBytesBE bytes = .ok s.context.environment.prevRandao) :
    s.context.environment.prevRandao.toBytesBE = bytes :=
  EthLib.EVM.Proofs.Word.toBytesBE_ofBytesBE bytes _ h

/-- Actual success yields the selected block word and preserves the context. -/
theorem block_observation_actual (s t : State) (o : Observation)
    (at_ : At s (some o.opcode)) (run : step s = .continue t) :
    t.stack.val = observationWord (o.value s) :: s.stack.val ∧
    t.context = s.context := by
  have fields := step_observation_actual s t o at_ run
  exact ⟨fields.2.2.2.2.2.2.1, fields.2.2.2.2.2.2.2.1⟩

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
