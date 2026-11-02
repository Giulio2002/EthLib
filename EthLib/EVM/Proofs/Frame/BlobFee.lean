module

public import EthLib.EVM.Proofs.Frame.Environment
public import EthLib.EVM.Proofs.BlobFee

/-! Contracts for the Cancun blob base fee observation. -/

@[expose] public section
namespace EthLib.EVM.Frame

/-- The direct helper checks gas before stack capacity. -/
theorem blobBaseFee_gas (s : State) (gas : s.gas < 2) :
    blobBaseFee s = .exception s .outOfGas :=
  observe_gas s _ gas

/-- A full stack fails after a successful gas check. -/
theorem blobBaseFee_full (s : State) (gas : 2 ≤ s.gas)
    (full : s.stack.val.length = 1024) : blobBaseFee s = .exception s .stackOverflow :=
  observe_full s _ gas full

/-- Sufficient fields for a direct helper call to succeed at any code and PC. -/
theorem blobBaseFee_success (s t : State) (gas : 2 ≤ s.gas)
    (room : s.stack.val.length < 1024)
    (fields : Advances s t (s.pc + 1) (s.gas - 2)
      (observationWord (BlobFee.calculateBlobGasPrice s.context.environment.excessBlobGas) :: s.stack.val)) :
    blobBaseFee s = .continue t :=
  observe_success s t _ gas room fields

/-- Every successful direct helper call has the specified gas, stack, and frame fields. -/
theorem blobBaseFee_helper_actual (s t : State) (run : blobBaseFee s = .continue t) :
    2 ≤ s.gas ∧ s.stack.val.length < 1024 ∧
    Advances s t (s.pc + 1) (s.gas - 2)
      (observationWord (BlobFee.calculateBlobGasPrice s.context.environment.excessBlobGas) :: s.stack.val) :=
  observe_actual s t _ run

/-- A successful opcode follows the independent integer recurrence. -/
theorem blobBaseFee_actual (s t : State) (at_ : At s (some .blobbasefee))
    (run : step s = .continue t) :
    ∃ sum, BlobFee.RecurrenceSpec s.context.environment.excessBlobGas.val
        3338477 1 3338477 0 sum ∧
      2 ≤ s.gas ∧ s.stack.val.length < 1024 ∧
      Advances s t (s.pc + 1) (s.gas - 2)
        (observationWord (sum / 3338477) :: s.stack.val) := by
  have spec := (BlobFee.calculateBlobGasPrice_spec s.context.environment.excessBlobGas
    (BlobFee.calculateBlobGasPrice s.context.environment.excessBlobGas)).mpr rfl
  obtain ⟨sum, hs, hr⟩ := spec
  have actual := step_observation_actual s t .blobbasefee at_ run
  refine ⟨sum, hs, actual.1, actual.2.1, ?_⟩
  simpa [Observation.value, hr] using actual.2.2

/-- Independent recurrence conditions characterize each successful opcode step. -/
theorem blobBaseFee_success_iff (s t : State) (at_ : At s (some .blobbasefee)) :
    step s = .continue t ↔
      ∃ sum, BlobFee.RecurrenceSpec s.context.environment.excessBlobGas.val
          3338477 1 3338477 0 sum ∧
        2 ≤ s.gas ∧ s.stack.val.length < 1024 ∧
        Advances s t (s.pc + 1) (s.gas - 2)
          (observationWord (sum / 3338477) :: s.stack.val) := by
  constructor
  · exact blobBaseFee_actual s t at_
  · rintro ⟨sum, spec, gas, room, fields⟩
    have eq := (BlobFee.calculateBlobGasPrice_spec s.context.environment.excessBlobGas
      (sum / 3338477)).mp ⟨sum, spec, rfl⟩
    apply step_observation s t .blobbasefee at_ gas room
    simpa [Observation.value, observationWord, eq] using fields

/-- Independent outcome rules for a BLOBBASEFEE instruction. -/
inductive BlobBaseFeeRule (s : State) : Outcome → Prop where
  | gas : s.gas < 2 → BlobBaseFeeRule s (.exception s .outOfGas)
  | full : 2 ≤ s.gas → s.stack.val.length = 1024 →
      BlobBaseFeeRule s (.exception s .stackOverflow)
  | success (t : State) :
      (∃ sum, BlobFee.RecurrenceSpec s.context.environment.excessBlobGas.val
          3338477 1 3338477 0 sum ∧
        2 ≤ s.gas ∧ s.stack.val.length < 1024 ∧
        Advances s t (s.pc + 1) (s.gas - 2)
          (observationWord (sum / 3338477) :: s.stack.val)) →
      BlobBaseFeeRule s (.continue t)

/-- At BLOBBASEFEE the independent rules characterize every outcome. -/
theorem blobBaseFee_step_iff (s : State) (out : Outcome)
    (at_ : At s (some .blobbasefee)) : step s = out ↔ BlobBaseFeeRule s out := by
  constructor
  · intro run
    by_cases gas : 2 ≤ s.gas
    · by_cases room : s.stack.val.length < 1024
      · let stack : Stack := ⟨observationWord (BlobFee.calculateBlobGasPrice s.context.environment.excessBlobGas) :: s.stack.val, by simp; omega⟩
        let t : State := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
        have fields : Advances s t (s.pc + 1) (s.gas - 2)
            (observationWord (BlobFee.calculateBlobGasPrice s.context.environment.excessBlobGas) :: s.stack.val) := by
          simp [Advances, t, stack]
        have success := step_observation s t .blobbasefee at_ gas room (by
          simpa [Observation.value, observationWord] using fields)
        rw [success] at run
        subst out
        exact .success t ((blobBaseFee_success_iff s t at_).mp success)
      · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
        have failed := step_observation_full s .blobbasefee at_ gas full
        rw [failed] at run
        subst out
        exact .full gas full
    · have short : s.gas < 2 := by omega
      have failed := step_observation_gas s .blobbasefee at_ short
      rw [failed] at run
      subst out
      exact .gas short
  · intro rule
    cases rule with
    | gas short => exact step_observation_gas s .blobbasefee at_ short
    | full gas full => exact step_observation_full s .blobbasefee at_ gas full
    | success t fields => exact (blobBaseFee_success_iff s t at_).mpr fields

/-- An actual successful opcode pushes the fee reduced modulo the word width. -/
theorem blobBaseFee_step_head_mod (s t : State) (at_ : At s (some .blobbasefee))
    (run : step s = .continue t) :
    ∃ head, t.stack.val.head? = some head ∧
      head.toNat = BlobFee.calculateBlobGasPrice s.context.environment.excessBlobGas % Word.modulus := by
  have actual := step_observation_stack s t .blobbasefee at_ run
  refine ⟨observationWord (BlobFee.calculateBlobGasPrice s.context.environment.excessBlobGas), ?_, ?_⟩
  · simpa [Observation.value] using congrArg List.head? actual
  · exact observationWord_toNat _

/-- A representable fee from an actual successful step agrees with checked conversion. -/
theorem blobBaseFee_step_head_exact (s t : State) (at_ : At s (some .blobbasefee))
    (run : step s = .continue t)
    (representable : BlobFee.calculateBlobGasPrice s.context.environment.excessBlobGas < Word.modulus) :
    ∃ head, t.stack.val.head? = some head ∧
      head.toNat = BlobFee.calculateBlobGasPrice s.context.environment.excessBlobGas ∧
      Word.ofNat (BlobFee.calculateBlobGasPrice s.context.environment.excessBlobGas) = .ok head := by
  have actual := step_observation_stack s t .blobbasefee at_ run
  refine ⟨observationWord (BlobFee.calculateBlobGasPrice s.context.environment.excessBlobGas), ?_, ?_, ?_⟩
  · simpa [Observation.value] using congrArg List.head? actual
  · exact observationWord_exact _ representable
  · exact observationWord_checked _ representable

/-- A representable Cancun fee is preserved by the stack-word conversion. -/
theorem blobBaseFee_word_exact (s : State)
    (representable : BlobFee.calculateBlobGasPrice s.context.environment.excessBlobGas < Word.modulus) :
    (observationWord (BlobFee.calculateBlobGasPrice s.context.environment.excessBlobGas)).toNat =
      BlobFee.calculateBlobGasPrice s.context.environment.excessBlobGas :=
  observationWord_exact _ representable

end EthLib.EVM.Frame
