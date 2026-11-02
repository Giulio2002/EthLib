module

public import EthLib.EVM.BlobFee
import Mathlib.Tactic

/-! Independent relational specification of the source integer recurrence. -/

@[expose] public section
namespace EthLib.EVM.BlobFee

/-- Each step adds the current term and truncates the next term by division. -/
inductive RecurrenceSpec (numerator denominator : Nat) : Nat → Nat → Nat → Nat → Prop where
  | done (index output) : RecurrenceSpec numerator denominator index 0 output output
  | next (index term output result) : term ≠ 0 →
      RecurrenceSpec numerator denominator (index + 1)
        (term * numerator / (denominator * index)) (output + term) result →
      RecurrenceSpec numerator denominator index term output result

/-- The executable loop follows the recurrence on its whole accepted domain. -/
theorem recurrence_spec (numerator denominator index term output : Nat)
    (denominatorPositive : 0 < denominator) (indexPositive : 0 < index) :
    RecurrenceSpec numerator denominator index term output
      (recurrence numerator denominator index term output denominatorPositive indexPositive) := by
  fun_induction recurrence numerator denominator index term output denominatorPositive indexPositive with
  | case1 =>
    simp_all [RecurrenceSpec.done]
  | case2 =>
    exact RecurrenceSpec.next _ _ _ _ (by assumption) (by assumption)

/-- The integer recurrence has at most one final sum. -/
theorem recurrenceSpec_unique {numerator denominator index term output result other : Nat}
    (first : RecurrenceSpec numerator denominator index term output result)
    (second : RecurrenceSpec numerator denominator index term output other) : result = other := by
  induction first generalizing other with
  | done index output =>
    cases second with
    | done => rfl
    | next _ _ _ _ nonzero _ => contradiction
  | next index term output result nonzero rest ih =>
    cases second with
    | done => contradiction
    | next _ _ _ _ _ next => exact ih next

/-- The relation characterizes the executable loop on its full domain. -/
theorem recurrence_iff (numerator denominator index term output result : Nat)
    (denominatorPositive : 0 < denominator) (indexPositive : 0 < index) :
    RecurrenceSpec numerator denominator index term output result ↔
      result = recurrence numerator denominator index term output denominatorPositive indexPositive := by
  constructor
  · intro h
    exact recurrenceSpec_unique h (recurrence_spec _ _ _ _ _ _ _)
  · intro h
    subst result
    exact recurrence_spec _ _ _ _ _ _ _

/-- The source approximation starts with the scaled factor and divides the final sum. -/
theorem taylorExponential_spec (factor numerator : Nat) (denominator : {d : Nat // 0 < d})
    (result : Nat) :
    (∃ sum, RecurrenceSpec numerator denominator.val 1 (factor * denominator.val) 0 sum ∧
      result = sum / denominator.val) ↔ result = taylorExponential factor numerator denominator := by
  constructor
  · rintro ⟨sum, hs, hr⟩
    have hsum := (recurrence_iff numerator denominator.val 1
      (factor * denominator.val) 0 sum denominator.property (by omega)).mp hs
    simpa [taylorExponential, hsum] using hr
  · intro h
    exact ⟨_, recurrence_spec _ _ _ _ _ _ _, h⟩

/-- The Cancun price uses the source constants and the U64 excess value. -/
theorem calculateBlobGasPrice_spec (excessBlobGas : Fin (2 ^ 64)) (result : Nat) :
    (∃ sum, RecurrenceSpec excessBlobGas.val 3338477 1 3338477 0 sum ∧
      result = sum / 3338477) ↔ result = calculateBlobGasPrice excessBlobGas := by
  change (∃ sum, RecurrenceSpec excessBlobGas.val blobBaseFeeUpdateFraction.val 1
    (1 * blobBaseFeeUpdateFraction.val) 0 sum ∧ result = sum / blobBaseFeeUpdateFraction.val) ↔
      result = taylorExponential 1 excessBlobGas.val blobBaseFeeUpdateFraction
  exact taylorExponential_spec 1 excessBlobGas.val blobBaseFeeUpdateFraction result

end EthLib.EVM.BlobFee
