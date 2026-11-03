module

public import EthLib.EVM.Gas.StateMeter
import Mathlib.Tactic

/-!
# State-gas meter contracts

The reference relations state arithmetic effects on each field.
They do not call the executable operations.
-/

@[expose] public section
namespace EthLib.EVM.Gas.StateMeter

/-- Fields that state-gas charges and credits do not change. -/
def Retained (before after : Meter) : Prop :=
  after.baseline = before.baseline ∧ after.refundCounter = before.refundCounter ∧
  after.committedSpill = before.committedSpill

/-- Mathematical charge effects, split by whether the reservoir covers the charge. -/
def ChargeEffect (before after : Meter) (amount : Nat) : Prop :=
  Retained before after ∧
    ((amount ≤ before.stateGas ∧ after.stateGas + amount = before.stateGas ∧
      after.executionGas = before.executionGas ∧ after.spilled = before.spilled) ∨
     (before.stateGas < amount ∧ amount ≤ before.stateGas + before.executionGas ∧
      after.stateGas = 0 ∧ after.executionGas + (amount - before.stateGas) = before.executionGas ∧
      after.spilled = before.spilled + (amount - before.stateGas)))

/-- Mathematical credit effects, split by whether the credit exhausts the spill. -/
def CreditEffect (before after : Meter) (amount : Nat) : Prop :=
  Retained before after ∧
    ((amount ≤ before.spilled ∧ after.executionGas = before.executionGas + amount ∧
      after.spilled + amount = before.spilled ∧ after.stateGas = before.stateGas) ∨
     (before.spilled < amount ∧ after.executionGas = before.executionGas + before.spilled ∧
      after.spilled = 0 ∧ after.stateGas = before.stateGas + (amount - before.spilled)))

/-- A signed refund change leaves both gas pools and spill bookkeeping unchanged. -/
def RefundEffect (before after : Meter) (delta : Int) : Prop :=
  after.executionGas = before.executionGas ∧ after.stateGas = before.stateGas ∧
  after.baseline = before.baseline ∧ after.refundCounter = before.refundCounter + delta ∧
  after.spilled = before.spilled ∧ after.committedSpill = before.committedSpill

/-- Signed refund adjustment satisfies the independent field relation exactly. -/
theorem adjustRefund_iff (before after : Meter) (delta : Int) :
    adjustRefund before delta = after ↔ RefundEffect before after delta := by
  cases before
  cases after
  simp [adjustRefund, RefundEffect, eq_comm]

/-- A charge succeeds exactly when the independent field relation holds. -/
theorem chargeState_ok_iff (before after : Meter) (amount : Nat) :
    chargeState before amount = .ok after ↔ ChargeEffect before after amount := by
  rcases before with ⟨execution, state, baseline, refund, spilled, committed⟩
  rcases after with ⟨execution', state', baseline', refund', spilled', committed'⟩
  by_cases h : amount ≤ state
  · simp [chargeState, ChargeEffect, Retained, h]
    omega
  · by_cases h2 : amount ≤ state + execution
    · simp [chargeState, ChargeEffect, Retained, h, h2]; omega
    · simp [chargeState, ChargeEffect, Retained, h, h2]

/-- A charge fails exactly when both gas pools are insufficient. -/
theorem chargeState_error_iff (before : Meter) (amount : Nat) :
    chargeState before amount = .error .outOfGas ↔ before.stateGas + before.executionGas < amount := by
  by_cases h : amount ≤ before.stateGas
  · simp [chargeState, h]
    omega
  · by_cases h2 : amount ≤ before.stateGas + before.executionGas
    · simp [chargeState, h, h2]
    · simp [chargeState, h, h2]; omega

/-- Every credit satisfies exactly the independent field relation. -/
theorem creditState_iff (before after : Meter) (amount : Nat) :
    creditState before amount = after ↔ CreditEffect before after amount := by
  rcases before with ⟨execution, state, baseline, refund, spilled, committed⟩
  rcases after with ⟨execution', state', baseline', refund', spilled', committed'⟩
  by_cases h : amount ≤ spilled
  · simp [creditState, CreditEffect, Retained, h]
    omega
  · have h2 : spilled ≤ amount := by omega
    simp [creditState, CreditEffect, Retained, h, Nat.min_eq_right h2]
    omega

/-- A successful charge removes exactly the requested amount from the two pools. -/
theorem chargeState_conservation (before after : Meter) (amount : Nat)
    (run : chargeState before amount = .ok after) :
    after.executionGas + after.stateGas + amount = before.executionGas + before.stateGas := by
  have effect := (chargeState_ok_iff before after amount).mp run
  rcases effect.2 with first | second <;> omega

/-- A credit returns exactly the requested amount to the two pools. -/
theorem creditState_conservation (before : Meter) (amount : Nat) :
    (creditState before amount).executionGas + (creditState before amount).stateGas =
      before.executionGas + before.stateGas + amount := by
  have effect := (creditState_iff before (creditState before amount) amount).mp rfl
  rcases effect.2 with first | second <;> omega

/-- With no existing spill, crediting a successful charge restores the meter. -/
theorem charge_credit_roundtrip (before after : Meter) (amount : Nat)
    (noSpill : before.spilled = 0) (run : chargeState before amount = .ok after) :
    creditState after amount = before := by
  rcases before with ⟨execution, state, baseline, refund, spilled, committed⟩
  simp only at noSpill
  subst spilled
  by_cases h : amount ≤ state
  · simp [chargeState, h] at run
    subst after
    simp [creditState, h]
  · have h2 : amount ≤ state + execution := by
      by_contra bad
      simp [chargeState, h, bad] at run
    simp [chargeState, h, h2] at run
    subst after
    simp [creditState]
    omega

end EthLib.EVM.Gas.StateMeter
