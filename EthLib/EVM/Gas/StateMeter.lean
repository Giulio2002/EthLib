module

public import EthLib.EVM.Gas

/-!
# Amsterdam state-gas meter

Amsterdam execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`,
`vm/gas.py`, `charge_state_gas_from_meter` and `credit_state_gas_refund`.
The meter is supplied by the caller and does not implement frame settlement.
-/

@[expose] public section
namespace EthLib.EVM.Gas.StateMeter

/-- The source meter fields needed to charge and credit state gas. -/
structure Meter where
  executionGas : Nat
  stateGas : Nat
  baseline : Nat
  refundCounter : Int
  spilled : Nat
  committedSpill : Nat
  deriving DecidableEq, Repr

/-- Charge the reservoir first, then spill into execution gas if necessary. -/
def chargeState (m : Meter) (amount : Nat) : Except Gas.Error Meter :=
  if amount ≤ m.stateGas then
    .ok { m with stateGas := m.stateGas - amount }
  else if amount ≤ m.stateGas + m.executionGas then
    let remainder := amount - m.stateGas
    .ok { m with stateGas := 0, executionGas := m.executionGas - remainder, spilled := m.spilled + remainder }
  else .error .outOfGas

/-- Credit outstanding spill first, then the state-gas reservoir. -/
def creditState (m : Meter) (amount : Nat) : Meter :=
  let fromExecution := min amount m.spilled
  { m with executionGas := m.executionGas + fromExecution, spilled := m.spilled - fromExecution, stateGas := m.stateGas + (amount - fromExecution) }

/-- Apply a signed refund-counter change as in Amsterdam `storage.py`, `sstore`. -/
def adjustRefund (m : Meter) (delta : Int) : Meter :=
  { m with refundCounter := m.refundCounter + delta }

end EthLib.EVM.Gas.StateMeter
