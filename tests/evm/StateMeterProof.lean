import EthLib.EVM.Proofs.Gas.StateMeter

open EthLib.EVM.Gas.StateMeter

namespace StateMeterConsumer

theorem charge_forward (m n : Meter) (amount : Nat) (h : chargeState m amount = .ok n) :
    ChargeEffect m n amount := (chargeState_ok_iff m n amount).mp h

theorem charge_converse (m n : Meter) (amount : Nat) (h : ChargeEffect m n amount) :
    chargeState m amount = .ok n := (chargeState_ok_iff m n amount).mpr h

theorem charge_error (m : Meter) (amount : Nat) :
    chargeState m amount = .error .outOfGas ↔ m.stateGas + m.executionGas < amount :=
  chargeState_error_iff m amount

theorem credit_forward (m : Meter) (amount : Nat) : CreditEffect m (creditState m amount) amount :=
  (creditState_iff m (creditState m amount) amount).mp rfl

theorem credit_converse (m n : Meter) (amount : Nat) (h : CreditEffect m n amount) :
    creditState m amount = n := (creditState_iff m n amount).mpr h

theorem composed (m n : Meter) (amount : Nat) (noSpill : m.spilled = 0)
    (run : chargeState m amount = .ok n) : creditState n amount = m :=
  charge_credit_roundtrip m n amount noSpill run

theorem totals (m n : Meter) (amount : Nat) (run : chargeState m amount = .ok n) :
    n.executionGas + n.stateGas + amount = m.executionGas + m.stateGas ∧
    (creditState n amount).executionGas + (creditState n amount).stateGas =
      n.executionGas + n.stateGas + amount :=
  ⟨chargeState_conservation m n amount run, creditState_conservation n amount⟩

theorem refund_forward (m : Meter) (delta : Int) : RefundEffect m (adjustRefund m delta) delta :=
  (adjustRefund_iff m (adjustRefund m delta) delta).mp rfl

theorem refund_converse (m n : Meter) (delta : Int) (h : RefundEffect m n delta) :
    adjustRefund m delta = n := (adjustRefund_iff m n delta).mpr h

#print axioms refund_forward
#print axioms refund_converse
#print axioms charge_forward
#print axioms charge_converse
#print axioms charge_error
#print axioms credit_forward
#print axioms credit_converse
#print axioms composed
#print axioms totals

end StateMeterConsumer
