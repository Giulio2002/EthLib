module

public import EthLib.EVM.Frame

/-! Amsterdam execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`,
`vm/interpreter.py` `process_call` and `vm/__init__.py` `incorporate_child`. -/

@[expose] public section
namespace EthLib.EVM.ChildSettlement

inductive Error where
  | toolingOutcome | missingSnapshot | committedChildSpill
  deriving DecidableEq, Repr

/-- Install a tracker checkpoint before executing a child frame. -/
def checkpoint (child : Frame.State) : Frame.State :=
  { child with tracker := TransactionState.snapshot child.tracker }

/-- Settle the tracker and meter of one terminal child. -/
def settleChild (parent child : Frame.State) (succeeded : Bool) (gas : Nat)
    (output : ByteArray) : Except Error Frame.State :=
  if child.stateGas.committedSpill != 0 then .error .committedChildSpill
  else match (if succeeded then TransactionState.commit child.tracker
              else TransactionState.rollback child.tracker) with
  | .error _ => .error .missingSnapshot
  | .ok tracker =>
    let childReservoir := if succeeded then child.stateGas.reservoir else child.stateGas.baseline
    let childSpilled := if succeeded then child.stateGas.spilled else 0
    let reservoir := parent.stateGas.reservoir + childReservoir
    let spilled := parent.stateGas.spilled + childSpilled
    let repayment := if succeeded then min reservoir spilled else 0
    let meter : Frame.StateGas := {
    parent.stateGas with
    reservoir := reservoir - repayment
    spilled := spilled - repayment
    refundCounter := parent.stateGas.refundCounter +
      (if succeeded then child.stateGas.refundCounter else 0) }
    .ok { parent with
    gas := parent.gas + gas + repayment
    stateGas := meter
    tracker := tracker
    returnData := output
    logs := if succeeded then parent.logs ++ child.logs else parent.logs
    warmAddresses := if succeeded then child.warmAddresses ++ parent.warmAddresses else parent.warmAddresses
    warmSlots := if succeeded then child.warmSlots ++ parent.warmSlots else parent.warmSlots }

end EthLib.EVM.ChildSettlement
