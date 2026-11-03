module

public import EthLib.EVM.ChildSettlement.Core
public import EthLib.EVM.Gas.Call
public import EthLib.EVM.TransactionTransfer

/-!
# CALL preparation

Amsterdam execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`,
`vm/instructions/system.py`, `call`.
A delegation designator and missing code are explicit tooling boundaries
in this incomplete preparation layer.
-/

@[expose] public section
namespace EthLib.EVM.CallPreparation

/-- Incomplete state or an operation outside the currently prepared subset. -/
inductive Tooling where
  | valueTransfer | delegation | missingCode
  deriving DecidableEq, Repr

/-- The post-charge parent and child parameters needed by the runner. -/
structure Prepared where
  parent : Frame.State
  request : Frame.CallRequest
  address : World.Address
  code : ByteArray
  childGas : Nat
  stateGrant : Nat
  newAccountCharged : Bool
  insufficientBalance : Bool

/-- Preparation can fail at a protocol gas check or a tooling boundary. -/
inductive Result where
  | ready (prepared : Prepared)
  | outOfGas (diagnostic : Frame.State)
  | tooling (diagnostic : Frame.State) (reason : Tooling)

/-- Recognize the source's 23-byte EIP-7702 designator. -/
def isDelegation (code : ByteArray) : Bool :=
  code.size == 23 && code.data.toList.take 3 == [0xef, 0x01, 0x00]

/-- Prepare a nondelegated CALL in source order. -/
def prepare (s : Frame.State) (r : Frame.CallRequest) : Result :=
  let address := Frame.balanceAddress r.address
  let warm := s.warmAddresses.contains address
  let accessCost := if warm then 100 else 3000
  let memoryCost := Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat
    r.outputOffset.toNat r.outputSize.toNat
  let transferCost := if r.value == 0 then 0 else 11300
  let cost := accessCost + transferCost + memoryCost
  if s.gas < cost then .outOfGas s else
  let touched := if warm then s.warmAddresses else address :: s.warmAddresses
  let first := TransactionTracker.getAccount s.tracker address
  let accessed := { s with warmAddresses := touched, tracker := first.2 }
  match TransactionAccount.getCode first.2 first.1.codeHash with
  | none => .tooling accessed .missingCode
  | some ownCode =>
    if isDelegation ownCode then .tooling accessed .delegation else
    let second := TransactionTracker.getAccount first.2 address
    match TransactionAccount.getCode second.2 second.1.codeHash with
    | none => .tooling { accessed with tracker := second.2 } .missingCode
    | some code =>
      let valueNonzero := r.value != 0
      let aliveRead := if valueNonzero then TransactionTracker.getAccountOptional second.2 address
        else (none, second.2)
      let newAccount := valueNonzero && (match aliveRead.1 with
        | none => true
        | some account => account == World.emptyAccount)
      let charged := { accessed with gas := s.gas - cost, tracker := aliveRead.2 }
      let meterResult := if newAccount then Gas.StateMeter.chargeState (Frame.stateMeter charged) 183600
        else .ok (Frame.stateMeter charged)
      match meterResult with
      | .error _ => .outOfGas charged
      | .ok meter =>
        let charged := Frame.withStateMeter charged meter
        let grant := Gas.Call.calculate r.value.toNat r.gas.toNat charged.gas 0 0 2300
        let firstMemory := Memory.Allocation.expand s.memory r.inputOffset.toNat r.inputSize.toNat
        let memory := Memory.Allocation.expand firstMemory r.outputOffset.toNat r.outputSize.toNat
        let memoryValid : Memory.Allocation.Valid memory :=
          Memory.Allocation.expand_valid_for_frame firstMemory r.outputOffset.toNat r.outputSize.toNat
            (Memory.Allocation.expand_valid_for_frame s.memory r.inputOffset.toNat r.inputSize.toNat s.memoryValid)
        let senderRead := TransactionTracker.getAccount charged.tracker s.context.environment.currentTarget
        let parent := { charged with
          gas := charged.gas - grant.cost, tracker := senderRead.2,
          memory := memory, memoryValid := memoryValid, returnData := ByteArray.empty,
          stateGas := { charged.stateGas with reservoir := 0 } }
        .ready ⟨parent, r, address, code, grant.child, charged.stateGas.reservoir,
          newAccount, senderRead.1.balance.toNat < r.value.toNat⟩

end EthLib.EVM.CallPreparation
