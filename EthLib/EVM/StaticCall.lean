module

public import EthLib.EVM.CallPreparation

/-!
# STATICCALL preparation

Amsterdam execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`,
`vm/instructions/system.py`, `staticcall`.
`Frame.staticCallEntry` has already popped the six operands.
This module prices the call, reads the callee code and withholds the child grants.
A delegation designator and missing code are the same tooling boundaries as for CALL.
-/

@[expose] public section
namespace EthLib.EVM.StaticCall

/-- State-independent execution gas checked before any state access. -/
def initialCost (s : Frame.State) (r : Frame.CallRequest) : Nat :=
  (if s.warmAddresses.contains (Frame.balanceAddress r.address) then 100 else 3000) +
  Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat r.outputOffset.toNat r.outputSize.toNat

/-- Prepare a nondelegated STATICCALL in source order.

The source differs from a zero-value CALL in three ways.
There is no transfer charge and no new-account state charge.
The access and memory costs enter `calculate_message_call_gas` as `extra_gas` and `memory_cost`.
There is no sender balance read, because no preflight balance check exists.
-/
def prepare (s : Frame.State) (r : Frame.CallRequest) : CallPreparation.Result :=
  let address := Frame.balanceAddress r.address
  let warm := s.warmAddresses.contains address
  let accessCost := if warm then 100 else 3000
  let memoryCost := Gas.pairCost s.memory.words r.inputOffset.toNat r.inputSize.toNat
    r.outputOffset.toNat r.outputSize.toNat
  -- `check_gas(evm, access_gas_cost + extend_memory.cost)`.
  if s.gas < accessCost + memoryCost then .outOfGas s else
  let touched := if warm then s.warmAddresses else address :: s.warmAddresses
  -- `calculate_delegation_cost` reads the callee code.
  let first := TransactionTracker.getAccount s.tracker address
  let accessed := { s with warmAddresses := touched, tracker := first.2 }
  match TransactionAccount.getCode first.2 first.1.codeHash with
  | none => .tooling accessed .missingCode
  | some ownCode =>
    if CallPreparation.isDelegation ownCode then .tooling accessed .delegation else
    -- `get_account(tx_state, code_address).code_hash` and `get_code`.
    let second := TransactionTracker.getAccount first.2 address
    match TransactionAccount.getCode second.2 second.1.codeHash with
    | none => .tooling { accessed with tracker := second.2 } .missingCode
    | some code =>
      let grant := Gas.Call.calculate 0 r.gas.toNat s.gas memoryCost accessCost 2300
      -- `charge_gas(evm, message_call_gas.cost + extend_memory.cost)`.
      if s.gas < grant.cost + memoryCost then .outOfGas { accessed with tracker := second.2 } else
      let firstMemory := Memory.Allocation.expand s.memory r.inputOffset.toNat r.inputSize.toNat
      let memory := Memory.Allocation.expand firstMemory r.outputOffset.toNat r.outputSize.toNat
      let memoryValid : Memory.Allocation.Valid memory :=
        Memory.Allocation.expand_valid_for_frame firstMemory r.outputOffset.toNat r.outputSize.toNat
          (Memory.Allocation.expand_valid_for_frame s.memory r.inputOffset.toNat r.inputSize.toNat s.memoryValid)
      -- `drain_state_gas_reservoir` hands the whole reservoir to the child.
      let parent := { accessed with
        gas := s.gas - (grant.cost + memoryCost), tracker := second.2,
        memory := memory, memoryValid := memoryValid, returnData := ByteArray.empty,
        stateGas := { s.stateGas with reservoir := 0 } }
      .ready ⟨parent, r, address, code, grant.child, s.stateGas.reservoir, false, false⟩

end EthLib.EVM.StaticCall
