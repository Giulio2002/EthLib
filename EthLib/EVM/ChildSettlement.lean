module

public import EthLib.EVM.Runner
public import EthLib.EVM.ChildSettlement.Core

/-!
# Child-frame settlement

Amsterdam execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`,
`vm/interpreter.py` `process_call`, `vm/__init__.py` `incorporate_child`,
and `vm/instructions/system.py` `generic_call`.
The caller must supply the parent after withholding the child grants and must put
the tracker snapshot corresponding to this parent on the child's stack before execution.
The snapshot must remain at the top, and the child must retain the same transaction
parent and the diagnostic read and creation metadata accumulated before entry.
The total functions do not check these caller-supplied ownership conditions.
At source-valid child entry, the parent reservoir has been drained into the grant.
The child reservoir and baseline both equal that grant.
The child spill, committed spill and refund counter start at zero.
The total functions also describe inputs that do not satisfy these conditions.
This incorporation precedes the failed-child account-creation refund in `generic_call`.
A caller that charged a new account must apply that refund separately.
The return-data choice is the CALL-style choice; successful CREATE clears it.
This module does not implement CALL, CREATE, child entry, or output-memory copying.
-/

@[expose] public section
namespace EthLib.EVM.ChildSettlement

/-- Tooling results do not settle a child. -/
def settle (parent : Frame.State) : Runner.Result → Except Error Frame.State
  | .stopped s => settleChild parent s true s.gas ByteArray.empty
  | .returned s output => settleChild parent s true s.gas output
  | .reverted s gas output => settleChild parent s false (gas + s.stateGas.spilled) output
  | .exception _ .missingCode | .exception _ .missingStorageAccount => .error .toolingOutcome
  | .exception s _ => settleChild parent s false 0 ByteArray.empty
  | .unsupported _ _ | .exhausted _ => .error .toolingOutcome

end EthLib.EVM.ChildSettlement
