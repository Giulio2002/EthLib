module

public import EthLib.EVM.Frame

/-!
# Fuel-bounded frame execution

Fuel bounds tooling work and is not EVM gas.
Running out of fuel does not produce an exceptional halt.
-/

@[expose] public section
namespace EthLib.EVM.Runner

/-- A bounded run either reaches a terminal result or exhausts its fuel. -/
inductive Result where
  | stopped (state : Frame.State)
  | returned (state : Frame.State) (output : ByteArray)
  | reverted (input : Frame.State) (gas : Nat) (output : ByteArray)
  | exception (input : Frame.State) (reason : Frame.Exception)
  | unsupported (input : Frame.State) (opcode : Opcode)
  | exhausted (state : Frame.State)

/-- The frame carried by a runner result. -/
def Result.frame : Result → Frame.State
  | .stopped s | .returned s _ | .reverted s _ _ | .exception s _ | .unsupported s _ | .exhausted s => s

/-- Project a bounded result to a protocol boundary when one exists.

Cancun `vm/interpreter.py`, `process_message`, clears gas on exceptional halt.
Fuel exhaustion and unsupported instructions are tooling outcomes.
-/
def settle : Result → Option Frame.Boundary
  | .stopped s => some (.stopped s.gas)
  | .returned s output => some (.returned s.gas output)
  | .reverted _ gas output => some (.reverted gas output)
  | .exception _ e => some (.exceptional 0 e)
  | .unsupported _ _ | .exhausted _ => none

/-- Execute at most `fuel` frame steps. -/
def run : Nat → Frame.State → Result
  | 0, s => .exhausted s
  | fuel + 1, s =>
    match Frame.step s with
    | .continue next => run fuel next
    | .stop next => .stopped next
    | .returned next output => .returned next output
    | .revert input gas output => .reverted input gas output
    | .exception input reason => .exception input reason
    | .unsupported input op => .unsupported input op
    | .callRequest input _ => .unsupported input .call
    | .staticCallRequest input _ => .unsupported input .staticcall

end EthLib.EVM.Runner
