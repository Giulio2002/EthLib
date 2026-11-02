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
  | exception (input : Frame.State) (reason : Frame.Exception)
  | unsupported (input : Frame.State) (opcode : Opcode)
  | exhausted (state : Frame.State)

/-- The frame carried by a runner result. -/
def Result.frame : Result → Frame.State
  | .stopped s | .exception s _ | .unsupported s _ | .exhausted s => s

/-- Execute at most `fuel` frame steps. -/
def run : Nat → Frame.State → Result
  | 0, s => .exhausted s
  | fuel + 1, s =>
    match Frame.step s with
    | .continue next => run fuel next
    | .stop next => .stopped next
    | .exception input reason => .exception input reason
    | .unsupported input op => .unsupported input op

end EthLib.EVM.Runner
