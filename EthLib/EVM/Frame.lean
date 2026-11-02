module

public import EthLib.EVM.Stack
public import EthLib.EVM.PushImmediate
public import EthLib.EVM.Gas

/-!
# Cancun frame subset

The instruction rules come from Cancun execution-specs revision
`fd9298410ec7218838c8348f69c1eb633f1797dc`, `vm/interpreter.py`,
`vm/instructions/stack.py`, `arithmetic.py`, `control_flow.py`, and `vm/gas.py`.
An exception retains the input frame only as diagnostic context.
Its gas is zero at the message boundary; its stack is not a protocol final state.
Unsupported instructions are a tooling result and do not execute.
-/

@[expose] public section
namespace EthLib.EVM.Frame

/-- The fields used by this instruction subset. -/
structure State where
  code : ByteArray
  pc : Nat
  stack : Stack
  gas : Nat
  memory : Memory.Allocation.State
  memoryValid : Memory.Allocation.Valid memory

/-- Exceptional halts distinguished by their first failing check. -/
inductive Exception where
  | invalidOpcode | outOfGas | stackUnderflow | stackOverflow
  deriving DecidableEq, Repr

/-- A tooling stop for an assigned opcode outside this subset. -/
inductive Outcome where
  | continue (state : State)
  | stop (state : State)
  | exception (input : State) (reason : Exception)
  | unsupported (input : State) (opcode : Opcode)

def failStack (s : State) : StackError → Outcome
  | .underflow => .exception s .stackUnderflow
  | .overflow => .exception s .stackOverflow

def charge (s : State) (cost : Nat) (k : Nat → Outcome) : Outcome :=
  match Gas.charge s.gas cost with
  | .error _ => .exception s .outOfGas
  | .ok gas => k gas

/-- Execute one instruction or stop at the end of code. -/
def step (s : State) : Outcome :=
  if h : s.pc < s.code.size then
    match Opcode.decode s.code[s.pc] with
    | none | some .invalid => .exception s .invalidOpcode
    | some .stop => .stop { s with pc := s.pc + 1 }
    | some (.push n) =>
      charge s (if n.val = 0 then 2 else 3) fun gas =>
        match Stack.push s.stack (PushImmediate.value s.code s.pc n) with
        | .error e => failStack s e
        | .ok stack => .continue { s with stack, gas, pc := PushImmediate.nextPC s.pc n }
    | some .pop =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (_, stack) =>
        charge s 2 fun gas => .continue { s with stack, gas, pc := s.pc + 1 }
    | some .add =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.add a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    | some (.dup i) =>
      charge s 3 fun gas =>
        match Stack.dup s.stack i with
        | .error e => failStack s e
        | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    | some (.swap i) =>
      charge s 3 fun gas =>
        match Stack.swap s.stack i with
        | .error e => failStack s e
        | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    | some op => .unsupported s op
  else .stop s

/-- The frame carried by an outcome, including diagnostic input for failures. -/
def Outcome.frame : Outcome → State
  | .continue s | .stop s | .exception s _ | .unsupported s _ => s

/-- Message-boundary observations modeled by this subset. -/
inductive Boundary where
  | stopped (gas : Nat)
  | exceptional (gas : Nat) (reason : Exception)

/-- Project protocol gas only for terminal EVM outcomes.

Cancun `vm/interpreter.py`, `process_message`, burns all remaining gas on
`ExceptionalHalt` and clears output. World rollback is outside this subset.
-/
def settle : Outcome → Option Boundary
  | .stop s => some (.stopped s.gas)
  | .exception _ reason => some (.exceptional 0 reason)
  | .continue _ | .unsupported _ _ => none

end EthLib.EVM.Frame
