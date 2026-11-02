module

public import EthLib.EVM.Stack
public import EthLib.EVM.PushImmediate
public import EthLib.EVM.Gas
public import EthLib.EVM.Word.DivMod
public import EthLib.EVM.Word.SignedDivMod

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

/-- Frame outcomes include a typed revert for future semantics.

The restricted step never constructs a revert.
The carried frame is diagnostic and does not represent world-state rollback.
Unsupported instructions are tooling outcomes. -/
inductive Outcome where
  | continue (state : State)
  | stop (state : State)
  | revert (input : State) (gas : Nat) (output : ByteArray)
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
    -- Cancun `arithmetic.py`, `mul`: pop twice before charging `OPCODE_MUL`.
    | some .mul =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 5 fun gas =>
            match Stack.push stack (Word.mul a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `arithmetic.py`, `sub`: the first pop is the left operand.
    | some .sub =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.sub a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `arithmetic.py`, `div`: the first pop is the left operand.
    | some .div =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 5 fun gas =>
            match Stack.push stack (Word.div a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `arithmetic.py`, `mod`: the first pop is the left operand.
    | some .mod =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 5 fun gas =>
            match Stack.push stack (Word.mod a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `arithmetic.py`, `sdiv`: the first pop is the left operand.
    | some .sdiv =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 5 fun gas =>
            match Stack.push stack (Word.sdiv a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `arithmetic.py`, `smod`: the first pop is the left operand.
    | some .smod =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 5 fun gas =>
            match Stack.push stack (Word.smod a b) with
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
  | .continue s | .stop s | .revert s _ _ | .exception s _ | .unsupported s _ => s

/-- Message-boundary observations modeled by this subset. -/
inductive Boundary where
  | stopped (gas : Nat)
  | reverted (gas : Nat) (output : ByteArray)
  | exceptional (gas : Nat) (reason : Exception)

/-- Project the modeled observations for terminal EVM outcomes.

Cancun `vm/interpreter.py`, `process_message`, burns all remaining gas on
`ExceptionalHalt` and clears output.
A manually supplied revert retains its gas and output.
World rollback is outside this subset.
-/
def settle : Outcome → Option Boundary
  | .stop s => some (.stopped s.gas)
  | .revert _ gas output => some (.reverted gas output)
  | .exception _ reason => some (.exceptional 0 reason)
  | .continue _ | .unsupported _ _ => none

end EthLib.EVM.Frame
