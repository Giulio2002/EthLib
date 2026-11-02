module

public import EthLib.EVM.Stack
public import EthLib.EVM.PushImmediate
public import EthLib.EVM.JumpDest
public import EthLib.EVM.Gas
public import EthLib.EVM.Memory.Invariant
public import EthLib.EVM.Word.AddMulMod
public import EthLib.EVM.Word.Exp
public import EthLib.EVM.Word.DivMod
public import EthLib.EVM.Word.SignedDivMod
public import EthLib.EVM.Word.Comparisons
public import EthLib.EVM.Word.Bitwise
public import EthLib.EVM.Word.Shifts
public import EthLib.EVM.Word.ByteSignExtend

/-!
# Cancun frame subset

The instruction rules come from Cancun execution-specs revision
`fd9298410ec7218838c8348f69c1eb633f1797dc`, `vm/interpreter.py`,
`vm/instructions/stack.py`, `arithmetic.py`, `comparison.py`, `bitwise.py`,
`control_flow.py`, `memory.py`, and `vm/gas.py`.
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
  | invalidOpcode | invalidJumpDestination | outOfGas | stackUnderflow | stackOverflow
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

/-- Total conversion for frame observations.

Values at least `2^256` are an extension beyond the source U256 domain.
-/
def observationWord (n : Nat) : Word := BitVec.ofNat 256 n

/-- Charge before pushing an observation.

Cancun `control_flow.py`, `pc` and `gas_left`, and `memory.py`, `msize`,
charge before calling `stack.py`, `push`.
`gas.py` gives each instruction the cost `BASE`, or two gas.
-/
def observe (s : State) (value : Nat → Nat) : Outcome :=
  charge s 2 fun gas =>
    match Stack.push s.stack (observationWord (value gas)) with
    | .error e => failStack s e
    | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }

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
    -- Cancun `control_flow.py`, `jump`: pop, charge, then validate the full word.
    | some .jump =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (destination, stack) =>
        charge s 8 fun gas =>
          if JumpDest.contains s.code destination.toNat then
            .continue { s with stack, gas, pc := destination.toNat }
          else .exception s .invalidJumpDestination
    -- Cancun `control_flow.py`, `jumpi`: the destination is popped first.
    | some .jumpi =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (destination, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (condition, stack) =>
          charge s 10 fun gas =>
            if condition.toNat = 0 then
              .continue { s with stack, gas, pc := s.pc + 1 }
            else if JumpDest.contains s.code destination.toNat then
              .continue { s with stack, gas, pc := destination.toNat }
            else .exception s .invalidJumpDestination
    -- Cancun `control_flow.py`, `jumpdest`: charge before advancing.
    | some .jumpdest =>
      charge s 1 fun gas => .continue { s with gas, pc := s.pc + 1 }
    | some .pc => observe s (fun _ => s.pc)
    | some .msize => observe s (fun _ => Memory.Allocation.byteSize s.memory)
    | some .gas => observe s id
    -- Cancun `memory.py`, `mload`: pop, charge, expand, then read.
    | some .mload =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (offset, stack) =>
        charge s (3 + Gas.rangeCost s.memory.words offset.toNat 32) fun gas =>
          let result := Memory.Allocation.loadWord s.memory offset.toNat
          match Stack.push stack result.1 with
          | .error e => failStack s e
          | .ok stack => .continue { s with stack, gas, pc := s.pc + 1, memory := result.2, memoryValid := Memory.Allocation.expand_valid_for_frame _ _ _ s.memoryValid }
    -- Cancun `memory.py`, `mstore`: the offset is popped before the value.
    | some .mstore =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (offset, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (value, stack) =>
          charge s (3 + Gas.rangeCost s.memory.words offset.toNat 32) fun gas =>
            .continue { s with stack, gas, pc := s.pc + 1, memory := Memory.Allocation.storeWord s.memory offset.toNat value, memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid }
    -- Cancun `memory.py`, `mstore8`: only the low byte is written.
    | some .mstore8 =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (offset, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (value, stack) =>
          charge s (3 + Gas.rangeCost s.memory.words offset.toNat 1) fun gas =>
            .continue { s with stack, gas, pc := s.pc + 1, memory := Memory.Allocation.storeByte s.memory offset.toNat value, memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid }
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
    -- Cancun `arithmetic.py`, `addmod`: pop three operands before charging.
    | some .addmod =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          match Stack.pop stack with
          | .error e => failStack s e
          | .ok (m, stack) =>
            charge s 8 fun gas =>
              match Stack.push stack (Word.addmod a b m) with
              | .error e => failStack s e
              | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `arithmetic.py`, `mulmod`: pop three operands before charging.
    | some .mulmod =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          match Stack.pop stack with
          | .error e => failStack s e
          | .ok (m, stack) =>
            charge s 8 fun gas =>
              match Stack.push stack (Word.mulmod a b m) with
              | .error e => failStack s e
              | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `arithmetic.py`, `exp`: base is popped before exponent.
    | some .exp =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (base, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (exponent, stack) =>
          charge s (Gas.expCost exponent) fun gas =>
            match Stack.push stack (Word.exp base exponent) with
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
    -- Cancun `comparison.py`, `less_than`: pop both operands before charging gas.
    | some .lt =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.ltResult a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `comparison.py`, `greater_than`: pop both operands before charging gas.
    | some .gt =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.gtResult a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `comparison.py`, `signed_less_than`: pop both operands before charging gas.
    | some .slt =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.sltResult a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `comparison.py`, `signed_greater_than`: pop both operands before charging gas.
    | some .sgt =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.sgtResult a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `comparison.py`, `equal`: pop both operands before charging gas.
    | some .eq =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.eqResult a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `bitwise.py`, `bitwise_and`: pop both operands before charging gas.
    | some .and =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.bitwiseAnd a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `bitwise.py`, `bitwise_or`: pop both operands before charging gas.
    | some .or =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.bitwiseOr a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `bitwise.py`, `bitwise_xor`: pop both operands before charging gas.
    | some .xor =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.bitwiseXor a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `bitwise.py`, `bitwise_shl`: pop the index or count first.
    | some .shl =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.shl a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `bitwise.py`, `bitwise_shr`: pop the index or count first.
    | some .shr =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.shr a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `bitwise.py`, `bitwise_sar`: pop the index or count first.
    | some .sar =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.sar a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `bitwise.py`, `get_byte`: pop the index or count first.
    | some .byte =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.byte a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `arithmetic.py`, `signextend`: pop the index or count first.
    | some .signextend =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 5 fun gas =>
            match Stack.push stack (Word.signextend a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `comparison.py`, `is_zero`: pop the operand before charging gas.
    | some .iszero =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        charge s 3 fun gas =>
          match Stack.push stack (Word.iszeroResult a) with
          | .error e => failStack s e
          | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `bitwise.py`, `bitwise_not`: pop the operand before charging gas.
    | some .not =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        charge s 3 fun gas =>
          match Stack.push stack (Word.bitwiseNot a) with
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
