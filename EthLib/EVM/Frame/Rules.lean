module

public import EthLib.EVM.Frame

/-!
# Frame transition rules

These rules state stack and gas conditions without invoking the executable step.
The source is Cancun execution-specs revision
`fd9298410ec7218838c8348f69c1eb633f1797dc`, `vm/interpreter.py`,
`vm/instructions/stack.py`, `arithmetic.py`, and `control_flow.py`.
-/

@[expose] public section
namespace EthLib.EVM.Frame

/-- The instruction at an in-bounds program counter. -/
def At (s : State) (op : Option Opcode) : Prop :=
  ∃ h : s.pc < s.code.size, Opcode.decode s.code[s.pc] = op

/-- Assigned opcodes for which this subset has no execution rule. -/
def Unsupported : Opcode → Prop
  | .stop | .invalid | .add | .pop | .push _ | .dup _ | .swap _ => False
  | _ => True

/-- Exact fields of a continuing frame, including fields untouched by this slice. -/
def Advances (s t : State) (pc gas : Nat) (xs : List Word) : Prop :=
  t.code = s.code ∧ t.memory = s.memory ∧ t.pc = pc ∧ t.gas = gas ∧ t.stack.val = xs

/-- Source-oriented rules for one frame transition. -/
inductive Rule : State → Outcome → Prop where
  | endCode (s) : s.code.size ≤ s.pc → Rule s (.stop s)
  | stop (s) : At s (some .stop) → Rule s (.stop { s with pc := s.pc + 1 })
  | invalid (s) : At s none ∨ At s (some .invalid) → Rule s (.exception s .invalidOpcode)
  | unsupported (s op) : At s (some op) → Unsupported op → Rule s (.unsupported s op)
  | pushGas (s n) : At s (some (.push n)) → s.gas < (if n.val = 0 then 2 else 3) →
      Rule s (.exception s .outOfGas)
  | pushFull (s n) : At s (some (.push n)) → (if n.val = 0 then 2 else 3) ≤ s.gas →
      s.stack.val.length = 1024 → Rule s (.exception s .stackOverflow)
  | push (s t n) : At s (some (.push n)) → (if n.val = 0 then 2 else 3) ≤ s.gas →
      s.stack.val.length < 1024 →
      Advances s t (PushImmediate.nextPC s.pc n) (s.gas - (if n.val = 0 then 2 else 3))
        (PushImmediate.value s.code s.pc n :: s.stack.val) → Rule s (.continue t)
  | popEmpty (s) : At s (some .pop) → s.stack.val = [] → Rule s (.exception s .stackUnderflow)
  | popGas (s x xs) : At s (some .pop) → s.stack.val = x :: xs → s.gas < 2 →
      Rule s (.exception s .outOfGas)
  | pop (s t x xs) : At s (some .pop) → s.stack.val = x :: xs → 2 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 2) xs → Rule s (.continue t)
  | addEmpty (s) : At s (some .add) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | addGas (s x y xs) : At s (some .add) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | add (s t x y xs) : At s (some .add) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.add x y :: xs) → Rule s (.continue t)
  | dupGas (s i) : At s (some (.dup i)) → s.gas < 3 → Rule s (.exception s .outOfGas)
  | dupEmpty (s i) : At s (some (.dup i)) → 3 ≤ s.gas → s.stack.val.length ≤ i.val →
      Rule s (.exception s .stackUnderflow)
  | dupFull (s i) : At s (some (.dup i)) → 3 ≤ s.gas → i.val < s.stack.val.length →
      s.stack.val.length = 1024 → Rule s (.exception s .stackOverflow)
  | dup (s t i) (h : i.val < s.stack.val.length) : At s (some (.dup i)) → 3 ≤ s.gas →
      s.stack.val.length < 1024 →
      Advances s t (s.pc + 1) (s.gas - 3) (s.stack.val[i.val] :: s.stack.val) →
      Rule s (.continue t)
  | swapGas (s i) : At s (some (.swap i)) → s.gas < 3 → Rule s (.exception s .outOfGas)
  | swapEmpty (s i) : At s (some (.swap i)) → 3 ≤ s.gas → s.stack.val.length ≤ i.val + 1 →
      Rule s (.exception s .stackUnderflow)
  | swap (s t i) (h : i.val + 1 < s.stack.val.length) : At s (some (.swap i)) → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3)
        ((s.stack.val.set 0 s.stack.val[i.val + 1]).set (i.val + 1) (s.stack.val[0]'(by omega))) →
      Rule s (.continue t)

end EthLib.EVM.Frame
