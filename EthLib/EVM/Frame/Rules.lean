module

public import EthLib.EVM.Frame

/-!
# Frame transition rules

These rules state stack and gas conditions without invoking the executable step.
The source is Cancun execution-specs revision
`fd9298410ec7218838c8348f69c1eb633f1797dc`, `vm/interpreter.py`,
`vm/instructions/stack.py`, `arithmetic.py`, `comparison.py`, `bitwise.py`, and `control_flow.py`.
-/

@[expose] public section
namespace EthLib.EVM.Frame

/-- The instruction at an in-bounds program counter. -/
def At (s : State) (op : Option Opcode) : Prop :=
  ∃ h : s.pc < s.code.size, Opcode.decode s.code[s.pc] = op

/-- Assigned opcodes for which this subset has no execution rule. -/
def Unsupported : Opcode → Prop
  | .addmod | .mulmod | .exp | .shl | .shr | .sar | .byte | .signextend | .lt | .gt | .slt | .sgt | .eq | .iszero | .and | .or | .xor | .not | .stop | .invalid | .add | .mul | .sub | .div | .mod | .sdiv | .smod | .pop | .push _ | .dup _ | .swap _ => False
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
  | addmodEmpty (s) : At s (some .addmod) → s.stack.val.length < 3 →
      Rule s (.exception s .stackUnderflow)
  | addmodGas (s x y m xs) : At s (some .addmod) → s.stack.val = x :: y :: m :: xs → s.gas < 8 →
      Rule s (.exception s .outOfGas)
  | addmod (s t x y m xs) : At s (some .addmod) → s.stack.val = x :: y :: m :: xs → 8 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 8) (Word.addmod x y m :: xs) → Rule s (.continue t)
  | mulmodEmpty (s) : At s (some .mulmod) → s.stack.val.length < 3 →
      Rule s (.exception s .stackUnderflow)
  | mulmodGas (s x y m xs) : At s (some .mulmod) → s.stack.val = x :: y :: m :: xs → s.gas < 8 →
      Rule s (.exception s .outOfGas)
  | mulmod (s t x y m xs) : At s (some .mulmod) → s.stack.val = x :: y :: m :: xs → 8 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 8) (Word.mulmod x y m :: xs) → Rule s (.continue t)
  | expEmpty (s) : At s (some .exp) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | expGas (s x y xs) : At s (some .exp) → s.stack.val = x :: y :: xs → s.gas < Gas.expCost y →
      Rule s (.exception s .outOfGas)
  | exp (s t x y xs) : At s (some .exp) → s.stack.val = x :: y :: xs → Gas.expCost y ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - Gas.expCost y) (Word.exp x y :: xs) → Rule s (.continue t)
  | mulEmpty (s) : At s (some .mul) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | mulGas (s x y xs) : At s (some .mul) → s.stack.val = x :: y :: xs → s.gas < 5 →
      Rule s (.exception s .outOfGas)
  | mul (s t x y xs) : At s (some .mul) → s.stack.val = x :: y :: xs → 5 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 5) (Word.mul x y :: xs) → Rule s (.continue t)
  | subEmpty (s) : At s (some .sub) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | subGas (s x y xs) : At s (some .sub) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | sub (s t x y xs) : At s (some .sub) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.sub x y :: xs) → Rule s (.continue t)
  | divEmpty (s) : At s (some .div) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | divGas (s x y xs) : At s (some .div) → s.stack.val = x :: y :: xs → s.gas < 5 →
      Rule s (.exception s .outOfGas)
  | div (s t x y xs) : At s (some .div) → s.stack.val = x :: y :: xs → 5 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 5) (Word.div x y :: xs) → Rule s (.continue t)
  | modEmpty (s) : At s (some .mod) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | modGas (s x y xs) : At s (some .mod) → s.stack.val = x :: y :: xs → s.gas < 5 →
      Rule s (.exception s .outOfGas)
  | mod (s t x y xs) : At s (some .mod) → s.stack.val = x :: y :: xs → 5 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 5) (Word.mod x y :: xs) → Rule s (.continue t)
  | sdivEmpty (s) : At s (some .sdiv) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | sdivGas (s x y xs) : At s (some .sdiv) → s.stack.val = x :: y :: xs → s.gas < 5 →
      Rule s (.exception s .outOfGas)
  | sdiv (s t x y xs) : At s (some .sdiv) → s.stack.val = x :: y :: xs → 5 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 5) (Word.sdiv x y :: xs) → Rule s (.continue t)
  | smodEmpty (s) : At s (some .smod) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | smodGas (s x y xs) : At s (some .smod) → s.stack.val = x :: y :: xs → s.gas < 5 →
      Rule s (.exception s .outOfGas)
  | smod (s t x y xs) : At s (some .smod) → s.stack.val = x :: y :: xs → 5 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 5) (Word.smod x y :: xs) → Rule s (.continue t)
  | ltEmpty (s) : At s (some .lt) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | ltGas (s x y xs) : At s (some .lt) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | lt (s t x y xs) : At s (some .lt) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.ltResult x y :: xs) → Rule s (.continue t)
  | gtEmpty (s) : At s (some .gt) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | gtGas (s x y xs) : At s (some .gt) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | gt (s t x y xs) : At s (some .gt) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.gtResult x y :: xs) → Rule s (.continue t)
  | sltEmpty (s) : At s (some .slt) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | sltGas (s x y xs) : At s (some .slt) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | slt (s t x y xs) : At s (some .slt) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.sltResult x y :: xs) → Rule s (.continue t)
  | sgtEmpty (s) : At s (some .sgt) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | sgtGas (s x y xs) : At s (some .sgt) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | sgt (s t x y xs) : At s (some .sgt) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.sgtResult x y :: xs) → Rule s (.continue t)
  | eqEmpty (s) : At s (some .eq) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | eqGas (s x y xs) : At s (some .eq) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | eq (s t x y xs) : At s (some .eq) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.eqResult x y :: xs) → Rule s (.continue t)
  | andEmpty (s) : At s (some .and) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | andGas (s x y xs) : At s (some .and) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | and (s t x y xs) : At s (some .and) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.bitwiseAnd x y :: xs) → Rule s (.continue t)
  | shlEmpty (s) : At s (some .shl) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | shlGas (s x y xs) : At s (some .shl) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | shl (s t x y xs) : At s (some .shl) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.shl x y :: xs) → Rule s (.continue t)
  | shrEmpty (s) : At s (some .shr) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | shrGas (s x y xs) : At s (some .shr) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | shr (s t x y xs) : At s (some .shr) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.shr x y :: xs) → Rule s (.continue t)
  | sarEmpty (s) : At s (some .sar) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | sarGas (s x y xs) : At s (some .sar) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | sar (s t x y xs) : At s (some .sar) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.sar x y :: xs) → Rule s (.continue t)
  | byteEmpty (s) : At s (some .byte) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | byteGas (s x y xs) : At s (some .byte) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | byte (s t x y xs) : At s (some .byte) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.byte x y :: xs) → Rule s (.continue t)
  | signextendEmpty (s) : At s (some .signextend) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | signextendGas (s x y xs) : At s (some .signextend) → s.stack.val = x :: y :: xs → s.gas < 5 →
      Rule s (.exception s .outOfGas)
  | signextend (s t x y xs) : At s (some .signextend) → s.stack.val = x :: y :: xs → 5 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 5) (Word.signextend x y :: xs) → Rule s (.continue t)
  | orEmpty (s) : At s (some .or) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | orGas (s x y xs) : At s (some .or) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | or (s t x y xs) : At s (some .or) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.bitwiseOr x y :: xs) → Rule s (.continue t)
  | xorEmpty (s) : At s (some .xor) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | xorGas (s x y xs) : At s (some .xor) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | xor (s t x y xs) : At s (some .xor) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.bitwiseXor x y :: xs) → Rule s (.continue t)
  | iszeroEmpty (s) : At s (some .iszero) → s.stack.val = [] → Rule s (.exception s .stackUnderflow)
  | iszeroGas (s x xs) : At s (some .iszero) → s.stack.val = x :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | iszero (s t x xs) : At s (some .iszero) → s.stack.val = x :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.iszeroResult x :: xs) → Rule s (.continue t)
  | notEmpty (s) : At s (some .not) → s.stack.val = [] → Rule s (.exception s .stackUnderflow)
  | notGas (s x xs) : At s (some .not) → s.stack.val = x :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | not (s t x xs) : At s (some .not) → s.stack.val = x :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.bitwiseNot x :: xs) → Rule s (.continue t)
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
