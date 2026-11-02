module

public import EthLib.EVM.Word
public import EthLib.EVM.Opcode

/-!
# PUSH immediate data

The source is execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`,
Cancun `vm.instructions.stack.push_n` and `vm.memory.buffer_read`.
The byte reader extends their zero-padding rule to arbitrary natural offsets.
This module does not execute instructions.
-/

@[expose] public section

namespace EthLib.EVM.PushImmediate

/-- The immediate length of a PUSH instruction. -/
abbrev Length := Fin 33

/-- Read one byte, returning zero beyond the code. -/
def byteAt (code : ByteArray) (offset : Nat) : UInt8 :=
  if h : offset < code.size then code[offset] else 0

/-- The immediate bytes in code order, padded on the right with zeros. -/
def bytes (code : ByteArray) (pc : Nat) (length : Length) : List UInt8 :=
  (List.range length.val).map (fun i => byteAt code (pc + 1 + i))

/-- Interpret bytes in big-endian order. -/
def value (code : ByteArray) (pc : Nat) (length : Length) : Word :=
  BitVec.ofNat 256 ((bytes code pc length).foldl (fun n b => 256 * n + b.toNat) 0)

/-- The next program counter, in natural arithmetic. -/
def nextPC (pc : Nat) (length : Length) : Nat := pc + 1 + length.val

/-- The decoded data and next program counter of a PUSH instruction. -/
structure Result where
  /-- The immediate bytes, with missing bytes padded on the right. -/
  data : List UInt8
  /-- The unsigned big-endian value of the immediate. -/
  word : Word
  /-- The next position in natural arithmetic. -/
  next : Nat
  deriving DecidableEq, Repr

/-- Decode immediate data only for a PUSH opcode. -/
def decode (op : Opcode) (code : ByteArray) (pc : Nat) : Option Result :=
  match op with
  | .push length => some ⟨bytes code pc length, value code pc length, nextPC pc length⟩
  | _ => none

end EthLib.EVM.PushImmediate
