module

public import EthLib.EVM.PushImmediate

/-!
# Amsterdam stack instruction immediates

The source is execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`,
Amsterdam `vm.stack.decode_single` and `vm.stack.decode_pair`.
The reader uses the zero-padding rule of `vm.memory.buffer_read`.
These functions do not execute instructions.
-/

@[expose] public section

namespace EthLib.EVM.StackImmediate

/-- Read the byte following an instruction, with zero beyond the code. -/
def byte (code : ByteArray) (pc : Nat) : UInt8 :=
  PushImmediate.byteAt code (pc + 1)

/-- Decode a DUPN or SWAPN immediate, rejecting the forbidden bytes. -/
def decodeSingle (x : UInt8) : Option Nat :=
  if x.toNat ≤ 90 ∨ 128 ≤ x.toNat then
    some ((x.toNat + 145) % 256)
  else none

/-- Decode an EXCHANGE immediate, rejecting the forbidden bytes. -/
def decodePair (x : UInt8) : Option (Nat × Nat) :=
  if x.toNat ≤ 81 ∨ 128 ≤ x.toNat then
    let k := Nat.xor x.toNat 143
    let q := k / 16
    let r := k % 16
    if q < r then some (q + 1, r + 1) else some (r + 1, 29 - q)
  else none

end EthLib.EVM.StackImmediate
