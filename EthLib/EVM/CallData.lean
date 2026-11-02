module

public import EthLib.EVM.PushImmediate

/-!
# Call data observations

Cancun execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`,
`vm.instructions.environment.calldataload` and `vm.memory.buffer_read` define the read.
This module does not execute instructions.
-/

@[expose] public section
namespace EthLib.EVM.CallData

/-- Immutable input bytes for a message. -/
structure Context where
  data : ByteArray

/-- Read exactly `length` bytes from a buffer, padding past its end with zeros.

Cancun `vm/memory.py`, `buffer_read` uses natural addition for the end.
The caller must authorize the requested length before constructing this list.
-/
def readRange (data : ByteArray) (offset length : Nat) : List UInt8 :=
  (List.range length).map (fun i => PushImmediate.byteAt data (offset + i))

/-- Read 32 bytes from the full word offset, padding on the right with zeros. -/
def bytes (ctx : Context) (offset : Word) : List UInt8 :=
  (List.range 32).map (fun i => PushImmediate.byteAt ctx.data (offset.toNat + i))

/-- Interpret the bytes as a big-endian word. -/
def load (ctx : Context) (offset : Word) : Word :=
  BitVec.ofNat 256 ((bytes ctx offset).foldl (fun n b => 256 * n + b.toNat) 0)

end EthLib.EVM.CallData
