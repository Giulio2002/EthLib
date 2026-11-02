module

public import EthLib.EVM.Memory

/-!
# Byte ranges

Cancun execution-specs `vm/memory.py`, `memory_read_bytes` and `memory_write`:
https://github.com/ethereum/execution-specs/blob/fd9298410ec7218838c8348f69c1eb633f1797dc/src/ethereum/forks/cancun/vm/memory.py

Cancun `vm/instructions/memory.py`, `mcopy`, reads before it writes:
https://github.com/ethereum/execution-specs/blob/fd9298410ec7218838c8348f69c1eb633f1797dc/src/ethereum/forks/cancun/vm/instructions/memory.py

The source expands memory before reading.
Here the sparse store supplies zeros outside its history.
This module models contents only, not allocation, gas, or opcode execution.
Natural addresses do not wrap.
-/

@[expose] public section

namespace EthLib.EVM.Memory

/-- Read a finite range in increasing address order. -/
def readRange (s : Store) (offset : Nat) : Nat → List UInt8
  | 0 => []
  | n + 1 => readByte s offset :: readRange s (offset + 1) n

/-- Write a finite list at consecutive addresses. -/
def writeRange (s : Store) (offset : Nat) : List UInt8 → Store
  | [] => s
  | b :: bs => writeByte (writeRange s (offset + 1) bs) offset b

/-- Copy a snapshot of the source range to the destination. -/
def copyRange (s : Store) (destination source : Nat) : Nat → Store
  | 0 => s
  | n + 1 => writeRange s destination (readRange s source (n + 1))

end EthLib.EVM.Memory
