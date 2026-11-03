module

public import EthLib.EVM.Word
public import EthLib.EVM.Memory.Allocation

/-!
# Word access to memory

Cancun execution-specs `vm/instructions/memory.py`, `mload`, `mstore` and `mstore8`:
https://github.com/ethereum/execution-specs/blob/fd9298410ec7218838c8348f69c1eb633f1797dc/src/ethereum/forks/cancun/vm/instructions/memory.py

These helpers model contents and logical allocation, not gas, stack or errors.
Addresses are natural numbers and do not wrap.
-/

@[expose] public section

namespace EthLib.EVM.Memory.Allocation

open EthLib.EVM

/-- Read a big-endian word and expand the logical memory. -/
def loadWord (s : State) (offset : Nat) : Word × State :=
  let result := read s offset 32
  (BitVec.ofNat 256 (EthLib.Execution.Precompiles.Modexp.bytesToNat result.1), result.2)

/-- Write all 32 big-endian bytes of a word. -/
def storeWord (s : State) (offset : Nat) (value : Word) : State :=
  write s offset value.toBytesBE.data.toList

/-- Write the least significant byte of a word. -/
def storeByte (s : State) (offset : Nat) (value : Word) : State :=
  write s offset [UInt8.ofNat value.toNat]

end EthLib.EVM.Memory.Allocation
