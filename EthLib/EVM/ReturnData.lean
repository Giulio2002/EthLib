module

public import EthLib.EVM.Word

/-!
# Return data ranges

Cancun execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`,
`vm/instructions/environment.py`, `returndatacopy`, checks the source range
using natural addition before slicing the buffer.
This module does not charge gas or execute instructions.
-/

@[expose] public section
namespace EthLib.EVM.ReturnData

/-- A source range extends beyond the return-data buffer. -/
inductive Error where
  | outOfBounds
  deriving DecidableEq, Repr

/-- Read a source range without padding.

The caller must charge for the copy before constructing the returned list.
-/
def read (data : ByteArray) (offset length : Nat) : Except Error (List UInt8) :=
  if offset + length ≤ data.size then
    .ok ((data.data.toList.drop offset).take length)
  else
    .error .outOfBounds

end EthLib.EVM.ReturnData
