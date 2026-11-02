module

public import EthLib.EVM.Word

/-!
# BYTE and SIGNEXTEND results

The sources are Cancun execution-specs revision
`fd9298410ec7218838c8348f69c1eb633f1797dc`, `get_byte` and `signextend`,
and the Shanghai Yellow Paper revision
`efc5f9a1f356cba376c978eedb63cb0363c2aa85`, Appendix H.2.
The first argument is the byte index and the second is the value.
These functions model results only.
-/

@[expose] public section

namespace EthLib.EVM.Word

/-- Extract a byte, counting from the most significant byte. -/
def byte (index value : Word) : Word :=
  if index.toNat < 32 then
    BitVec.ofNat 256 (value.toNat / 2 ^ (8 * (31 - index.toNat)) % 256)
  else 0

/-- Extend the sign of the selected low bytes across the word. -/
def signextend (index value : Word) : Word :=
  if index.toNat < 32 then
    let width := 8 * (index.toNat + 1)
    let low := value.toNat % 2 ^ width
    if low < 2 ^ (width - 1) then
      BitVec.ofNat 256 low
    else
      BitVec.ofNat 256 (2 ^ 256 - 2 ^ width + low)
  else value

end EthLib.EVM.Word
