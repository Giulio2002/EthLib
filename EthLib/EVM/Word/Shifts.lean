module

public import EthLib.EVM.Word.SignedDivMod

/-!
# EVM shift results

Cancun execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`,
`vm/instructions/bitwise.py`, functions `bitwise_shl`, `bitwise_shr` and
`bitwise_sar`, gives these result rules.
EIP-145, Specification, and the Shanghai Yellow Paper revision
`efc5f9a1f356cba376c978eedb63cb0363c2aa85`, Appendix H.2, specify them too.
The count is the first popped word and the value is the second.
These functions do not execute an instruction.
-/

@[expose] public section

namespace EthLib.EVM.Word

/-- Logical left shift, with a full-width count. -/
def shl (count value : Word) : Word :=
  if count.toNat < 256 then BitVec.ofNat 256 (value.toNat * 2 ^ count.toNat) else 0

/-- Logical right shift, with a full-width count. -/
def shr (count value : Word) : Word :=
  if count.toNat < 256 then BitVec.ofNat 256 (value.toNat / 2 ^ count.toNat) else 0

/-- Arithmetic right shift uses floor division on signed integers. -/
def sar (count value : Word) : Word :=
  if count.toNat < 256 then ofSigned (signed value / (2 ^ count.toNat : Int))
  else if signed value < 0 then ofSigned (-1) else 0

end EthLib.EVM.Word
