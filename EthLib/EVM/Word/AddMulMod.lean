module

public import EthLib.EVM.Word

/-!
# Modular arithmetic results

Cancun execution-specs `arithmetic.py`, `addmod` and `mulmod`, at
`fd9298410ec7218838c8348f69c1eb633f1797dc` uses unbounded intermediates.
Yellow Paper revision `efc5f9a1f356cba376c978eedb63cb0363c2aa85`,
Appendix H.2, ADDMOD and MULMOD, specifies the same results.
The first two operands are arithmetic inputs and the third is the modulus.
-/

@[expose] public section

namespace EthLib.EVM.Word

/-- Full-precision sum reduced by the third operand, or zero for modulus zero. -/
def addmod (a b m : Word) : Word :=
  if m.toNat = 0 then 0 else BitVec.ofNat 256 ((a.toNat + b.toNat) % m.toNat)

/-- Full-precision product reduced by the third operand, or zero for modulus zero. -/
def mulmod (a b m : Word) : Word :=
  if m.toNat = 0 then 0 else BitVec.ofNat 256 ((a.toNat * b.toNat) % m.toNat)

end EthLib.EVM.Word
