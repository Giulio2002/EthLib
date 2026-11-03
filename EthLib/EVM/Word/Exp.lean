module

public import EthLib.EVM.Word
public import EthLib.Execution.Precompiles.Modexp.Core

/-!
# EVM exponentiation result

Cancun execution-specs `exp`, revision `fd9298410ec7218838c8348f69c1eb633f1797dc`,
pops the base first and exponent second, and computes their power modulo `2^256`.
The Shanghai Yellow Paper, revision `efc5f9a1f356cba376c978eedb63cb0363c2aa85`,
Appendix H.2 gives the same EXP result.
This helper models the result only, not gas, stack effects or instruction execution.
-/

@[expose] public section

namespace EthLib.EVM.Word

/-- EXP's modular result, using square-and-multiply on the full exponent. -/
def exp (base exponent : Word) : Word :=
  BitVec.ofNat 256 (EthLib.Execution.Precompiles.Modexp.powMod base.toNat exponent.toNat modulus)

end EthLib.EVM.Word
