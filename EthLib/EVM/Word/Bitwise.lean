module

public import EthLib.EVM.Word

/-!
# EVM bitwise results

The result equations are from Yellow Paper revision
`efc5f9a1f356cba376c978eedb63cb0363c2aa85`, Appendix H.2,
"10s: Comparison & Bitwise Logic Operations", AND through NOT.
They also correspond to Cancun `bitwise_and`, `bitwise_or`, `bitwise_xor`,
and `bitwise_not` in execution-specs revision
`fd9298410ec7218838c8348f69c1eb633f1797dc`.
This is a human interpretation of those sources.
The proof module checks refinement of the definitions to stated mathematical equations.
It does not prove the interpretation of the sources or compiled runtime behavior.
Stack, gas, opcode execution and the interpreter are outside this module.
-/

@[expose] public section

namespace EthLib.EVM.Word

/-- The AND result. -/
def bitwiseAnd (a b : Word) : Word := a &&& b

/-- The OR result. -/
def bitwiseOr (a b : Word) : Word := a ||| b

/-- The XOR result. -/
def bitwiseXor (a b : Word) : Word := a ^^^ b

/-- The 256-bit complement. -/
def bitwiseNot (a : Word) : Word := ~~~a

end EthLib.EVM.Word
