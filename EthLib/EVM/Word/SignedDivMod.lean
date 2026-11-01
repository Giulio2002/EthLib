module

public import EthLib.EVM.Word

/-!
# Signed EVM arithmetic results

The Shanghai Yellow Paper, revision `efc5f9a1f356cba376c978eedb63cb0363c2aa85`,
Appendix H.2, SDIV and SMOD, treats both operands as signed two's-complement words.
The Cancun execution specification revision `fd9298410ec7218838c8348f69c1eb633f1797dc`
gives the same rules in `vm/instructions/arithmetic.py`, functions `sdiv` and `smod`.
The first operand is the first popped word, and is the numerator.
Only arithmetic results are modeled here.
-/

@[expose] public section

namespace EthLib.EVM.Word

/-- Interpret a word as a signed two's-complement integer. -/
def signed (a : Word) : Int := a.toInt

/-- Encode any integer modulo `2^256`.

Unlike `Word.ofNat`, this intentionally wraps out-of-range inputs.
-/
def ofSigned (a : Int) : Word := BitVec.ofInt 256 a

/-- Signed division truncated toward zero, with wrapped overflow. -/
def sdiv (numerator divisor : Word) : Word := BitVec.sdiv numerator divisor

/-- Signed remainder with the numerator's sign and zero for a zero divisor. -/
def smod (numerator divisor : Word) : Word :=
  if divisor = 0 then 0 else numerator.srem divisor

end EthLib.EVM.Word
