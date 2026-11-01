module

public import EthLib.EVM.Word

/-!
Unsigned result equations from the Shanghai Yellow Paper, Appendix H.2, DIV and MOD.
The first argument is the first-popped numerator; the second is the divisor.
Only arithmetic results are modeled.
- Escape from Lean's natural remainder at zero is explicit for MOD.
- The Cancun execution specification at revision
  `fd9298410ec7218838c8348f69c1eb633f1797dc`, `div` and `mod`,
  uses the same operand order and zero-divisor results.
-/

@[expose] public section

namespace EthLib.EVM.Word

/-- Unsigned quotient, with zero returned for a zero divisor. -/
def div (numerator divisor : Word) : Word :=
  if divisor.toNat = 0 then 0 else BitVec.ofNat 256 (numerator.toNat / divisor.toNat)

/-- Unsigned remainder, with zero returned for a zero divisor. -/
def mod (numerator divisor : Word) : Word :=
  if divisor.toNat = 0 then 0 else BitVec.ofNat 256 (numerator.toNat % divisor.toNat)

end EthLib.EVM.Word
