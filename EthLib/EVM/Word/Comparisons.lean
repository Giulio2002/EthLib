module

public import EthLib.EVM.Word.SignedDivMod

/-!
# EVM comparison results

The Shanghai Yellow Paper revision `efc5f9a1f356cba376c978eedb63cb0363c2aa85`,
Appendix H.2, gives LT, GT, SLT, SGT, EQ and ISZERO.
The Cancun execution specification revision `fd9298410ec7218838c8348f69c1eb633f1797dc`
gives them in `vm/instructions/comparison.py`.
The left operand is the first popped word.
Each result is the word 1 when the condition holds and 0 otherwise.
Only results are modeled here.
-/

@[expose] public section

namespace EthLib.EVM.Word

/-- Unsigned less-than result. -/
def ltResult (left right : Word) : Word := if left.toNat < right.toNat then 1 else 0

/-- Unsigned greater-than result. -/
def gtResult (left right : Word) : Word := if left.toNat > right.toNat then 1 else 0

/-- Signed less-than result. -/
def sltResult (left right : Word) : Word := if signed left < signed right then 1 else 0

/-- Signed greater-than result. -/
def sgtResult (left right : Word) : Word := if signed left > signed right then 1 else 0

/-- Equality result. -/
def eqResult (left right : Word) : Word := if left = right then 1 else 0

/-- Zero-test result. -/
def iszeroResult (x : Word) : Word := if x = 0 then 1 else 0

end EthLib.EVM.Word
