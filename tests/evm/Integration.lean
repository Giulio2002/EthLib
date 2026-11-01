module
import EthLib.EVM

open EthLib.EVM

-- Exercise each result operation through the ordinary public import.
example : Word.ofNat 1 = .ok 1 := rfl
example : Word.add 1 2 = 3 := by decide
example : Word.sub 1 2 = -1 := by decide
example : Word.mul 2 3 = 6 := by decide
example : Word.div 7 3 = 2 := by decide
example : Word.mod 7 3 = 1 := by decide
example : Word.sdiv (Word.ofSigned (-7)) 3 = Word.ofSigned (-2) := by decide
example : Word.smod (Word.ofSigned (-7)) 3 = Word.ofSigned (-1) := by decide
example : Word.signed (Word.ofSigned (-1)) = -1 := by decide
example : Word.ltResult 1 2 = 1 := by decide
example : Word.gtResult 2 1 = 1 := by decide
example : Word.sltResult (-1) 0 = 1 := by decide
example : Word.sgtResult 0 (-1) = 1 := by decide
example : Word.eqResult 1 1 = 1 := by decide
example : Word.iszeroResult 0 = 1 := by decide
example : Word.bitwiseAnd 12 10 = 8 := by decide
example : Word.bitwiseOr 12 10 = 14 := by decide
example : Word.bitwiseXor 12 10 = 6 := by decide
example : Word.bitwiseNot 0 = -1 := by decide
example : Word.shl 8 1 = 256 := by decide
example : Word.shr 8 256 = 1 := by decide
example : Word.sar 1 (Word.ofSigned (-3)) = Word.ofSigned (-2) := by decide
example : Word.byte 30 (Word.shl 8 0xab) = 0xab := by decide
example : Word.signextend 0 255 = -1 := by decide
example : Word.addmod (-1) 1 3 = 1 := by decide
example : Word.mulmod (BitVec.ofNat 256 (2^255)) 2 3 = 1 := by decide
-- EXP computation is checked by the executable matrix in Exp.lean.
def expConsumer : Word := Word.exp 2 8
example : Word.ofBytesBE (Word.toBytesBE (Word.ofSigned (-1))) = .ok (Word.ofSigned (-1)) := rfl
