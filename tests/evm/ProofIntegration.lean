module
import EthLib.EVM.Proofs

open EthLib.EVM
open EthLib.EVM.Proofs.Word

example (w : Word) : Word.ofBytesBE (Word.toBytesBE w) = .ok w := ofBytesBE_toBytesBE w
example (w : Word) : Word.sub w 0 = w := sub_zero w
example (w : Word) : Word.mul w 1 = w := mul_one w
example (w : Word) : Word.div w 0 = 0 := div_zero w
example (w : Word) : Word.sdiv w 0 = 0 := SignedDivMod.sdiv_zero w
example (w : Word) : Word.eqResult w w = 1 := (Comparisons.eq_one_iff w w).2 rfl
example (w : Word) : Word.bitwiseXor w w = 0 := Bitwise.xor_self w
example (w : Word) : Word.shl 0 w = w := Shifts.shl_zero w
example (w : Word) : Word.signextend 31 w = w := ByteSignExtend.signextend_31 w
example (a b : Word) : Word.addmod a b 0 = 0 := AddMulMod.addmod_zero_modulus a b
example (w : Word) : Word.exp w 0 = 1 := exp_zero w

-- The public proof consumer can connect executable lookup to source boundaries.
example (code : ByteArray) (pc : Nat) :
    JumpDest.contains code pc = true ↔ Frame.ValidJumpDest code pc :=
  Frame.validJumpDest_iff code pc

example (s : Frame.State) (out : Frame.Outcome) :
    Frame.step s = out ↔ Frame.Rule s out := Frame.step_iff_rule s out
