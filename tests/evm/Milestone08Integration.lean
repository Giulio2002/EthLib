import EthLib.EVM.Runner
import EthLib.EVM.Proofs.Memory.Allocation

open EthLib.EVM

-- One program crosses arithmetic, comparison, bitwise, shift, ternary,
-- dynamic gas, stack, untaken branch and observation instruction boundaries.
private def code : ByteArray := ⟨#[
  0x60, 3, 0x60, 4, 0x01, 0x60, 7, 0x14,
  0x60, 1, 0x1b, 0x60, 3, 0x16,
  0x60, 4, 0x60, 4, 0x60, 5, 0x08,
  0x60, 2, 0x0a, 0x50, 0x5f, 0x5f, 0x57,
  0x58, 0x59, 0x5a, 0x00]⟩
private def initial : Frame.State :=
  ⟨code, 0, Stack.empty, 300, Memory.Allocation.empty, Memory.Allocation.empty_valid, ⟨ByteArray.empty, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, [], [], BlobFee.cancun⟩⟩, ByteArray.empty, { parent := {} }, [], []⟩

-- The byte lengths place PC at 28; MSIZE is zero and 129 gas was charged, including one EXP exponent byte.
/-- info: (32, 171, [171, 0, 28, 2]) -/
#guard_msgs in
#eval match Runner.run 23 initial with
  | .stopped s => (s.pc, s.gas, s.stack.val.map (fun w => BitVec.toNat w))
  | _ => (0, 0, [])
