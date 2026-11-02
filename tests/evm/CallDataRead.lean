import EthLib.EVM.CallData

open EthLib.EVM

-- These pin right padding and big-endian order for a two-byte input.
example : (CallData.load ⟨ByteArray.mk #[0x12, 0x34], ⟨0, 0, 0, 0, 0⟩⟩ 0).toNat =
    0x1234 * 256 ^ 30 := by decide

example : (CallData.load ⟨ByteArray.mk #[0x12, 0x34], ⟨0, 0, 0, 0, 0⟩⟩ 1).toNat =
    0x34 * 256 ^ 31 := by decide

example : CallData.load ⟨ByteArray.mk #[0x12, 0x34], ⟨0, 0, 0, 0, 0⟩⟩ (BitVec.ofNat 256 (2 ^ 256 - 1)) = 0 := by
  decide
