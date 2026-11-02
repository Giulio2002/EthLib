import EthLib.EVM.Proofs.Opcode
import EthLib.EVM.Proofs.PushImmediate

open EthLib.EVM
open EthLib.EVM.PushImmediate
open EthLib.EVM.Proofs.PushImmediate

-- PUSH2 reads one available byte and pads the missing low byte.
example : bytes (ByteArray.mk #[0x61, 0x12]) 0 ⟨2, by decide⟩ = [0x12, 0] := by decide
example : value (ByteArray.mk #[0x61, 0x12]) 0 ⟨2, by decide⟩ = (0x1200 : Word) := by decide

-- Leading and trailing zero bytes occupy different positions.
example : value (ByteArray.mk #[0x61, 0, 1]) 0 ⟨2, by decide⟩ = (1 : Word) := by decide
example : value (ByteArray.mk #[0x61, 1, 0]) 0 ⟨2, by decide⟩ = (256 : Word) := by decide

-- The maximum immediate length pads all missing low bytes.
example : (bytes (ByteArray.mk #[0x7f, 0xff]) 0 ⟨32, by decide⟩).length = 32 := by decide
example : value (ByteArray.mk #[0x7f, 0xff]) 0 ⟨32, by decide⟩ =
    BitVec.ofNat 256 (255 * 256 ^ 31) := by decide

-- Natural positions do not wrap at the EVM word boundary.
example : nextPC (2 ^ 256 - 1) ⟨32, by decide⟩ = 2 ^ 256 + 32 := by decide
example : bytes (ByteArray.mk #[0x61, 1]) (2 ^ 256) ⟨2, by decide⟩ = [0, 0] := by decide

-- Every permitted length has exactly that many immediate bytes.
example (code : ByteArray) (pc : Nat) (n : Fin 33) : (bytes code pc n).length = n.val :=
  bytes_length code pc n

-- Every PUSH length has its specified byte and is decoded canonically.
example (n : Fin 33) : Opcode.decode (UInt8.ofNat (0x5f + n.val)) = some (.push n) := by
  exact EthLib.EVM.Proofs.Opcode.decode_encode (.push n)
