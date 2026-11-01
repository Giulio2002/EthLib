import EthLib.EVM.Proofs.JumpDest

open EthLib.EVM.JumpDest

example : destinations (ByteArray.mk #[]) = [] := by unfold destinations; rw [scanFrom, scanFrom, scanFrom, scanFrom, scanFrom, scanFrom, scanFrom]; decide
example : destinations (ByteArray.mk #[0x5b]) = [0] := by unfold destinations; rw [scanFrom, scanFrom, scanFrom, scanFrom, scanFrom, scanFrom, scanFrom]; decide
example : destinations (ByteArray.mk #[0x5b, 0x5b]) = [0, 1] := by unfold destinations; rw [scanFrom, scanFrom, scanFrom, scanFrom, scanFrom, scanFrom, scanFrom]; decide
example : destinations (ByteArray.mk #[0x60, 0x5b, 0x5b]) = [2] := by unfold destinations; rw [scanFrom, scanFrom, scanFrom, scanFrom, scanFrom, scanFrom, scanFrom]; decide
example : destinations (ByteArray.mk #[0x5f, 0x5b]) = [1] := by unfold destinations; rw [scanFrom, scanFrom, scanFrom, scanFrom, scanFrom, scanFrom, scanFrom]; decide
example : destinations (ByteArray.mk #[0x00, 0xf3, 0xfe, 0x0c, 0x5b]) = [4] := by unfold destinations; rw [scanFrom, scanFrom, scanFrom, scanFrom, scanFrom, scanFrom, scanFrom]; decide
example : destinations (ByteArray.mk #[0x61, 0x60, 0x5b, 0x5b]) = [3] := by unfold destinations; rw [scanFrom, scanFrom, scanFrom, scanFrom, scanFrom, scanFrom, scanFrom]; decide
example : destinations (ByteArray.mk #[0x7f, 0x5b]) = [] := by unfold destinations; rw [scanFrom, scanFrom, scanFrom, scanFrom, scanFrom, scanFrom, scanFrom]; decide
