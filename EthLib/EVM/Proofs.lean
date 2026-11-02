module
public import EthLib.EVM.Proofs.Memory.WordAccess
public import EthLib.EVM.Proofs.Gas

public import EthLib.EVM.Proofs.Word
public import EthLib.EVM.Proofs.Memory
public import EthLib.EVM.Proofs.Memory.Ranges
public import EthLib.EVM.Proofs.Memory.Allocation
public import EthLib.EVM.Proofs.Word.DivMod
public import EthLib.EVM.Proofs.Word.SignedDivMod
public import EthLib.EVM.Proofs.Word.Comparisons
public import EthLib.EVM.Proofs.Word.Bitwise
public import EthLib.EVM.Proofs.Word.Shifts
public import EthLib.EVM.Proofs.Word.ByteSignExtend
public import EthLib.EVM.Proofs.Word.AddMulMod
public import EthLib.EVM.Proofs.Word.Exp
public import EthLib.EVM.Proofs.Opcode
public import EthLib.EVM.Proofs.PushImmediate
public import EthLib.EVM.Proofs.JumpDest
public import EthLib.EVM.Proofs.Stack
public import EthLib.EVM.Proofs.Frame
public import EthLib.EVM.Proofs.FrameArithmetic
public import EthLib.EVM.Proofs.FrameComparison
public import EthLib.EVM.Proofs.Frame.Reference
public import EthLib.EVM.Proofs.Frame.Memory
public import EthLib.EVM.Proofs.Runner
public import EthLib.EVM.Proofs.Runner.StraightLine
public import EthLib.EVM.Proofs.Runner.Mixed
public import EthLib.EVM.Proofs.Runner.Memory

/-!
# `EthLib.EVM.Proofs`

Word representation, construction, and memory access contracts.
Arithmetic, comparison, bitwise, BYTE and SIGNEXTEND result contracts.
Division and remainder contracts cover signed and unsigned results.
Arithmetic contracts include modular addition and exponentiation.
Cancun opcode classification, PUSH immediate decoding and jump destination scanning.
Bounded stack correctness and source-model refinement.
This root belongs to the separate `Proofs` library.
-/
