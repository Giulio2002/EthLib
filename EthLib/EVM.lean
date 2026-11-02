module
public import EthLib.EVM.Memory.WordAccess
public import EthLib.EVM.Gas

public import EthLib.EVM.Word
public import EthLib.EVM.Memory
public import EthLib.EVM.Memory.Ranges
public import EthLib.EVM.Memory.Allocation
public import EthLib.EVM.Word.DivMod
public import EthLib.EVM.Word.SignedDivMod
public import EthLib.EVM.Word.Comparisons
public import EthLib.EVM.Word.Bitwise
public import EthLib.EVM.Word.Shifts
public import EthLib.EVM.Word.ByteSignExtend
public import EthLib.EVM.Word.AddMulMod
public import EthLib.EVM.Word.Exp
public import EthLib.EVM.Opcode
public import EthLib.EVM.PushImmediate
public import EthLib.EVM.CallData
public import EthLib.EVM.JumpDest
public import EthLib.EVM.Stack
public import EthLib.EVM.Frame
public import EthLib.EVM.Frame.Rules
public import EthLib.EVM.Runner

/-!
# `EthLib.EVM`

256-bit words, result helpers, and logically allocated byte memory.
Division and remainder include signed and unsigned results.
Arithmetic includes modular addition and exponentiation results.
Opcode classification and PUSH immediate decoding follow Cancun.
Bounded stack helpers.
The frame runner implements a restricted Cancun instruction subset.
It does not implement fork selection or whole-EVM execution.
Cancun opcode decoding includes jump destination scanning.
Precompiles belong to the Execution domain.
-/
