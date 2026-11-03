module
public import EthLib.EVM.World
public import EthLib.EVM.TransactionState
public import EthLib.EVM.TransactionTracker
public import EthLib.EVM.TransactionAccount
public import EthLib.EVM.TransactionTransfer
public import EthLib.EVM.Memory.WordAccess
public import EthLib.EVM.Gas
public import EthLib.EVM.Gas.StateMeter
public import EthLib.EVM.Gas.Call
public import EthLib.EVM.BlobFee

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
public import EthLib.EVM.StackImmediate
public import EthLib.EVM.CallData
public import EthLib.EVM.ReturnData
public import EthLib.EVM.JumpDest
public import EthLib.EVM.Stack
public import EthLib.EVM.Frame
public import EthLib.EVM.Frame.Rules
public import EthLib.EVM.Runner
public import EthLib.EVM.ChildSettlement
public import EthLib.EVM.StaticCall
public import EthLib.EVM.NestedRunner

/-!
# `EthLib.EVM`

256-bit words, result helpers, and logically allocated byte memory.
Division and remainder include signed and unsigned results.
Arithmetic includes modular addition and exponentiation results.
Opcode classification includes the historical Cancun classifier and Osaka CLZ.
Bounded stack helpers.
The frame runner implements a restricted Cancun-based subset, Osaka CLZ,
and the selected Amsterdam opcodes SLOTNUM, DUPN, SWAPN and EXCHANGE.
It does not implement fork selection or whole-EVM execution.
PUSH immediate decoding and jump destination scanning follow Cancun.
The historical Cancun decoder and augmented decoder include PUSH immediates.
The Amsterdam stack immediates have a separate decoder.
Precompiles belong to the Execution domain.
-/
