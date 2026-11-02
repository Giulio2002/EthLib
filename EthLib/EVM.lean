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

/-!
# `EthLib.EVM`

256-bit words, result helpers, and logically allocated byte memory.
Division and remainder include signed and unsigned results.
Arithmetic includes modular addition and exponentiation results.
This domain does not implement instruction execution or fork selection.
-/
