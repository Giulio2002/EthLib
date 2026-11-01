module

public import EthLib.EVM.Word
public import EthLib.EVM.Word.DivMod
public import EthLib.EVM.Word.SignedDivMod
public import EthLib.EVM.Word.Comparisons
public import EthLib.EVM.Word.Bitwise
public import EthLib.EVM.Word.Shifts
public import EthLib.EVM.Word.ByteSignExtend
public import EthLib.EVM.Word.AddMulMod

/-!
# `EthLib.EVM`

256-bit words and arithmetic, comparison, bitwise, BYTE and SIGNEXTEND results.
Division and remainder include signed and unsigned results.
This domain does not implement instruction execution or fork selection.
The existing precompile modules retain their paths and ownership.
-/
