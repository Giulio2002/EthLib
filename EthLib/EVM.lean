module

public import EthLib.EVM.Word
public import EthLib.EVM.Word.DivMod
public import EthLib.EVM.Word.SignedDivMod
public import EthLib.EVM.Word.Comparisons
public import EthLib.EVM.Word.Bitwise
public import EthLib.EVM.Word.Shifts

/-!
# `EthLib.EVM`

256-bit words and arithmetic, comparison, and bitwise results.
Division and remainder include signed and unsigned results.
This domain does not implement instruction execution or fork selection.
The existing precompile modules retain their paths and ownership.
-/
