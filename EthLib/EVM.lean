module

public import EthLib.EVM.Word
public import EthLib.EVM.Memory
public import EthLib.EVM.Memory.Ranges
public import EthLib.EVM.Memory.Allocation

/-!
# `EthLib.EVM`

Unsigned 256-bit words and modular addition.
This domain does not implement instruction execution or fork selection.
The existing precompile modules retain their paths and ownership.
-/
