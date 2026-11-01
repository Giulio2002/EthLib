module

public import EthLib.EVM.Word
public import EthLib.EVM.Opcode
public import EthLib.EVM.PushImmediate

/-!
# `EthLib.EVM`

Unsigned 256-bit words, modular addition and Cancun opcode decoding.
Opcode classification does not implement instruction execution or fork selection.
The existing precompile modules retain their paths and ownership.
-/
