import EthLib.EVM.StackImmediate

open EthLib.EVM

-- EIP-8024 Specification, Assembly/Disassembly examples.
example : StackImmediate.decodeSingle 0x80 = some 17 := by decide
example : StackImmediate.decodeSingle 0xdb = some 108 := by decide
example : StackImmediate.decodeSingle 0x5b = none := by decide
example : StackImmediate.decodePair 0x9d = some (2, 3) := by decide
example : StackImmediate.decodePair 0x2f = some (1, 19) := by decide
example : StackImmediate.decodePair 0x50 = some (14, 16) := by decide
example : StackImmediate.decodePair 0x51 = some (14, 15) := by decide
example : StackImmediate.decodePair 0x52 = none := by decide
example : StackImmediate.byte ⟨#[0xe6]⟩ 0 = 0 := by decide
