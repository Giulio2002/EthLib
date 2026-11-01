import EthLib.EVM.Memory
open EthLib.EVM.Memory
#guard readByte empty (2^256) == 0
#guard readByte (writeByte empty (2^256) 7) (2^256) == 7
#guard readByte (writeByte (writeByte empty (2^256) 7) (2^256 + 1) 9) (2^256) == 7
#guard readByte (writeByte (writeByte empty (2^256) 7) (2^256) 0) (2^256) == 0
#guard readByte (writeByte (writeByte empty (2^256) 7) (2^256) 8) (2^256) == 8
