import EthLib.EVM.Memory.Ranges
open EthLib.EVM.Memory

def sample : Store := writeRange empty 0 [1, 2, 3, 4]
#guard readRange (copyRange sample 1 0 3) 0 4 == [1, 1, 2, 3]
#guard readRange (copyRange sample 0 1 3) 0 4 == [2, 3, 4, 4]
#guard readRange (copyRange sample 0 0 4) 0 4 == [1, 2, 3, 4]
#guard copyRange sample (2^256) (2^256) 0 == sample
#guard readRange empty (2^256) 0 == []
#guard writeRange sample (2^256) [] == sample
#guard readRange (copyRange (writeByte empty 12 8) 20 10 4) 20 4 == [0, 0, 8, 0]
#guard readRange (copyRange sample 10 0 4) 10 4 == [1, 2, 3, 4]
#guard readRange (writeRange (writeRange empty 0 [1, 2]) 1 [9, 8]) 0 3 == [1, 9, 8]
