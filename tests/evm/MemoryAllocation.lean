import EthLib.EVM.Memory.Allocation
open EthLib.EVM.Memory
open EthLib.EVM.Memory.Allocation

#guard requiredWords 0 31 == 1
#guard requiredWords 0 32 == 1
#guard requiredWords 0 33 == 2
#guard requiredWords (2^256) 0 == 0
#guard byteSize (expand Allocation.empty 0 33) == 64
#guard byteSize (expand (expand Allocation.empty 0 33) 0 1) == 64
#guard byteSize (copy Allocation.empty 0 64 1) == 96
#guard copy Allocation.empty (2^256) (2^256) 0 == Allocation.empty
#guard (read (expand Allocation.empty 0 64) 32 2).1 == [0, 0]
def sample : State := write Allocation.empty 0 [1, 2, 3, 4]
#guard (read (copy sample 1 0 3) 0 4).1 == [1, 1, 2, 3]
#guard (read (copy sample 0 1 3) 0 4).1 == [2, 3, 4, 4]
#guard write sample (2^256) [] == sample
