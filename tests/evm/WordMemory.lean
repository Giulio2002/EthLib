import EthLib.EVM
import EthLib.EVM.Proofs

open EthLib.EVM EthLib.EVM.Memory EthLib.EVM.Memory.Allocation

def pattern : Word := BitVec.ofNat 256 (2^255 + 258)
def maximal : Word := BitVec.ofNat 256 (2^256 - 1)

def checkOffset (n : Nat) : Bool :=
  (loadWord (storeWord Allocation.empty n pattern) n).1 == pattern &&
  (storeWord Allocation.empty n pattern).words == requiredWords n 32

#guard checkOffset 0
#guard checkOffset 1
#guard checkOffset 31
#guard checkOffset 32
#guard checkOffset 33
#guard checkOffset (2^256)
#guard (loadWord (storeWord Allocation.empty 33 maximal) 33).1 == maximal
#guard readByte (storeWord Allocation.empty 0 pattern).store 0 == 128
#guard readByte (storeWord Allocation.empty 0 pattern).store 30 == 1
#guard readByte (storeWord Allocation.empty 0 pattern).store 31 == 2
#guard (read (storeByte (write Allocation.empty 0 [1, 2, 3]) 1 maximal) 0 3).1 == [1, 255, 3]
#guard (loadWord (copy (storeWord Allocation.empty 1 pattern) 33 1 32) 33).1 == pattern

example (s : State) (a : Nat) (w : Word) : (loadWord (storeWord s a w) a).1 = w :=
  loadWord_storeWord s a w

-- A byte at the end of allocated memory is followed by zero bytes on load.
def lastByte : State := write Allocation.empty 31 [171]
#guard (loadWord lastByte 31).1.toNat == 171 * 256^31
#guard (loadWord lastByte 32).1 == 0
#guard (loadWord (storeByte (storeWord Allocation.empty 0 pattern) 32 maximal) 0).1 == pattern

example (s : State) (a b : Nat) (w : Word)
    (h : b + 32 ≤ a ∨ a + 1 ≤ b) :
    (loadWord (storeByte s a w) b).1 = (loadWord s b).1 :=
  loadWord_storeByte_disjoint s a b w h

example (s : State) (a k : Nat) (h : Valid s) (hk : k ≤ 32)
    (outside : byteSize s ≤ a + k) :
    (loadWord s a).1.toNat =
      EthLib.Base.bytesToNat (readRange s.store a k) * 256 ^ (32 - k) :=
  loadWord_right_zero_padding s a k h hk outside
