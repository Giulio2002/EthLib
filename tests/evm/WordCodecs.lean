import EthLib.EVM.Word
open EthLib.EVM

def bytes (xs : List UInt8) : ByteArray := ⟨xs.toArray⟩

def zeros (n : Nat) : List UInt8 := List.replicate n 0

-- Zero, one, the largest word and the high bit pin the endpoint bytes.
#guard Word.toBytesBE 0 == bytes (zeros 32)
#guard Word.toBytesBE 1 == bytes (zeros 31 ++ [1])
#guard Word.toBytesBE (BitVec.ofNat 256 (2^256 - 1)) == bytes (List.replicate 32 255)
#guard Word.toBytesBE (BitVec.ofNat 256 (2^255)) == bytes (128 :: zeros 31)
-- Distinct positions and embedded zeros pin the order of the bytes.
#guard Word.toBytesBE (BitVec.ofNat 256 (2^248 + 2^128 + 3)) ==
  bytes ([1] ++ zeros 14 ++ [1] ++ zeros 15 ++ [3])
def checkDecode (b : ByteArray) (expected : Option Word) : Bool :=
  match Word.ofBytesBE b, expected with
  | .error _, none => true
  | .ok w, some v => w == v
  | _, _ => false

#guard checkDecode (bytes (zeros 0)) none
#guard checkDecode (bytes (zeros 31)) none
#guard checkDecode (bytes (zeros 32)) (some 0)
#guard checkDecode (bytes (zeros 33)) none
#guard checkDecode (bytes ([1] ++ zeros 14 ++ [1] ++ zeros 15 ++ [3]))
  (some (BitVec.ofNat 256 (2^248 + 2^128 + 3)))
