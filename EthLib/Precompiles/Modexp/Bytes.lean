import EthLib.Precompiles.Modexp.Constants

/-!
# `Modexp.Bytes`

Reading big-endian integers out of the call data, and writing them back.

EIP-198 says the call data is "assumed to be infinitely right-padded with zero bytes".
So `byteAt` is total: every index past the end reads as zero.
That is the rule of `buffer_read`.
It lives in `forks/bpo2/vm/memory.py`, in execution-specs at `2c0c8e7`.
-/

namespace EthLib.Precompiles.Modexp

/-- The byte at index `i` of the call data, or `0` past its end. -/
def byteAt (data : ByteArray) (i : Nat) : UInt8 :=
  data.data.getD i 0

/-- The big-endian integer written by a byte list. -/
def bytesToNat (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- `size` bytes of the call data from `start`, zero-padded on the right.

`buffer_read` in `forks/bpo2/vm/memory.py`. -/
def bufferRead (data : ByteArray) (start size : Nat) : List UInt8 :=
  (List.range size).map fun i => byteAt data (start + i)

/-- The big-endian integer held by `size` bytes of the call data from `start`. -/
def readNat (data : ByteArray) (start size : Nat) : Nat :=
  bytesToNat (bufferRead data start size)

/-- `n` as exactly `len` big-endian bytes, dropping any bits above `256 ^ len`.

The execution-specs module fixes the width the same way,
with `to_bytes(Uint(modulus_length), "big")`. -/
def natToBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | len + 1, n => natToBytes len (n / 256) ++ [UInt8.ofNat (n % 256)]

end EthLib.Precompiles.Modexp
