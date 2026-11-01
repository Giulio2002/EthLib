module

public import EthLib.Precompiles.Modexp.Bytes

/-!
# EVM words

The source is the Shanghai Yellow Paper, revision
`efc5f9a1f356cba376c978eedb63cb0363c2aa85`:
https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex

Section 9.1 fixes the word width at 256 bits.
Appendix H.2, "0s: Stop and Arithmetic Operations", gives addition modulo `2^256`.
Only the arithmetic result is modeled here.
Stack effects, gas, program counters, and instruction execution are outside this module.
-/

@[expose] public section

namespace EthLib.EVM

/-- An unsigned 256-bit word, as specified by Yellow Paper section 9.1.

This abbreviation leaves BitVec constructors, literals and operators available.
Only `Word.ofNat` enforces the checked natural-input boundary.
The formal refinement contract is in `EthLib.EVM.Proofs.Word`.
-/
abbrev Word := BitVec 256

namespace Word

/-- The arithmetic modulus from Yellow Paper Appendix H.2. -/
def modulus : Nat := 2 ^ 256

/-- An input that cannot be represented as an unsigned EVM word. -/
inductive InputError where
  /-- The natural number is at least `2^256`. -/
  | outOfRange
  deriving DecidableEq, Repr

/-- Accept a natural number only when it fits, without reducing it modulo the word size.

This is an API boundary check, not an EVM instruction.
-/
def ofNat (n : Nat) : Except InputError Word :=
  if h : n < modulus then
    .ok (BitVec.ofNatLT n h)
  else
    .error .outOfRange

/-- Addition modulo `2^256`, from Yellow Paper Appendix H.2, ADD's result equation.

Reduction here is the specified arithmetic operation, not input validation.
-/
def add (a b : Word) : Word := BitVec.ofNat 256 (a.toNat + b.toNat)

/-- A byte sequence whose length is not exactly 32. -/
inductive BytesError where
  | invalidLength
  deriving DecidableEq, Repr

/-- Encode a word in 32 big-endian bytes.

Cancun execution-specs at `fd9298410ec7218838c8348f69c1eb633f1797dc`
uses `U256.to_be_bytes32` in `vm/instructions/storage.py`.
Yellow Paper section 9.1 fixes the word width at 256 bits.
Appendix H.2 BYTE numbers bytes from the most significant end.
-/
def toBytesBE (w : Word) : ByteArray :=
  ⟨(EthLib.Precompiles.Modexp.natToBytes 32 w.toNat).toArray⟩

/-- Decode exactly 32 big-endian bytes, rejecting every other length.

The length check is an API boundary, independent of EVM memory padding.
-/
def ofBytesBE (bytes : ByteArray) : Except BytesError Word :=
  if bytes.size = 32 then
    .ok (BitVec.ofNat 256 (EthLib.Precompiles.Modexp.bytesToNat bytes.data.toList))
  else
    .error .invalidLength

end Word
end EthLib.EVM
