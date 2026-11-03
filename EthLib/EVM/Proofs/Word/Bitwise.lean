module

public import EthLib.EVM.Word.Bitwise
public import EthLib.EVM.Proofs.Word

/-! # Bitwise result contracts

These equations formalize a reading of the cited sources.
The kernel checks refinement to these equations, not that reading itself.
-/

@[expose] public section

namespace EthLib.EVM.Proofs.Word.Bitwise

open EthLib.EVM EthLib.EVM.Word

/-- Each bit of AND, including positions outside the word. -/
theorem and_bit (a b : Word) (i : Nat) :
    (bitwiseAnd a b).getLsbD i = (a.getLsbD i && b.getLsbD i) := by
  exact BitVec.getLsbD_and

/-- Each bit of OR, including positions outside the word. -/
theorem or_bit (a b : Word) (i : Nat) :
    (bitwiseOr a b).getLsbD i = (a.getLsbD i || b.getLsbD i) := by
  exact BitVec.getLsbD_or

/-- Each bit of XOR, including positions outside the word. -/
theorem xor_bit (a b : Word) (i : Nat) :
    (bitwiseXor a b).getLsbD i = (a.getLsbD i ^^ b.getLsbD i) := by
  exact BitVec.getLsbD_xor

/-- NOT complements only positions inside the word. -/
theorem not_bit (a : Word) (i : Nat) :
    (bitwiseNot a).getLsbD i = (decide (i < 256) && !a.getLsbD i) := by
  exact BitVec.getLsbD_not

/-- AND agrees with the natural-number bitwise operation. -/
theorem and_nat (a b : Word) : (bitwiseAnd a b).toNat = a.toNat &&& b.toNat := by
  exact BitVec.toNat_and a b

/-- OR agrees with the natural-number bitwise operation. -/
theorem or_nat (a b : Word) : (bitwiseOr a b).toNat = a.toNat ||| b.toNat := by
  exact BitVec.toNat_or a b

/-- XOR agrees with the natural-number bitwise operation. -/
theorem xor_nat (a b : Word) : (bitwiseXor a b).toNat = a.toNat ^^^ b.toNat := by
  exact BitVec.toNat_xor a b

/-- NOT is complement within the 256-bit mask. -/
theorem not_nat (a : Word) : (bitwiseNot a).toNat = modulus - 1 - a.toNat := by
  exact BitVec.toNat_not

/-- The result of AND is in range. -/
theorem and_range (a b : Word) : (bitwiseAnd a b).toNat < modulus := (bitwiseAnd a b).isLt
/-- The result of OR is in range. -/
theorem or_range (a b : Word) : (bitwiseOr a b).toNat < modulus := (bitwiseOr a b).isLt
/-- The result of XOR is in range. -/
theorem xor_range (a b : Word) : (bitwiseXor a b).toNat < modulus := (bitwiseXor a b).isLt
/-- The result of NOT is in range. -/
theorem not_range (a : Word) : (bitwiseNot a).toNat < modulus := (bitwiseNot a).isLt

/-- AND is commutative. -/
theorem and_comm (a b : Word) : bitwiseAnd a b = bitwiseAnd b a := BitVec.and_comm a b
/-- OR is commutative. -/
theorem or_comm (a b : Word) : bitwiseOr a b = bitwiseOr b a := BitVec.or_comm a b
/-- XOR is commutative. -/
theorem xor_comm (a b : Word) : bitwiseXor a b = bitwiseXor b a := BitVec.xor_comm a b
/-- AND is associative. -/
theorem and_assoc (a b c : Word) : bitwiseAnd (bitwiseAnd a b) c = bitwiseAnd a (bitwiseAnd b c) := BitVec.and_assoc a b c
/-- OR is associative. -/
theorem or_assoc (a b c : Word) : bitwiseOr (bitwiseOr a b) c = bitwiseOr a (bitwiseOr b c) := BitVec.or_assoc a b c
/-- XOR is associative. -/
theorem xor_assoc (a b c : Word) : bitwiseXor (bitwiseXor a b) c = bitwiseXor a (bitwiseXor b c) := BitVec.xor_assoc a b c
/-- AND with zero is zero. -/
theorem and_zero (a : Word) : bitwiseAnd a 0 = 0 := BitVec.and_zero
/-- AND with all ones is the operand. -/
theorem and_ones (a : Word) : bitwiseAnd a (BitVec.allOnes 256) = a := BitVec.and_allOnes
/-- OR with zero is the operand. -/
theorem or_zero (a : Word) : bitwiseOr a 0 = a := BitVec.or_zero
/-- OR with all ones is all ones. -/
theorem or_ones (a : Word) : bitwiseOr a (BitVec.allOnes 256) = BitVec.allOnes 256 := BitVec.or_allOnes
/-- XOR with zero is the operand. -/
theorem xor_zero (a : Word) : bitwiseXor a 0 = a := BitVec.xor_zero
/-- XOR with all ones complements the operand. -/
theorem xor_ones (a : Word) : bitwiseXor a (BitVec.allOnes 256) = bitwiseNot a := BitVec.xor_allOnes
/-- XOR cancels equal operands. -/
theorem xor_self (a : Word) : bitwiseXor a a = 0 := BitVec.xor_self
/-- NOT exchanges zero and all ones. -/
theorem not_zero : bitwiseNot 0 = BitVec.allOnes 256 := BitVec.not_zero
/-- NOT exchanges all ones and zero. -/
theorem not_ones : bitwiseNot (BitVec.allOnes 256) = 0 := BitVec.not_allOnes
/-- NOT is an involution. -/
theorem not_not (a : Word) : bitwiseNot (bitwiseNot a) = a := BitVec.not_not
/-- Complement distributes over AND as OR. -/
theorem not_and (a b : Word) : bitwiseNot (bitwiseAnd a b) = bitwiseOr (bitwiseNot a) (bitwiseNot b) := BitVec.not_and
/-- Complement distributes over OR as AND. -/
theorem not_or (a b : Word) : bitwiseNot (bitwiseOr a b) = bitwiseAnd (bitwiseNot a) (bitwiseNot b) := BitVec.not_or

/-- A low-bit example with two distinct inputs. -/
theorem example_and : bitwiseAnd 12 10 = 8 := by decide
/-- Complement of zero reaches the top boundary. -/
theorem example_not_zero : (bitwiseNot 0).toNat = modulus - 1 := by decide

end EthLib.EVM.Proofs.Word.Bitwise
