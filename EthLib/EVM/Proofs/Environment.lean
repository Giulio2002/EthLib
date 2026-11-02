module

public import EthLib.EVM.Environment
public import EthLib.EVM.Proofs.Word
import Mathlib.Tactic

/-! Numeric and word-codec contracts for message addresses. -/

@[expose] public section
namespace EthLib.EVM.Environment

/-- Zero extension preserves every address as a natural number. -/
theorem addressWord_toNat (address : Address) :
    (addressWord address).toNat = address.val := by
  simp only [addressWord, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have bound := address.isLt
  have widths : 2 ^ 160 < 2 ^ 256 := by decide
  omega

/-- Distinct addresses produce distinct stack words. -/
theorem addressWord_injective : Function.Injective addressWord := by
  intro a b h
  apply Fin.ext
  have h' := congrArg BitVec.toNat h
  simpa only [addressWord_toNat] using h'

/-- The standard word codec round-trips every zero-extended address. -/
theorem addressWord_codec (address : Address) :
    Word.ofBytesBE (addressWord address).toBytesBE = .ok (addressWord address) :=
  EthLib.EVM.Proofs.Word.ofBytesBE_toBytesBE _

/-- An in-range index selects the supplied decoded word. -/
theorem blobHash_in_range (context : Context) (index : Word)
    (h : index.toNat < context.blobVersionedHashes.length) :
    blobHash context index = context.blobVersionedHashes[index.toNat] := by
  simp [blobHash, h]

/-- An index outside the supplied list returns zero. -/
theorem blobHash_out_of_range (context : Context) (index : Word)
    (h : context.blobVersionedHashes.length ≤ index.toNat) :
    blobHash context index = 0 := by
  simp [blobHash, Nat.not_lt.mpr h]

/-- The bytes represented by a selected word are exactly the supplied bytes. -/
theorem blobHash_codec (context : Context) (index : Word) (bytes : ByteArray)
    (h : index.toNat < context.blobVersionedHashes.length)
    (codec : Word.ofBytesBE bytes = .ok context.blobVersionedHashes[index.toNat]) :
    (blobHash context index).toBytesBE = bytes := by
  rw [blobHash_in_range context index h]
  exact EthLib.EVM.Proofs.Word.toBytesBE_ofBytesBE bytes _ codec

/-- A selected word has the source bytes exactly when their big-endian value agrees. -/
theorem blobHash_decode_iff (context : Context) (index : Word) (bytes : ByteArray)
    :
    Word.ofBytesBE bytes = .ok (blobHash context index) ↔
      bytes.size = 32 ∧ (blobHash context index).toNat =
        EthLib.Precompiles.Modexp.bytesToNat bytes.data.toList := by
  exact EthLib.EVM.Proofs.Word.ofBytesBE_ok_iff _ _

end EthLib.EVM.Environment
