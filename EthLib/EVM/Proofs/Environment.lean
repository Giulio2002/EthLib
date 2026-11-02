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

end EthLib.EVM.Environment
