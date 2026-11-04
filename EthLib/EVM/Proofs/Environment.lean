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
        EthLib.Base.bytesToNat bytes.data.toList := by
  exact EthLib.EVM.Proofs.Word.ofBytesBE_ok_iff _ _

/-- An available in-window hash is selected by its age from the newest end. -/
theorem blockHash_in_range (history : BlockHistory) (current index : Word)
    (window : index.toNat < current.toNat ∧ current.toNat ≤ index.toNat + 256)
    (available : current.toNat - index.toNat ≤ history.length) :
    blockHash history current index =
      history[history.length - (current.toNat - index.toNat)]' (by omega) := by
  have bound : history.length - (current.toNat - index.toNat) < history.length := by omega
  simp [blockHash, window, available, bound]

/-- The source returns zero for a current, future, or too-old number. -/
theorem blockHash_out_of_window (history : BlockHistory) (current index : Word)
    (outside : ¬ (index.toNat < current.toNat ∧ current.toNat ≤ index.toNat + 256)) :
    blockHash history current index = 0 := by
  simp [blockHash, outside]

/-- Missing in-window history has the documented total extension. -/
theorem blockHash_missing (history : BlockHistory) (current index : Word)
    (missing : history.length < current.toNat - index.toNat) :
    blockHash history current index = 0 := by
  simp [blockHash, Nat.not_le.mpr missing]

/-- A covered window has an entry for each number that EELS indexes. -/
theorem blockHash_covered (history : BlockHistory) (current index : Word)
    (valid : HistoryCoversWindow history current)
    (window : index.toNat < current.toNat ∧ current.toNat ≤ index.toNat + 256) :
    current.toNat - index.toNat ≤ history.length := by
  unfold HistoryCoversWindow at valid
  omega

/-- A matching oldest-first suffix yields the chain hash for an in-window number. -/
theorem blockHash_source_agreement (history : BlockHistory) (current index : Word)
    (chain : Nat → Word) (valid : HistoryMatches history current chain)
    (window : index.toNat < current.toNat ∧ current.toNat ≤ index.toNat + 256) :
    blockHash history current index = chain index.toNat := by
  obtain ⟨covers, _, _, agrees⟩ := valid
  have available := blockHash_covered history current index covers window
  rw [blockHash_in_range history current index window available]
  have bound : history.length - (current.toNat - index.toNat) < history.length := by omega
  have numbered : history.length ≤ current.toNat +
      (history.length - (current.toNat - index.toNat)) := by omega
  rw [agrees _ bound numbered]
  congr 1
  omega

/-- A selected hash preserves its fixed-width big-endian source bytes. -/
theorem blockHash_codec (history : BlockHistory) (current index : Word) (bytes : ByteArray)
    (window : index.toNat < current.toNat ∧ current.toNat ≤ index.toNat + 256)
    (available : current.toNat - index.toNat ≤ history.length)
    (codec : Word.ofBytesBE bytes = .ok
      (history[history.length - (current.toNat - index.toNat)]' (by omega))) :
    (blockHash history current index).toBytesBE = bytes := by
  rw [blockHash_in_range history current index window available]
  exact EthLib.EVM.Proofs.Word.toBytesBE_ofBytesBE bytes _ codec

end EthLib.EVM.Environment
