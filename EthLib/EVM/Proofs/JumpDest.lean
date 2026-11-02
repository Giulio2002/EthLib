module

public import EthLib.EVM.JumpDest
import Mathlib.Tactic

/-! Kernel-checked properties of the jump destination scan. -/

@[expose] public section

namespace EthLib.EVM.Proofs.JumpDest

open EthLib.EVM
open EthLib.EVM.JumpDest

/-- Source byte-length rule, independent of opcode decoding. -/
def sourceLength (b : UInt8) : Nat :=
  if 0x60 ≤ b.toNat ∧ b.toNat ≤ 0x7f then 1 + (b.toNat - 0x5f) else 1

set_option maxHeartbeats 4000000 in
/-- The decoder's step agrees with the source byte ranges for every byte. -/
theorem decodedLength (b : UInt8) :
    (match Opcode.decode b with
     | some (.push n) => 1 + n.val
     | _ => 1) = sourceLength b := by
  have check (n : Fin 256) :
      (match Opcode.decode (UInt8.ofNat n.val) with
       | some (.push n) => 1 + n.val
       | _ => 1) = sourceLength (UInt8.ofNat n.val) := by
    fin_cases n <;> decide
  have hb : UInt8.ofNat b.toNat = b := UInt8.ofNat_toNat
  rw [← hb]
  exact check ⟨b.toNat, UInt8.toNat_lt b⟩

/-- Each scanner step advances strictly in natural arithmetic. -/
theorem nextPC_gt (code : ByteArray) (pc : Nat) : pc < nextPC code pc := by
  unfold nextPC PushImmediate.nextPC
  split <;> omega

/-- A boundary reached from a starting position by the source byte-length rule. -/
inductive BoundaryFrom (code : ByteArray) : Nat → Nat → Prop where
  | here (pc : Nat) (inside : pc < code.size) : BoundaryFrom code pc pc
  | step (pc x : Nat) (inside : pc < code.size)
      (later : BoundaryFrom code (pc + sourceLength (PushImmediate.byteAt code pc)) x) :
      BoundaryFrom code pc x

/-- Boundaries are reached from position zero. -/
def Boundary (code : ByteArray) (pc : Nat) : Prop := BoundaryFrom code 0 pc

/-- The executable step uses the same byte length as the source rule. -/
theorem nextPC_eq_source (code : ByteArray) (pc : Nat) :
    nextPC code pc = pc + sourceLength (PushImmediate.byteAt code pc) := by
  have h := decodedLength (PushImmediate.byteAt code pc)
  unfold nextPC PushImmediate.nextPC
  generalize he : Opcode.decode (PushImmediate.byteAt code pc) = op at h ⊢
  cases op with
  | none => simp only at h ⊢; omega
  | some op => cases op <;> simp only at h ⊢ <;> omega

/-- Scanning from any position returns exactly the source boundaries with byte 0x5b. -/
theorem scanFrom_mem (code : ByteArray) (pc x : Nat) :
    x ∈ scanFrom code pc ↔ BoundaryFrom code pc x ∧ PushImmediate.byteAt code x = 0x5b := by
  induction pc using (measure (fun pc => code.size - pc)).wf.induction with
  | h pc ih =>
    rw [scanFrom]
    by_cases hp : pc < code.size
    · simp only [hp, ↓reduceIte]
      have decrease : code.size - nextPC code pc < code.size - pc := by
        have := nextPC_gt code pc
        omega
      have hi := ih (nextPC code pc) decrease
      rw [nextPC_eq_source] at hi ⊢
      by_cases hb : PushImmediate.byteAt code pc = 0x5b
      · rw [hb] at hi
        simp only [hb, beq_self_eq_true, ↓reduceIte, List.mem_cons, hi]
        constructor
        · rintro (rfl | ⟨h, hx⟩)
          · exact ⟨.here x hp, hb⟩
          · exact ⟨.step pc x hp (by simpa only [hb] using h), hx⟩
        · rintro ⟨h, hx⟩
          cases h with
          | here => exact Or.inl rfl
          | step _ _ _ h => exact Or.inr ⟨by simpa only [hb] using h, hx⟩
      · simp only [beq_iff_eq, hb, ↓reduceIte, hi]
        constructor
        · rintro ⟨h, hx⟩
          exact ⟨.step pc x hp h, hx⟩
        · rintro ⟨h, hx⟩
          cases h with
          | here => contradiction
          | step _ _ _ h => exact ⟨h, hx⟩
    · simp only [hp, ↓reduceIte, List.not_mem_nil, false_iff]
      rintro ⟨h, _⟩
      cases h with
      | here _ inside => exact hp inside
      | step _ _ inside _ => exact hp inside

/-- Membership is exactly the independent source boundary rule. -/
theorem mem_iff (code : ByteArray) (pc : Nat) :
    pc ∈ destinations code ↔ Boundary code pc ∧ PushImmediate.byteAt code pc = 0x5b :=
  scanFrom_mem code 0 pc

/-- Every output lies between the initial position and the end of code. -/
theorem scanFrom_bounds (code : ByteArray) (pc x : Nat)
    (h : x ∈ scanFrom code pc) : pc ≤ x ∧ x < code.size := by
  induction pc using (measure (fun pc => code.size - pc)).wf.induction with
  | h pc ih =>
    rw [scanFrom] at h
    split at h
    next hp =>
      split at h
      · simp only [List.mem_cons] at h
        rcases h with rfl | h
        · exact ⟨le_rfl, hp⟩
        · have ht := ih (nextPC code pc) (by change code.size - nextPC code pc < code.size - pc; have := nextPC_gt code pc; omega) h
          have := nextPC_gt code pc
          omega
      · have ht := ih (nextPC code pc) (by change code.size - nextPC code pc < code.size - pc; have := nextPC_gt code pc; omega) h
        have := nextPC_gt code pc
        omega
    next => simp at h

/-- All returned destinations lie inside the code. -/
theorem destinations_bounds (code : ByteArray) (x : Nat)
    (h : x ∈ destinations code) : x < code.size :=
  (scanFrom_bounds code 0 x h).2

/-- The scan lists destinations in strictly increasing order. -/
theorem scanFrom_sorted (code : ByteArray) (pc : Nat) :
    (scanFrom code pc).Pairwise (· < ·) := by
  induction pc using (measure (fun pc => code.size - pc)).wf.induction with
  | h pc ih =>
    rw [scanFrom]
    by_cases hp : pc < code.size
    · simp only [hp, ↓reduceIte]
      have dec : code.size - nextPC code pc < code.size - pc := by
        have := nextPC_gt code pc
        omega
      have hs := ih (nextPC code pc) dec
      split
      · apply List.pairwise_cons.mpr
        constructor
        · intro x hx
          have bound := scanFrom_bounds code (nextPC code pc) x hx
          have := nextPC_gt code pc
          omega
        · exact hs
      · exact hs
    · simp only [hp, ↓reduceIte]; exact List.Pairwise.nil

/-- Destinations are strictly ordered and therefore have no duplicates. -/
theorem destinations_sorted (code : ByteArray) :
    (destinations code).Pairwise (· < ·) := scanFrom_sorted code 0

/-- The Boolean API agrees with list membership. -/
theorem contains_iff (code : ByteArray) (pc : Nat) :
    contains code pc = true ↔ pc ∈ destinations code := by
  simp [contains]

/-- The executable test agrees with the independent instruction-boundary rule. -/
theorem contains_iff_boundary (code : ByteArray) (pc : Nat) :
    contains code pc = true ↔ Boundary code pc ∧ PushImmediate.byteAt code pc = 0x5b := by
  rw [contains_iff, mem_iff]

/-- Empty code has no destinations. -/
theorem empty : destinations (ByteArray.mk #[]) = [] := by
  rw [destinations, scanFrom]
  decide

end EthLib.EVM.Proofs.JumpDest
