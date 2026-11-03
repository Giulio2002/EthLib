module

public import EthLib.EVM.Proofs.Frame
public import EthLib.EVM.Proofs.Word
public import EthLib.Cryptography.Proofs.Hash.KeccakKernel

/-!
# KECCAK256 adapter

The execution adapter uses Ethereum's shared Keccak-256 primitive.
The permutation replacement below does not establish an independent sponge specification.
-/

@[expose] public section
namespace EthLib.EVM.Frame

/-- The digest conversion is the checked big-endian word decoder. -/
theorem digestWord_decode (digest : Vector UInt8 32) :
    Word.ofBytesBE ⟨digest.toArray⟩ = .ok (digestWord digest) := by
  have size : (⟨digest.toArray⟩ : ByteArray).size = 32 := digest.size_toArray
  simp [Word.ofBytesBE, digestWord, size]

/-- Converting a digest to a word and back preserves all 32 bytes. -/
theorem digestWord_encode (digest : Vector UInt8 32) :
    Word.toBytesBE (digestWord digest) = ⟨digest.toArray⟩ := by
  exact EthLib.EVM.Proofs.Word.toBytesBE_ofBytesBE _ _ (digestWord_decode digest)

/-- The same digest is obtained with the proved record permutation replacement. -/
theorem digestWord_record (bytes : ByteArray) :
    digestWord (EthLib.Cryptography.Hash.Keccak.keccak256 bytes) =
      digestWord (EthLib.Cryptography.Hash.Keccak.Kernel.keccak256 bytes) := by
  rw [EthLib.Cryptography.Hash.Keccak.Kernel.keccak256_eq]

/-- An independent digest specification must be supplied and separately justified. -/
def IndependentSpongeLink (spec : ByteArray → Vector UInt8 32) : Prop :=
  ∀ bytes, EthLib.Cryptography.Hash.Keccak.Kernel.keccak256 bytes = spec bytes

/-- Under an independent sponge link, the adapter yields that specification's word. -/
theorem digestWord_of_independent (spec : ByteArray → Vector UInt8 32)
    (link : IndependentSpongeLink spec) (bytes : ByteArray) :
    digestWord (EthLib.Cryptography.Hash.Keccak.keccak256 bytes) = digestWord (spec bytes) := by
  rw [digestWord_record, link bytes]

/-- Actual execution returns the independent digest when its link is supplied. -/
theorem keccak_helper_actual_independent (s t : State) (x y : Word) (xs : List Word)
    (spec : ByteArray → Vector UInt8 32) (link : IndependentSpongeLink spec)
    (items : s.stack.val = x :: y :: xs) (run : keccak s = .continue t) :
    Gas.keccakCost s.memory.words x.toNat y.toNat ≤ s.gas ∧
    AdvancesMemory s t (Memory.Allocation.expand s.memory x.toNat y.toNat)
      (s.pc + 1) (s.gas - Gas.keccakCost s.memory.words x.toNat y.toNat)
      (digestWord (spec ⟨(Memory.readRange s.memory.store x.toNat y.toNat).toArray⟩) :: xs) := by
  have actual := keccak_helper_actual s t x y xs items run
  rw [digestWord_of_independent spec link] at actual
  exact actual

/-- A successful helper returns the exact digest bytes and preserves the input fields.

The contract applies at every program counter and for every code byte array.
The digest is relative to the shared Keccak-256 primitive.
-/
theorem keccak_helper_actual_output (s t : State) (offset length : Word) (xs : List Word)
    (items : s.stack.val = offset :: length :: xs) (run : keccak s = .continue t) :
    ∃ digest : Word,
      Gas.keccakCost s.memory.words offset.toNat length.toNat ≤ s.gas ∧
      t.stack.val = digest :: xs ∧
      Word.toBytesBE digest = ⟨(EthLib.Cryptography.Hash.Keccak.keccak256
        ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩).toArray⟩ ∧
      t.memory.words = max s.memory.words
        (Memory.Allocation.requiredWords offset.toNat length.toNat) ∧
      (∀ address, Memory.readByte t.memory.store address = Memory.readByte s.memory.store address) ∧
      t.pc = s.pc + 1 ∧
      t.gas = s.gas - Gas.keccakCost s.memory.words offset.toNat length.toNat ∧
      t.code = s.code ∧ t.context = s.context ∧ t.returnData = s.returnData := by
  obtain ⟨gas, code, memory, pc, remaining, stack, context, returnData, _tracker, _warm⟩ :=
    keccak_helper_actual s t offset length xs items run
  refine ⟨_, gas, stack, digestWord_encode _, ?_, ?_, pc, remaining, code, context, returnData⟩
  · rw [memory]; rfl
  · intro address
    rw [memory]
    rfl

/-- A successful KECCAK256 step has the same exact output contract. -/
theorem keccak_step_actual_output (s t : State) (offset length : Word) (xs : List Word)
    (at_ : At s (some .keccak)) (items : s.stack.val = offset :: length :: xs)
    (run : step s = .continue t) :
    ∃ digest : Word,
      Gas.keccakCost s.memory.words offset.toNat length.toNat ≤ s.gas ∧
      t.stack.val = digest :: xs ∧
      Word.toBytesBE digest = ⟨(EthLib.Cryptography.Hash.Keccak.keccak256
        ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩).toArray⟩ ∧
      t.memory.words = max s.memory.words
        (Memory.Allocation.requiredWords offset.toNat length.toNat) ∧
      (∀ address, Memory.readByte t.memory.store address = Memory.readByte s.memory.store address) ∧
      t.pc = s.pc + 1 ∧
      t.gas = s.gas - Gas.keccakCost s.memory.words offset.toNat length.toNat ∧
      t.code = s.code ∧ t.context = s.context ∧ t.returnData = s.returnData := by
  obtain ⟨bounds, decoded⟩ := at_
  have helper : keccak s = .continue t := by
    simpa only [step, dite_eq_left bounds, decoded] using run
  exact keccak_helper_actual_output s t offset length xs items helper

/-- Source-shaped outcomes for the helper at any program counter and code. -/
inductive KeccakHelperRule (s : State) : Outcome → Prop where
  | underflow : s.stack.val.length < 2 → KeccakHelperRule s (.exception s .stackUnderflow)
  | gas (x y xs) : s.stack.val = x :: y :: xs →
      s.gas < Gas.keccakCost s.memory.words x.toNat y.toNat →
      KeccakHelperRule s (.exception s .outOfGas)
  | success (t x y xs) : s.stack.val = x :: y :: xs →
      Gas.keccakCost s.memory.words x.toNat y.toNat ≤ s.gas →
      AdvancesMemory s t (Memory.Allocation.expand s.memory x.toNat y.toNat)
        (s.pc + 1) (s.gas - Gas.keccakCost s.memory.words x.toNat y.toNat)
        (digestWord (EthLib.Cryptography.Hash.Keccak.keccak256
          ⟨(Memory.readRange s.memory.store x.toNat y.toNat).toArray⟩) :: xs) →
      KeccakHelperRule s (.continue t)

/-- Every helper rule follows from execution. -/
theorem keccak_helper_rule_sound {s : State} {out : Outcome}
    (h : KeccakHelperRule s out) : keccak s = out := by
  cases h with
  | underflow short => exact keccak_helper_empty s short
  | gas x y xs items gas =>
    rw [keccak_helper_result s x y xs items]
    simp [Nat.not_le.mpr gas]
  | success t x y xs items gas fields =>
    rw [keccak_helper_result s x y xs items]
    simp only [ite_eq_left gas]
    apply congrArg Outcome.continue
    symm
    apply advancesMemory_eq
    exact fields

/-- Every helper input has one source-shaped outcome. -/
theorem keccak_helper_rule_total (s : State) : ∃ out, KeccakHelperRule s out := by
  cases items : s.stack.val with
  | nil => exact ⟨_, .underflow (by simp [items])⟩
  | cons x xs =>
    cases xs with
    | nil => exact ⟨_, .underflow (by simp [items])⟩
    | cons y ys =>
      by_cases gas : Gas.keccakCost s.memory.words x.toNat y.toNat ≤ s.gas
      · let stack : Stack := ⟨digestWord (EthLib.Cryptography.Hash.Keccak.keccak256
          ⟨(Memory.readRange s.memory.store x.toNat y.toNat).toArray⟩) :: ys,
          by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
        let t : State := { s with stack, pc := s.pc + 1, gas := s.gas - Gas.keccakCost s.memory.words x.toNat y.toNat, memory := Memory.Allocation.expand s.memory x.toNat y.toNat, memoryValid := Memory.Allocation.expand_valid_for_frame _ _ _ s.memoryValid }
        exact ⟨_, .success t x y ys items gas (by simp [AdvancesMemory, t, stack])⟩
      · exact ⟨_, .gas x y ys items (Nat.lt_of_not_ge gas)⟩

/-- The helper and its independent outcome rules agree on their entire domain. -/
theorem keccak_helper_iff_rule (s : State) (out : Outcome) :
    keccak s = out ↔ KeccakHelperRule s out := by
  constructor
  · intro run
    obtain ⟨result, rule⟩ := keccak_helper_rule_total s
    have eq := keccak_helper_rule_sound rule
    rw [run] at eq
    cases eq
    exact rule
  · exact keccak_helper_rule_sound

/-- Every helper outcome preserves the raw memory store. -/
theorem keccak_helper_outcome_store (s : State) (out : Outcome)
    (run : keccak s = out) : out.frame.memory.store = s.memory.store := by
  have rule := (keccak_helper_iff_rule s out).mp run
  cases rule with
  | underflow _ => rfl
  | gas _ _ _ _ _ => rfl
  | success t x y xs items gas fields =>
    change t.memory.store = s.memory.store
    rw [fields.2.1]
    rfl

/-- Every KECCAK256 step preserves raw store bytes, including exceptional outcomes. -/
theorem keccak_step_outcome_store (s : State) (out : Outcome)
    (at_ : At s (some .keccak)) (run : step s = out) :
    out.frame.memory.store = s.memory.store := by
  obtain ⟨bounds, decoded⟩ := at_
  have helper : keccak s = out := by simpa only [step, dite_eq_left bounds, decoded] using run
  exact keccak_helper_outcome_store s out helper

end EthLib.EVM.Frame
