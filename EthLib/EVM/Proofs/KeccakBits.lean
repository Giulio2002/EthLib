module

public import EthLib.EVM.Proofs.Keccak
public import EthLib.Cryptography.Proofs.Hash.KeccakBitsRefinement

/-!
# KECCAK256 and the bit-coordinate sponge

The shared cryptography proof relates the executable hash to the independent bit model.
This module composes that result with the EVM execution contract.
-/

@[expose] public section
namespace EthLib.EVM.Frame

/-- The concrete independent bit sponge discharges the adapter's link obligation. -/
theorem independentSpongeLink_keccakBits :
    IndependentSpongeLink EthLib.Cryptography.Hash.KeccakBits.keccak256 := by
  intro bytes
  rw [← EthLib.Cryptography.Hash.Keccak.Kernel.keccak256_eq,
    EthLib.Cryptography.Hash.KeccakBits.keccak256_eq]

/-- Actual helper execution returns the independent bit sponge's bytes. -/
theorem keccak_helper_actual_bits (s t : State) (offset length : Word) (xs : List Word)
    (items : s.stack.val = offset :: length :: xs) (run : keccak s = .continue t) :
    ∃ digest : Word,
      Gas.keccakCost s.memory.words offset.toNat length.toNat ≤ s.gas ∧
      t.stack.val = digest :: xs ∧
      Word.toBytesBE digest = ⟨(EthLib.Cryptography.Hash.KeccakBits.keccak256
        ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩).toArray⟩ ∧
      t.memory.words = max s.memory.words
        (Memory.Allocation.requiredWords offset.toNat length.toNat) ∧
      (∀ address, Memory.readByte t.memory.store address = Memory.readByte s.memory.store address) ∧
      t.pc = s.pc + 1 ∧
      t.gas = s.gas - Gas.keccakCost s.memory.words offset.toNat length.toNat ∧
      t.code = s.code ∧ t.context = s.context ∧ t.returnData = s.returnData := by
  have actual := keccak_helper_actual_output s t offset length xs items run
  rw [EthLib.Cryptography.Hash.KeccakBits.keccak256_eq] at actual
  exact actual

/-- Actual KECCAK256 execution returns the independent bit sponge's bytes. -/
theorem keccak_step_actual_bits (s t : State) (offset length : Word) (xs : List Word)
    (at_ : At s (some .keccak)) (items : s.stack.val = offset :: length :: xs)
    (run : step s = .continue t) :
    ∃ digest : Word,
      Gas.keccakCost s.memory.words offset.toNat length.toNat ≤ s.gas ∧
      t.stack.val = digest :: xs ∧
      Word.toBytesBE digest = ⟨(EthLib.Cryptography.Hash.KeccakBits.keccak256
        ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩).toArray⟩ ∧
      t.memory.words = max s.memory.words
        (Memory.Allocation.requiredWords offset.toNat length.toNat) ∧
      (∀ address, Memory.readByte t.memory.store address = Memory.readByte s.memory.store address) ∧
      t.pc = s.pc + 1 ∧
      t.gas = s.gas - Gas.keccakCost s.memory.words offset.toNat length.toNat ∧
      t.code = s.code ∧ t.context = s.context ∧ t.returnData = s.returnData := by
  have actual := keccak_step_actual_output s t offset length xs at_ items run
  rw [EthLib.Cryptography.Hash.KeccakBits.keccak256_eq] at actual
  exact actual

end EthLib.EVM.Frame
