module

public import EthLib.EVM.Proofs.Runner
public import EthLib.EVM.Proofs.Frame.Memory
public import EthLib.EVM.Proofs.Gas

/-!
# Store and load program

Cancun execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`,
`vm/instructions/memory.py`, `mstore` and `mload`.
-/

@[expose] public section
namespace EthLib.EVM.Runner.Memory

/-- Store and then load the same offset. -/
def program : ByteArray := ⟨#[0x52, 0x51]⟩

/-- The loaded word is the arbitrary word stored by the preceding instruction. -/
theorem store_load (x value : Word) (xs : List Word) (room : xs.length ≤ 1021)
    (mem : EthLib.EVM.Memory.Allocation.State) (valid : EthLib.EVM.Memory.Allocation.Valid mem)
    (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State) (warmAddresses : List World.Address) (warmSlots : List (World.Address × Word)) (g : Nat) :
    ∃ t, Runner.run 2 ⟨program, 0, ⟨x :: value :: x :: xs, by simp; omega⟩,
      6 + Gas.rangeCost mem.words x.toNat 32 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots⟩ = .exhausted t ∧
      t.stack.val = value :: xs ∧ t.pc = 2 ∧ t.gas = g ∧ t.code = program := by
  let cost := Gas.rangeCost mem.words x.toNat 32
  let stored := EthLib.EVM.Memory.Allocation.storeWord mem x.toNat value
  let s : Frame.State := ⟨program, 0, ⟨x :: value :: x :: xs, by simp; omega⟩,
    6 + cost + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots⟩
  let s1 : Frame.State := { s with pc := 1, gas := 3 + g, stack := ⟨x :: xs, by simp; omega⟩, memory := stored, memoryValid := EthLib.EVM.Memory.Allocation.write_valid_for_frame _ _ _ valid }
  let s2 : Frame.State := { s1 with pc := 2, gas := g, stack := ⟨value :: xs, by simp; omega⟩, memory := (EthLib.EVM.Memory.Allocation.loadWord stored x.toNat).2, memoryValid := EthLib.EVM.Memory.Allocation.expand_valid_for_frame _ _ _ s1.memoryValid }
  have zero : Gas.rangeCost stored.words x.toNat 32 = 0 := by
    simp [stored, EthLib.EVM.Memory.Allocation.storeWord_words, Gas.rangeCost,
      Gas.expansion_idempotent]
  have loaded : (EthLib.EVM.Memory.Allocation.loadWord stored x.toNat).1 = value :=
    EthLib.EVM.Memory.Allocation.loadWord_storeWord _ _ _
  have h1 : Frame.Rule s (.continue s1) := by
    apply Frame.Rule.mstore s s1 x value (x :: xs)
    · simp [Frame.At, s, program, ByteArray.size, -ByteArray.size_data,
        ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s, cost]; omega
    · simp [Frame.AdvancesMemory, s, s1, stored, cost]; omega
  have h2 : Frame.Rule s1 (.continue s2) := by
    apply Frame.Rule.mload s1 s2 x xs
    · simp [Frame.At, s1, s, program, ByteArray.size, -ByteArray.size_data,
        ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s1, zero]
    · simp [Frame.AdvancesMemory, s1, s2, zero, loaded]
  have run := (Runner.run_exhausted_iff 2 s s2).mpr (.next h1 (.next h2 (.nil s2)))
  exact ⟨s2, by simpa [s, cost] using run, rfl, rfl, rfl, rfl⟩

end EthLib.EVM.Runner.Memory
