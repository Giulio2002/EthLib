module

public import EthLib.EVM.Proofs.Runner
public import EthLib.EVM.Proofs.Keccak
public import EthLib.EVM.Proofs.Frame.Memory

/-!
# Calldata copy followed by KECCAK256

Cancun execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`,
`instructions/environment.py`, `calldatacopy`, and `instructions/keccak.py`, `keccak`.
-/

@[expose] public section
namespace EthLib.EVM.Runner.CopyKeccak

/-- Copy 32 bytes, then hash them. -/
def program : ByteArray := ⟨#[0x37, 0x20]⟩

/-- The bounded program hashes the copied source bytes and preserves its context. -/
theorem run_copy_keccak (context : CallData.Context) (returnData : ByteArray)
    (source : Word) (xs : List Word) (room : xs.length ≤ 1019)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem) (g : Nat) :
    let bytes := CallData.readRange context.data source.toNat 32
    let m := Memory.Allocation.write mem 0 bytes
    let c1 := Gas.inputCopyCost mem.words 0 32
    let c2 := Gas.keccakCost m.words 0 32
    ∃ t, run 2 ⟨program, 0, ⟨[0, source, 32, 0, 32] ++ xs, by simp; omega⟩,
        c1 + c2 + g, mem, valid, context, returnData⟩ = .exhausted t ∧
      t.stack.val = Frame.digestWord (EthLib.Cryptography.Hash.Keccak.keccak256 ⟨bytes.toArray⟩) :: xs ∧
      t.pc = 2 ∧ t.gas = g ∧ t.memory.store = m.store ∧ t.context = context ∧
      t.returnData = returnData ∧ Memory.readRange t.memory.store 0 32 = bytes := by
  dsimp only
  let bytes := CallData.readRange context.data source.toNat 32
  let m := Memory.Allocation.write mem 0 bytes
  let c1 := Gas.inputCopyCost mem.words 0 32
  let c2 := Gas.keccakCost m.words 0 32
  let s : Frame.State := ⟨program, 0, ⟨[0, source, 32, 0, 32] ++ xs, by simp; omega⟩, c1+c2+g, mem, valid, context, returnData⟩
  let s1 : Frame.State := { s with pc := 1, gas := c2+g, stack := ⟨[0, 32] ++ xs, by simp; omega⟩, memory := m, memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ valid }
  let digest := Frame.digestWord (EthLib.Cryptography.Hash.Keccak.keccak256 ⟨bytes.toArray⟩)
  let s2 : Frame.State := { s1 with pc := 2, gas := g, stack := ⟨digest :: xs, by simp; omega⟩, memory := Memory.Allocation.expand m 0 32, memoryValid := Memory.Allocation.expand_valid_for_frame _ _ _ s1.memoryValid }
  have len : bytes.length = 32 := by simp [bytes, Proofs.CallData.readRange_length]
  have read : Memory.readRange m.store 0 32 = bytes := by
    change Memory.readRange (Memory.writeRange mem.store 0 bytes) 0 32 = bytes
    rw [← len, Memory.readRange_writeRange]
  have h1 : Frame.Rule s (.continue s1) := by
    apply Frame.Rule.inputCopy s s1 .calldata 0 source 32 ([0, 32] ++ xs)
    · simp [Frame.At, Frame.InputSource.opcode, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s, c1]; omega
    · simp [Frame.AdvancesMemory, Frame.InputSource.bytes, s, s1, m, bytes, c1]; omega
  have h2 : Frame.Rule s1 (.continue s2) := by
    apply Frame.Rule.keccak s1 s2 0 32 xs
    · simp [Frame.At, s1, s, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · simp [s1, c2]
    · simp [Frame.AdvancesMemory, s1, s2, s, m, c2, digest, read]
  have trace : Runner.Continues s 2 s2 := .next h1 (.next h2 (.nil s2))
  have result := (Runner.run_exhausted_iff 2 s s2).mpr trace
  refine ⟨s2, result, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · rfl
  · exact read

end EthLib.EVM.Runner.CopyKeccak
