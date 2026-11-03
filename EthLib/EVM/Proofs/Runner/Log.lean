module

public import EthLib.EVM.Proofs.Runner
public import EthLib.EVM.Proofs.Frame.LogLocal

@[expose] public section
namespace EthLib.EVM.Runner.LogProgram

/-- LOG0, LOG1 and STOP, each with an empty data range. -/
def program : ByteArray := ⟨#[0xa0, 0xa1, 0x00]⟩

/-- The constructed runner trace appends both entries in order. -/
theorem run (s : Frame.State) (topic : Word) (xs : List Word) (room : xs.length ≤ 1019) (g : Nat) :
    let initial : Frame.State := { s with code := program, pc := 0, gas := 1125 + g, isStatic := false, stack := ⟨0 :: 0 :: 0 :: 0 :: topic :: xs, by simp; omega⟩ }
    ∃ t, Runner.run 3 initial = .stopped t ∧ t.gas = g ∧ t.stack.val = xs ∧
      t.logs = s.logs ++ [⟨s.context.environment.currentTarget, [], ⟨#[]⟩⟩,
        ⟨s.context.environment.currentTarget, [Frame.logTopic topic], ⟨#[]⟩⟩] := by
  let initial : Frame.State := { s with code := program, pc := 0, gas := 1125 + g, isStatic := false, stack := ⟨0 :: 0 :: 0 :: 0 :: topic :: xs, by simp; omega⟩ }
  let first : Stack := ⟨0 :: 0 :: 0 :: topic :: xs, by simp; omega⟩
  let rest : Stack := ⟨0 :: 0 :: topic :: xs, by simp; omega⟩
  let first1 : Stack := ⟨0 :: topic :: xs, by simp; omega⟩
  let rest1 : Stack := ⟨topic :: xs, by simp; omega⟩
  let tail : Stack := ⟨xs, by omega⟩
  let entry0 : Frame.LogEntry := ⟨s.context.environment.currentTarget, [], ⟨#[]⟩⟩
  let entry1 : Frame.LogEntry := ⟨s.context.environment.currentTarget, [Frame.logTopic topic], ⟨#[]⟩⟩
  let s1 : Frame.State := { initial with pc := 1, gas := 750 + g, stack := rest, logs := s.logs ++ [entry0] }
  let s2 : Frame.State := { s1 with pc := 2, gas := g, stack := tail, logs := s.logs ++ [entry0, entry1] }
  let s3 : Frame.State := { s2 with pc := 3 }
  have h1 : Frame.Rule initial (.continue s1) := by
    apply Frame.Rule.logSuccess initial s1 ⟨0, by decide⟩ first rest rest 0 0 []
    · simp [Frame.At, initial, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp [initial, Gas.rangeCost, Gas.expansionCost, Memory.Allocation.requiredWords] <;> omega
    · simp [Frame.AdvancesMemory, s1, initial, rest, entry0, Memory.Allocation.expand, Memory.Allocation.requiredWords, Memory.readRange, Gas.rangeCost, Gas.expansionCost] <;> omega
  have h2 : Frame.Rule s1 (.continue s2) := by
    apply Frame.Rule.logSuccess s1 s2 ⟨1, by decide⟩ first1 rest1 tail 0 0 [topic]
    · simp [Frame.At, s1, initial, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp [s1, initial, Gas.rangeCost, Gas.expansionCost, Memory.Allocation.requiredWords] <;> omega
    · simp [Frame.AdvancesMemory, s2, s1, initial, tail, entry0, entry1, Memory.Allocation.expand, Memory.Allocation.requiredWords, Memory.readRange, Gas.rangeCost, Gas.expansionCost, List.append_assoc]
  have h3 : Frame.Rule s2 (.stop s3) := by
    apply Frame.Rule.stop
    simp [Frame.At, s2, s1, initial, program, ByteArray.size, -ByteArray.size_data, ByteArray.getElem_eq_getElem_data, Opcode.decode]
  have trace : Runner.Terminates initial 3 (.stopped s3) := .next h1 (.next h2 (.stop h3))
  exact ⟨s3, by simpa [initial] using Runner.run_of_terminates trace 0, rfl, rfl, by simp [s3, s2, entry0, entry1]⟩

end EthLib.EVM.Runner.LogProgram
