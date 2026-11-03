module

public import EthLib.EVM.Proofs.Frame.SstoreLocal
public import EthLib.EVM.Proofs.Runner.Sload
import Aesop

/-! A mixed SSTORE, SLOAD, STOP program with caller-supplied transaction state. -/

@[expose] public section
namespace EthLib.EVM.Runner.SstoreProgram

/-- Write a slot, read a slot, then stop. -/
def program : ByteArray := ⟨#[0x55, 0x54, 0x00]⟩

/-- The actual runner follows independently specified SSTORE and SLOAD transitions. -/
theorem run_mixed (s t u : Frame.State) (rest : Stack) (key : Word)
    (code : s.code = program) (pc : s.pc = 0)
    (store : Frame.SstoreLocal s (.continue t))
    (items : t.stack.val = key :: rest.val) (gas : Frame.SloadCost t key ≤ t.gas)
    (load : Frame.Advances { t with warmSlots := Frame.SloadWarm t key, tracker := Frame.SloadRead t key }
      u (t.pc + 1) (t.gas - Frame.SloadCost t key) (Frame.SloadValue t key :: rest.val)) :
    Runner.run 3 s = .stopped { u with pc := 3 } ∧
      u.tracker = Frame.SloadRead t key ∧ u.warmSlots = Frame.SloadWarm t key := by
  have atStore : Frame.At s (some .sstore) := by
    simp [Frame.At, code, pc, program, ByteArray.size, -ByteArray.size_data,
      ByteArray.getElem_eq_getElem_data, Opcode.decode]
  have stepStore : Frame.step s = .continue t := by
    obtain ⟨bounds, decoded⟩ := atStore
    simpa only [Frame.step, dite_eq_left bounds, decoded] using Frame.sstore_local_sound store
  have codeT : t.code = program := (Frame.continue_code_unchanged stepStore).trans code
  have pcT : t.pc = 1 := by
    cases store
    all_goals simp_all [Frame.SstoreReady, Frame.SstoreReadFields, Frame.SstoreCreditFields,
      Frame.SstoreExecutionFields, Frame.SstoreChargeFields, Frame.SstoreMeterRetained,
      Frame.SstoreWriteFields]
    all_goals aesop
  have atLoad : Frame.At t (some .sload) := by
    simp [Frame.At, codeT, pcT, program, ByteArray.size, -ByteArray.size_data,
      ByteArray.getElem_eq_getElem_data, Opcode.decode]
  have codeU : u.code = program := load.1.trans codeT
  have pcU : u.pc = 2 := by simpa [pcT] using load.2.2.1
  have atStop : Frame.At u (some .stop) := by
    simp [Frame.At, codeU, pcU, program, ByteArray.size, -ByteArray.size_data,
      ByteArray.getElem_eq_getElem_data, Opcode.decode]
  have r1 : Frame.Rule s (.continue t) := (Frame.step_iff_rule _ _).mp stepStore
  have r2 : Frame.Rule t (.continue u) := .sload t u rest key atLoad items gas load
  have r3 : Frame.Rule u (.stop { u with pc := 3 }) := by
    simpa [pcU] using Frame.Rule.stop u atStop
  have trace : Runner.Terminates s 3 (.stopped { u with pc := 3 }) := .next r1 (.next r2 (.stop r3))
  exact ⟨by simpa using Runner.run_of_terminates trace 0, load.2.2.2.2.2.2.2.1,
    load.2.2.2.2.2.2.2.2.2.1⟩

end EthLib.EVM.Runner.SstoreProgram
