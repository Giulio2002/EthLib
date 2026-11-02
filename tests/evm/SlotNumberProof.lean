import EthLib.EVM.Proofs.Runner.SlotNumber
import EthLib.EVM.Proofs.Frame.SlotNumber

open EthLib.EVM

example (s t : Frame.State) (h : Frame.At s (some Frame.Observation.slotnum.opcode))
    (run : Frame.step s = .continue t) :
    2 ≤ s.gas ∧ s.stack.val.length < 1024 ∧
      Frame.Advances s t (s.pc + 1) (s.gas - 2)
        (Frame.observationWord (Frame.Observation.slotnum.value s) :: s.stack.val) :=
  Frame.step_observation_actual s t .slotnum h run

example (s t : Frame.State) (h : Frame.At s (some Frame.Observation.slotnum.opcode))
    (gas : 2 ≤ s.gas) (room : s.stack.val.length < 1024)
    (fields : Frame.Advances s t (s.pc + 1) (s.gas - 2)
      (BitVec.ofNat 256 (Frame.Observation.slotnum.value s) :: s.stack.val)) :
    Frame.step s = .continue t := Frame.step_observation s t .slotnum h gas room fields

example (s : Frame.State) (h : Frame.At s (some Frame.Observation.slotnum.opcode))
    (gas : s.gas < 2) : Frame.step s = .exception s .outOfGas :=
  Frame.step_observation_gas s .slotnum h gas

example (s : Frame.State) (h : Frame.At s (some Frame.Observation.slotnum.opcode))
    (gas : 2 ≤ s.gas) (full : s.stack.val.length = 1024) :
    Frame.step s = .exception s .stackOverflow :=
  Frame.step_observation_full s .slotnum h gas full

example (s : Frame.State) :
    (Frame.observationWord (Frame.Observation.slotnum.value s)).toNat =
      s.context.environment.slotNumber.val :=
  Frame.chainId_word_toNat s.context.environment.slotNumber

example (s t : Frame.State) (h : Frame.At s (some Frame.Observation.slotnum.opcode))
    (run : Frame.step s = .continue t) :
    ∃ w, Word.ofNat s.context.environment.slotNumber.val = .ok w ∧
      w.toNat = s.context.environment.slotNumber.val ∧
      t.stack.val = w :: s.stack.val ∧ t.context = s.context :=
  Frame.slotNumber_actual s t h run

example (s : Frame.State) (out : Frame.Outcome) :
    Frame.step s = out ↔ Frame.Rule s out := Frame.step_iff_rule s out

example (s : Frame.State) (out : Frame.Outcome) (run : Frame.step s = out) :
    out.frame.context = s.context :=
  Frame.outcome_context_unchanged ((Frame.step_iff_rule s out).mp run)

example (s t : Frame.State) (run : Frame.observe s (fun _ => s.context.environment.slotNumber.val) = .continue t) :
    2 ≤ s.gas ∧ s.stack.val.length < 1024 ∧
      Frame.Advances s t (s.pc + 1) (s.gas - 2)
        (Frame.observationWord s.context.environment.slotNumber.val :: s.stack.val) :=
  Frame.observe_actual s t _ run

example (s t : Frame.State) (gas : 2 ≤ s.gas) (room : s.stack.val.length < 1024)
    (fields : Frame.Advances s t (s.pc + 1) (s.gas - 2)
      (Frame.observationWord s.context.environment.slotNumber.val :: s.stack.val)) :
    Frame.observe s (fun _ => s.context.environment.slotNumber.val) = .continue t :=
  Frame.observe_success s t _ gas room fields

example (s : Frame.State) (gas : s.gas < 2) :
    Frame.observe s (fun _ => s.context.environment.slotNumber.val) = .exception s .outOfGas :=
  Frame.observe_gas s _ gas

example (s : Frame.State) (gas : 2 ≤ s.gas) (full : s.stack.val.length = 1024) :
    Frame.observe s (fun _ => s.context.environment.slotNumber.val) = .exception s .stackOverflow :=
  Frame.observe_full s _ gas full

-- A consumer recovers the complete runner result for arbitrary supplied metadata.
example (context : CallData.Context) (returnData : ByteArray) (xs : List Word)
    (room : xs.length ≤ 1022) (g : Nat) (mem : Memory.Allocation.State)
    (valid : Memory.Allocation.Valid mem) :
    ∃ t, Runner.run 3 ⟨Runner.SlotNumber.program, 0, ⟨xs, by omega⟩,
        4 + g, mem, valid, context, returnData⟩ = .stopped t ∧
      t.pc = 3 ∧ t.gas = g ∧ t.code = Runner.SlotNumber.program ∧ t.memory = mem ∧
      t.context = context ∧ t.returnData = returnData ∧
      t.stack.val = context.environment.number ::
        BitVec.ofNat 256 context.environment.slotNumber.val :: xs := by
  obtain ⟨t, execution, pc, gas, code, memory, preserved, returndata, stack⟩ :=
    Runner.SlotNumber.run context returnData xs room g mem valid
  exact ⟨t, execution, pc, gas, code, memory, preserved, returndata, stack⟩
