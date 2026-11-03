import EthLib.EVM.Proofs.Runner.Finish
import EthLib.EVM.Proofs.Runner.SelfBalance
import EthLib.EVM.Proofs.Runner.LogPreservation

open EthLib.EVM

namespace FinishConsumer

theorem first_forward (s : Frame.State) (kind : Frame.FinishKind) (empty : s.stack.val = []) :
    kind.execute s = .exception s .stackUnderflow :=
  (Frame.finish_iff_local kind s _).mpr (.empty kind s empty)

theorem second_forward (s : Frame.State) (kind : Frame.FinishKind) (first : Stack) (offset : Word)
    (items : s.stack.val = offset :: first.val) (empty : first.val = []) :
    kind.execute s = .exception { s with stack := first } .stackUnderflow :=
  (Frame.finish_iff_local kind s _).mpr (.second kind s first offset items empty)

theorem gas_forward (s : Frame.State) (kind : Frame.FinishKind) (first rest : Stack) (offset length : Word)
    (p : s.stack.val = offset :: first.val) (q : first.val = length :: rest.val)
    (gas : s.gas < Gas.rangeCost s.memory.words offset.toNat length.toNat) :
    kind.execute s = .exception { s with stack := rest } .outOfGas :=
  (Frame.finish_iff_local kind s _).mpr (.gas kind s first rest offset length p q gas)

theorem success_forward (s t : Frame.State) (kind : Frame.FinishKind) (first rest : Stack)
    (offset length : Word) (output : ByteArray) (p : s.stack.val = offset :: first.val)
    (q : first.val = length :: rest.val) (gas : Gas.rangeCost s.memory.words offset.toNat length.toNat ≤ s.gas)
    (eq : output = ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩)
    (bytes : Frame.FinishBytes s offset length output)
    (fields : Frame.AdvancesMemory s t (Memory.Allocation.expand s.memory offset.toNat length.toNat) s.pc
      (s.gas - Gas.rangeCost s.memory.words offset.toNat length.toNat) rest.val) :
    kind.execute s = kind.outcome t output :=
  (Frame.finish_iff_local kind s _).mpr (.success kind s t first rest offset length output p q gas eq bytes fields)

theorem return_converse (s t : Frame.State) (output : ByteArray) (run : Frame.returnOp s = .returned t output) :
    ∃ (first rest : Stack) (offset length : Word),
      s.stack.val = offset :: first.val ∧ first.val = length :: rest.val ∧
      Gas.rangeCost s.memory.words offset.toNat length.toNat ≤ s.gas ∧ Frame.FinishBytes s offset length output ∧
      Frame.AdvancesMemory s t (Memory.Allocation.expand s.memory offset.toNat length.toNat) s.pc
        (s.gas - Gas.rangeCost s.memory.words offset.toNat length.toNat) rest.val := by
  have local_ := (Frame.finish_iff_local .return_ s _).mp run
  cases local_ with
  | success _ first rest offset length data p q gas eq bytes fields =>
    exact ⟨first, rest, offset, length, p, q, gas, bytes, fields⟩

theorem revert_converse (s t : Frame.State) (gas : Nat) (output : ByteArray)
    (run : Frame.revertOp s = .revert t gas output) :
    ∃ (first rest : Stack) (offset length : Word),
      s.stack.val = offset :: first.val ∧ first.val = length :: rest.val ∧
      Gas.rangeCost s.memory.words offset.toNat length.toNat ≤ s.gas ∧ Frame.FinishBytes s offset length output ∧
      gas = t.gas ∧ Frame.AdvancesMemory s t (Memory.Allocation.expand s.memory offset.toNat length.toNat) s.pc
        (s.gas - Gas.rangeCost s.memory.words offset.toNat length.toNat) rest.val := by
  have local_ := (Frame.finish_iff_local .revert_ s _).mp run
  cases local_ with
  | success _ first rest offset length data p q enough eq bytes fields =>
    exact ⟨first, rest, offset, length, p, q, enough, bytes, rfl, fields⟩

theorem gas_converse (s t : Frame.State) (kind : Frame.FinishKind)
    (run : kind.execute s = .exception t .outOfGas) :
    ∃ (first rest : Stack) (offset length : Word),
      s.stack.val = offset :: first.val ∧ first.val = length :: rest.val ∧
      s.gas < Gas.rangeCost s.memory.words offset.toNat length.toNat ∧ t = { s with stack := rest } := by
  have local_ := (Frame.finish_iff_local kind s _).mp run
  cases kind <;> cases local_ with
  | gas first rest offset length p q gas => exact ⟨first, rest, offset, length, p, q, gas, rfl⟩

theorem underflow_converse (s t : Frame.State) (kind : Frame.FinishKind)
    (run : kind.execute s = .exception t .stackUnderflow) :
    (s.stack.val = [] ∧ t = s) ∨
    (∃ (first : Stack) (offset : Word), s.stack.val = offset :: first.val ∧ first.val = [] ∧ t = { s with stack := first }) := by
  have local_ := (Frame.finish_iff_local kind s _).mp run
  cases kind <;> cases local_ with
  | empty empty => exact Or.inl ⟨empty, rfl⟩
  | second first offset p empty => exact Or.inr ⟨first, offset, p, empty, rfl⟩

-- These applications use the actual dispatcher at either terminal opcode.
theorem dispatch_first_forward (s : Frame.State) (kind : Frame.FinishKind)
    (at_ : Frame.At s (some kind.opcode)) (empty : s.stack.val = []) :
    Frame.step s = .exception s .stackUnderflow :=
  (Frame.finish_step_iff_local kind s _ at_).mpr (.empty kind s empty)

theorem dispatch_second_forward (s : Frame.State) (kind : Frame.FinishKind)
    (at_ : Frame.At s (some kind.opcode)) (first : Stack) (offset : Word)
    (p : s.stack.val = offset :: first.val) (empty : first.val = []) :
    Frame.step s = .exception { s with stack := first } .stackUnderflow :=
  (Frame.finish_step_iff_local kind s _ at_).mpr (.second kind s first offset p empty)

theorem dispatch_gas_forward (s : Frame.State) (kind : Frame.FinishKind)
    (at_ : Frame.At s (some kind.opcode)) (first rest : Stack) (offset length : Word)
    (p : s.stack.val = offset :: first.val) (q : first.val = length :: rest.val)
    (gas : s.gas < Gas.rangeCost s.memory.words offset.toNat length.toNat) :
    Frame.step s = .exception { s with stack := rest } .outOfGas :=
  (Frame.finish_step_iff_local kind s _ at_).mpr (.gas kind s first rest offset length p q gas)

theorem dispatch_success_forward (s t : Frame.State) (kind : Frame.FinishKind)
    (at_ : Frame.At s (some kind.opcode)) (first rest : Stack) (offset length : Word) (output : ByteArray)
    (p : s.stack.val = offset :: first.val) (q : first.val = length :: rest.val)
    (gas : Gas.rangeCost s.memory.words offset.toNat length.toNat ≤ s.gas)
    (eq : output = ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩)
    (bytes : Frame.FinishBytes s offset length output)
    (fields : Frame.AdvancesMemory s t (Memory.Allocation.expand s.memory offset.toNat length.toNat) s.pc
      (s.gas - Gas.rangeCost s.memory.words offset.toNat length.toNat) rest.val) :
    Frame.step s = kind.outcome t output :=
  (Frame.finish_step_iff_local kind s _ at_).mpr (.success kind s t first rest offset length output p q gas eq bytes fields)

theorem dispatch_underflow_converse (s t : Frame.State) (kind : Frame.FinishKind)
    (at_ : Frame.At s (some kind.opcode)) (run : Frame.step s = .exception t .stackUnderflow) :
    (s.stack.val = [] ∧ t = s) ∨
    (∃ (first : Stack) (offset : Word), s.stack.val = offset :: first.val ∧ first.val = [] ∧ t = { s with stack := first }) := by
  have local_ := (Frame.finish_step_iff_local kind s _ at_).mp run
  cases kind <;> cases local_ with
  | empty empty => exact Or.inl ⟨empty, rfl⟩
  | second first offset p empty => exact Or.inr ⟨first, offset, p, empty, rfl⟩

theorem dispatch_gas_converse (s t : Frame.State) (kind : Frame.FinishKind)
    (at_ : Frame.At s (some kind.opcode)) (run : Frame.step s = .exception t .outOfGas) :
    ∃ (first rest : Stack) (offset length : Word), s.stack.val = offset :: first.val ∧
      first.val = length :: rest.val ∧ s.gas < Gas.rangeCost s.memory.words offset.toNat length.toNat ∧
      t = { s with stack := rest } := by
  have local_ := (Frame.finish_step_iff_local kind s _ at_).mp run
  cases kind <;> cases local_ with
  | gas first rest offset length p q gas => exact ⟨first, rest, offset, length, p, q, gas, rfl⟩

theorem dispatch_return_converse (s t : Frame.State) (output : ByteArray)
    (at_ : Frame.At s (some .return)) (run : Frame.step s = .returned t output) :
    ∃ (first rest : Stack) (offset length : Word), s.stack.val = offset :: first.val ∧
      first.val = length :: rest.val ∧ Gas.rangeCost s.memory.words offset.toNat length.toNat ≤ s.gas ∧
      output = ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩ ∧
      Frame.FinishBytes s offset length output ∧
      Frame.AdvancesMemory s t (Memory.Allocation.expand s.memory offset.toNat length.toNat) s.pc
        (s.gas - Gas.rangeCost s.memory.words offset.toNat length.toNat) rest.val := by
  have local_ := (Frame.finish_step_iff_local .return_ s _ at_).mp run
  cases local_ with
  | success _ first rest offset length data p q gas eq bytes fields =>
    exact ⟨first, rest, offset, length, p, q, gas, eq, bytes, fields⟩

theorem dispatch_revert_converse (s t : Frame.State) (gas : Nat) (output : ByteArray)
    (at_ : Frame.At s (some .revert)) (run : Frame.step s = .revert t gas output) :
    ∃ (first rest : Stack) (offset length : Word), s.stack.val = offset :: first.val ∧
      first.val = length :: rest.val ∧ Gas.rangeCost s.memory.words offset.toNat length.toNat ≤ s.gas ∧
      output = ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩ ∧
      Frame.FinishBytes s offset length output ∧ gas = t.gas ∧
      Frame.AdvancesMemory s t (Memory.Allocation.expand s.memory offset.toNat length.toNat) s.pc
        (s.gas - Gas.rangeCost s.memory.words offset.toNat length.toNat) rest.val := by
  have local_ := (Frame.finish_step_iff_local .revert_ s _ at_).mp run
  cases local_ with
  | success _ first rest offset length data p q enough eq bytes fields =>
    exact ⟨first, rest, offset, length, p, q, enough, eq, bytes, rfl, fields⟩

theorem returned_trace (s t : Frame.State) (fuel : Nat) (output : ByteArray)
    (run : Runner.run fuel s = .returned t output) :
    ∃ n, n ≤ fuel ∧ Runner.Terminates s n (.returned t output) :=
  Runner.terminates_of_run run (by intros; simp)

theorem reverted_trace (s t : Frame.State) (fuel gas : Nat) (output : ByteArray)
    (run : Runner.run fuel s = .reverted t gas output) :
    ∃ n, n ≤ fuel ∧ Runner.Terminates s n (.reverted t gas output) :=
  Runner.terminates_of_run run (by intros; simp)

theorem characterize_return (s t : Frame.State) (fuel : Nat) (output : ByteArray)
    (run : Runner.run fuel s = .returned t output) :
    ∃ n, n ≤ fuel ∧ Runner.Terminates s n (.returned t output) := by
  rcases (Runner.run_characterization fuel s _).mp run with ⟨_, impossible, _⟩ | trace
  · cases impossible
  · exact trace

theorem characterize_revert (s t : Frame.State) (fuel gas : Nat) (output : ByteArray)
    (run : Runner.run fuel s = .reverted t gas output) :
    ∃ n, n ≤ fuel ∧ Runner.Terminates s n (.reverted t gas output) := by
  rcases (Runner.run_characterization fuel s _).mp run with ⟨_, impossible, _⟩ | trace
  · cases impossible
  · exact trace

theorem exhausted_trace (s t : Frame.State) (fuel : Nat)
    (run : Runner.run fuel s = .exhausted t) : Runner.Continues s fuel t :=
  (Runner.run_exhausted_iff fuel s t).mp run

theorem trace_exhausted (s t : Frame.State) (fuel : Nat)
    (trace : Runner.Continues s fuel t) : Runner.run fuel s = .exhausted t :=
  (Runner.run_exhausted_iff fuel s t).mpr trace

theorem restricted_terminal_trace (s t : Frame.State) (fuel gas : Nat) (output : ByteArray)
    (trace : Runner.Terminates s fuel (.reverted t gas output))
    (noRevert : Runner.NoRevertRun fuel s) : False :=
  Runner.terminates_not_reverted trace noRevert

theorem terminal_trace (s : Frame.State) (fuel : Nat) (result : Runner.Result)
    (run : Runner.run fuel s = result) (terminal : ∀ t, result ≠ .exhausted t) :
    ∃ n, n ≤ fuel ∧ Runner.Terminates s n result := Runner.terminates_of_run run terminal

theorem characterize_exhaustion (s t : Frame.State) (fuel : Nat)
    (run : Runner.run fuel s = .exhausted t) : Runner.Continues s fuel t := by
  rcases (Runner.run_characterization fuel s _).mp run with ⟨u, eq, trace⟩ | ⟨n, _, trace⟩
  · cases eq; exact trace
  · exact (Runner.run_exhausted_iff fuel s t).mp run

theorem return_allowed (s t : Frame.State) (output : ByteArray)
    (at_ : Frame.At s (some .return)) (run : Frame.step s = .returned t output) :
    Runner.NoRevertRun 1 s := by
  refine ⟨?_, by simp [run]⟩
  intro conflict
  obtain ⟨_, ret⟩ := at_
  obtain ⟨_, rev⟩ := conflict
  rw [ret] at rev
  cases rev

theorem mixed_run (s : Frame.State) (kind : Frame.FinishKind) (length : Word) (xs : List Word)
    (room : xs.length ≤ 1022) (extraGas : Nat) :
    let cost := Gas.rangeCost s.memory.words 0 length.toNat
    let initial : Frame.State := { s with code := Runner.FinishProgram.program kind, pc := 0, gas := 2 + cost + extraGas, stack := ⟨length :: xs, by simp; omega⟩ }
    let output : ByteArray := ⟨(Memory.readRange s.memory.store 0 length.toNat).toArray⟩
    ∃ t, (match kind with
      | .return_ => Runner.run 2 initial = .returned t output
      | .revert_ => Runner.run 2 initial = .reverted t extraGas output) ∧
      t.gas = extraGas ∧ t.pc = 1 ∧ t.stack.val = xs ∧ t.logs = s.logs ∧
      Frame.FinishBytes s 0 length output := Runner.FinishProgram.run s kind length xs room extraGas

theorem return_extra_fuel (s t : Frame.State) (output : ByteArray) (fuel extra : Nat)
    (run : Runner.run fuel s = .returned t output) :
    Runner.run (fuel + extra) s = .returned t output :=
  Runner.run_terminal_stable run (by intros; simp) extra

theorem revert_extra_fuel (s t : Frame.State) (gas : Nat) (output : ByteArray) (fuel extra : Nat)
    (run : Runner.run fuel s = .reverted t gas output) :
    Runner.run (fuel + extra) s = .reverted t gas output :=
  Runner.run_terminal_stable run (by intros; simp) extra

theorem returned_retains_metadata (s t : Frame.State) (fuel : Nat) (output : ByteArray)
    (run : Runner.run fuel s = .returned t output) :
    t.tracker.parent = s.tracker.parent ∧ t.tracker.createdAccounts = s.tracker.createdAccounts ∧
      t.tracker.snapshots = s.tracker.snapshots ∧ ∃ suffix, t.logs = s.logs ++ suffix := by
  have metadata := Runner.SelfBalanceProgram.run_tracker_metadata_retained fuel s
  have logs := Runner.run_logs_prefix fuel s
  simp only [run, Runner.Result.frame] at metadata logs
  exact ⟨metadata.1, metadata.2.1, metadata.2.2, logs⟩

theorem reverted_retains_metadata (s t : Frame.State) (fuel gas : Nat) (output : ByteArray)
    (run : Runner.run fuel s = .reverted t gas output) :
    t.tracker.parent = s.tracker.parent ∧ t.tracker.createdAccounts = s.tracker.createdAccounts ∧
      t.tracker.snapshots = s.tracker.snapshots ∧ ∃ suffix, t.logs = s.logs ++ suffix := by
  have metadata := Runner.SelfBalanceProgram.run_tracker_metadata_retained fuel s
  have logs := Runner.run_logs_prefix fuel s
  simp only [run, Runner.Result.frame] at metadata logs
  exact ⟨metadata.1, metadata.2.1, metadata.2.2, logs⟩

theorem zero_fuel (s : Frame.State) : Runner.run 0 s = .exhausted s := rfl

theorem split_fuel (s : Frame.State) (fuel extra : Nat) :
    Runner.run (fuel + extra) s = match Runner.run fuel s with
      | .exhausted t => Runner.run extra t
      | r => r := Runner.run_add fuel extra s

end FinishConsumer
