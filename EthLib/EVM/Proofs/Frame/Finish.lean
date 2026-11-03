module

public import EthLib.EVM.Proofs.Frame
public import EthLib.EVM.Proofs.Memory.Ranges
import Aesop

@[expose] public section
namespace EthLib.EVM.Frame

/-- Output bytes observe the original memory at the popped offset. -/
def FinishBytes (s : State) (offset length : Word) (output : ByteArray) : Prop :=
  output.size = length.toNat ∧ ∀ i, (h : i < output.size) →
    output[i] = Memory.readByte s.memory.store (offset.toNat + i)

/-- The memory reader satisfies the independent byte observation. -/
theorem finish_bytes (s : State) (offset length : Word) :
    FinishBytes s offset length ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩ := by
  constructor
  · simp [ByteArray.size, Memory.readRange_length]
  · intro i h
    have bound : i < length.toNat := by simpa [ByteArray.size, Memory.readRange_length] using h
    simpa [ByteArray.getElem_eq_getElem_data] using Memory.readRange_getElem s.memory.store offset.toNat length.toNat i bound

/-- The source-order helper cases at arbitrary code and program counter. -/
inductive FinishLocal : FinishKind → State → Outcome → Prop where
  | empty (kind : FinishKind) (s : State) : s.stack.val = [] → FinishLocal kind s (.exception s .stackUnderflow)
  | second (kind : FinishKind) (s : State) (first : Stack) (offset : Word) :
      s.stack.val = offset :: first.val → first.val = [] →
      FinishLocal kind s (.exception { s with stack := first } .stackUnderflow)
  | gas (kind : FinishKind) (s : State) (first rest : Stack) (offset length : Word) :
      s.stack.val = offset :: first.val → first.val = length :: rest.val →
      s.gas < Gas.rangeCost s.memory.words offset.toNat length.toNat →
      FinishLocal kind s (.exception { s with stack := rest } .outOfGas)
  | success (kind : FinishKind) (s t : State) (first rest : Stack) (offset length : Word) (output : ByteArray) :
      s.stack.val = offset :: first.val → first.val = length :: rest.val →
      Gas.rangeCost s.memory.words offset.toNat length.toNat ≤ s.gas →
      output = ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩ →
      FinishBytes s offset length output →
      AdvancesMemory s t (Memory.Allocation.expand s.memory offset.toNat length.toNat) s.pc
        (s.gas - Gas.rangeCost s.memory.words offset.toNat length.toNat) rest.val →
      FinishLocal kind s (kind.outcome t output)

/-- Both helpers have the same source-order implementation. -/
def FinishKind.execute (kind : FinishKind) (s : State) : Outcome :=
  match kind with
  | .return_ => returnOp s
  | .revert_ => revertOp s

/-- Every independent source case determines the helper result. -/
theorem finishLocal_sound {kind : FinishKind} {s : State} {out : Outcome}
    (h : FinishLocal kind s out) : kind.execute s = out := by
  cases h with
  | empty empty =>
    have p := (Proofs.Stack.pop_underflow_iff _).mpr empty
    cases kind <;> simp [FinishKind.execute, returnOp, revertOp, finish, p, failStack]
  | second first offset items empty =>
    have p := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
    have q := (Proofs.Stack.pop_underflow_iff _).mpr empty
    cases kind <;> simp [FinishKind.execute, returnOp, revertOp, finish, p, q, failStack]
  | gas first rest offset length items items' gas =>
    have p := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
    have q := (Proofs.Stack.pop_ok_iff _ _ _).mpr items'
    cases kind <;> simp [FinishKind.execute, returnOp, revertOp, finish, p, q, charge, Gas.charge, Nat.not_le_of_gt gas]
  | success t first rest offset length output items items' gas eq _bytes fields =>
    subst output
    have p := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
    have q := (Proofs.Stack.pop_ok_iff _ _ _).mpr items'
    have frame := advancesMemory_eq s t _ (Memory.Allocation.expand_valid_for_frame _ _ _ s.memoryValid)
      s.pc (s.gas - Gas.rangeCost s.memory.words offset.toNat length.toNat) rest fields
    subst t
    cases kind <;> simp [FinishKind.execute, FinishKind.outcome, returnOp, revertOp, finish, p, q, charge, Gas.charge, gas]

/-- Independent source cases cover every input frame. -/
theorem finishLocal_total (kind : FinishKind) (s : State) : ∃ out, FinishLocal kind s out := by
  cases items : s.stack.val with
  | nil => exact ⟨_, .empty kind s items⟩
  | cons offset xs =>
    let first : Stack := ⟨xs, by have h := s.stack.property; rw [items] at h; simp at h; omega⟩
    have items' : s.stack.val = offset :: first.val := items
    cases second : first.val with
    | nil => exact ⟨_, .second kind s first offset items' second⟩
    | cons length ys =>
      let rest : Stack := ⟨ys, by have h := first.property; rw [second] at h; simp at h; omega⟩
      have second' : first.val = length :: rest.val := second
      by_cases gas : Gas.rangeCost s.memory.words offset.toNat length.toNat ≤ s.gas
      · let t := { s with stack := rest, gas := s.gas - Gas.rangeCost s.memory.words offset.toNat length.toNat, memory := Memory.Allocation.expand s.memory offset.toNat length.toNat, memoryValid := Memory.Allocation.expand_valid_for_frame _ _ _ s.memoryValid }
        exact ⟨_, .success kind s t first rest offset length _ items' second' gas rfl (finish_bytes s offset length) (by simp [AdvancesMemory, t])⟩
      · exact ⟨_, .gas kind s first rest offset length items' second' (Nat.lt_of_not_ge gas)⟩

/-- Each direct helper agrees with the independent cases. -/
theorem finish_iff_local (kind : FinishKind) (s : State) (out : Outcome) :
    kind.execute s = out ↔ FinishLocal kind s out := by
  constructor
  · intro run
    obtain ⟨result, cases⟩ := finishLocal_total kind s
    have sound := finishLocal_sound cases
    rw [run] at sound
    subst result
    exact cases
  · exact finishLocal_sound

/-- The local cases also characterize actual opcode dispatch. -/
theorem finish_step_iff_local (kind : FinishKind) (s : State) (out : Outcome)
    (at_ : At s (some kind.opcode)) : step s = out ↔ FinishLocal kind s out := by
  obtain ⟨bounds, decoded⟩ := at_
  cases kind with
  | return_ =>
    simp [FinishKind.opcode] at decoded
    simpa only [step, dite_eq_left bounds, decoded, FinishKind.execute] using finish_iff_local .return_ s out
  | revert_ =>
    simp [FinishKind.opcode] at decoded
    simpa only [step, dite_eq_left bounds, decoded, FinishKind.execute] using finish_iff_local .revert_ s out

end EthLib.EVM.Frame
