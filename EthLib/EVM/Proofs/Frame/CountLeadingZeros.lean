module

public import EthLib.EVM.Proofs.Frame
public import EthLib.EVM.Proofs.Word.CountLeadingZeros

/-! Direct and opcode contracts for CLZ. -/

@[expose] public section
namespace EthLib.EVM.Frame

/-- The direct helper checks the stack before gas for any code and PC. -/
theorem clz_helper_empty (s : State) (empty : s.stack.val = []) :
    clz s = .exception s .stackUnderflow := by
  have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr empty
  simp [clz, pop, failStack]

/-- The direct helper checks gas after its successful pop. -/
theorem clz_helper_gas (s : State) (x : Word) (xs : List Word)
    (items : s.stack.val = x :: xs) (gas : s.gas < 5) :
    clz s = .exception s .outOfGas := by
  let rest : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  simp [clz, pop, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A nonempty stack and enough gas suffice, even when the original stack is full. -/
theorem clz_helper_success (s t : State) (x : Word) (xs : List Word)
    (items : s.stack.val = x :: xs) (gas : 5 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 5) (Word.countLeadingZeros x :: xs)) :
    clz s = .continue t := by
  let rest : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  let final : Stack := ⟨Word.countLeadingZeros x :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have push : rest.push (Word.countLeadingZeros x) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 5) final fields
  simp only [clz, pop, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- Actual helper success fixes the input, gas, and all fields in `Advances`. -/
theorem clz_helper_actual (s t : State) (run : clz s = .continue t) :
    ∃ x xs, s.stack.val = x :: xs ∧ 5 ≤ s.gas ∧
      Advances s t (s.pc + 1) (s.gas - 5) (Word.countLeadingZeros x :: xs) := by
  cases items : s.stack.val with
  | nil =>
    rw [clz_helper_empty s items] at run
    cases run
  | cons x xs =>
    by_cases gas : 5 ≤ s.gas
    · let stack : Stack := ⟨Word.countLeadingZeros x :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
      let u : State := { s with stack, pc := s.pc + 1, gas := s.gas - 5 }
      have fields : Advances s u (s.pc + 1) (s.gas - 5) (Word.countLeadingZeros x :: xs) := by simp [Advances, u, stack]
      have success := clz_helper_success s u x xs items gas fields
      rw [success] at run
      have eq : u = t := Outcome.continue.inj run
      subst t
      exact ⟨x, xs, rfl, gas, fields⟩
    · rw [clz_helper_gas s x xs items (Nat.lt_of_not_ge gas)] at run
      cases run

/-- Actual opcode success has the same complete fields as the direct helper. -/
theorem clz_step_actual (s t : State) (at_ : At s (some .clz))
    (run : step s = .continue t) :
    ∃ x xs, s.stack.val = x :: xs ∧ 5 ≤ s.gas ∧
      Advances s t (s.pc + 1) (s.gas - 5) (Word.countLeadingZeros x :: xs) := by
  obtain ⟨bounds, decoded⟩ := at_
  apply clz_helper_actual s t
  simpa only [step, dite_eq_left bounds, decoded] using run

/-- CLZ outcomes described by an independent mathematical result relation. -/
inductive ClzRule (s : State) : Outcome → Prop where
  | empty : s.stack.val = [] → ClzRule s (.exception s .stackUnderflow)
  | gas (x : Word) (xs : List Word) : s.stack.val = x :: xs → s.gas < 5 →
      ClzRule s (.exception s .outOfGas)
  | success (t : State) (x result : Word) (xs : List Word) :
      s.stack.val = x :: xs → 5 ≤ s.gas → Word.CountLeadingZerosSpec x result →
      Advances s t (s.pc + 1) (s.gas - 5) (result :: xs) → ClzRule s (.continue t)

/-- The independent relation characterizes every direct helper outcome. -/
theorem clz_helper_iff (s : State) (out : Outcome) : clz s = out ↔ ClzRule s out := by
  constructor
  · intro run
    cases items : s.stack.val with
    | nil =>
      rw [clz_helper_empty s items] at run
      subst out
      exact .empty items
    | cons x xs =>
      by_cases gas : 5 ≤ s.gas
      · let stack : Stack := ⟨Word.countLeadingZeros x :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
        let t : State := { s with stack, pc := s.pc + 1, gas := s.gas - 5 }
        have fields : Advances s t (s.pc + 1) (s.gas - 5) (Word.countLeadingZeros x :: xs) := by simp [Advances, t, stack]
        rw [clz_helper_success s t x xs items gas fields] at run
        subst out
        exact .success t x (Word.countLeadingZeros x) xs items gas
          ((Word.countLeadingZeros_spec x _).2 rfl) fields
      · rw [clz_helper_gas s x xs items (Nat.lt_of_not_ge gas)] at run
        subst out
        exact .gas x xs items (Nat.lt_of_not_ge gas)
  · intro rule
    cases rule with
    | empty items => exact clz_helper_empty s items
    | gas x xs items gas => exact clz_helper_gas s x xs items gas
    | success t x result xs items gas spec fields =>
      have eq := (Word.countLeadingZeros_spec x result).1 spec
      subst result
      exact clz_helper_success s t x xs items gas fields

/-- At CLZ, the same independent relation characterizes every opcode outcome. -/
theorem clz_step_iff (s : State) (out : Outcome) (at_ : At s (some .clz)) :
    step s = out ↔ ClzRule s out := by
  obtain ⟨bounds, decoded⟩ := at_
  simpa only [step, dite_eq_left bounds, decoded] using clz_helper_iff s out

end EthLib.EVM.Frame
