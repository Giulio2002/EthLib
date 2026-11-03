module

public import EthLib.EVM.Proofs.Frame.Balance

/-! Amsterdam `vm/instructions/storage.py`, `sload`, warms before charging. -/

@[expose] public section
namespace EthLib.EVM.Frame

/-- An empty stack fails before warming or charging. -/
theorem sload_underflow (s : State) (empty : s.stack.val = []) :
    sload s = .exception s .stackUnderflow := by
  have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr empty
  simp [sload, pop, failStack]

/-- A failed charge preserves the popped stack and the warmed slot. -/
theorem sload_gas (s : State) (rest : Stack) (x : Word)
    (items : s.stack.val = x :: rest.val) (gas : s.gas < SloadCost s x) :
    sload s = .exception { s with stack := rest, warmSlots := SloadWarm s x } .outOfGas := by
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have cost : (if s.warmSlots.contains (s.context.environment.currentTarget, x) then 100 else 2100) = SloadCost s x := by simp [SloadCost]
  have warms : (if s.warmSlots.contains (s.context.environment.currentTarget, x) then s.warmSlots else (s.context.environment.currentTarget, x) :: s.warmSlots) = SloadWarm s x := by simp [SloadWarm]
  simp only [sload, pop, cost, warms, charge, Gas.charge,
    ite_eq_right (Nat.not_le_of_gt gas)]

/-- A charged read fixes the full resulting frame. -/
theorem sload_success (s t : State) (rest : Stack) (x : Word)
    (items : s.stack.val = x :: rest.val) (gas : SloadCost s x ≤ s.gas)
    (fields : Advances { s with warmSlots := SloadWarm s x, tracker := SloadRead s x }
      t (s.pc + 1) (s.gas - SloadCost s x)
      (SloadValue s x :: rest.val)) :
    sload s = .continue t := by
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have room : rest.val.length < 1024 := by have bound := s.stack.property; rw [items] at bound; simp at bound; omega
  let stack : Stack := ⟨SloadValue s x :: rest.val, by simp; omega⟩
  have push : rest.push (SloadValue s x) = .ok stack :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨room, rfl⟩
  have eq := advances_eq { s with warmSlots := SloadWarm s x, tracker := SloadRead s x } t
    (s.pc + 1) (s.gas - SloadCost s x) stack fields
  subst t
  have value : (TransactionTracker.getStorage s.tracker s.context.environment.currentTarget x).1 = SloadValue s x := by
    unfold TransactionTracker.getStorage SloadValue
    cases h : s.tracker.writes.storageWrites.lookup (s.context.environment.currentTarget, x) <;> simp [h]
  have read : (TransactionTracker.getStorage s.tracker s.context.environment.currentTarget x).2 = SloadRead s x := rfl
  have cost : (if s.warmSlots.contains (s.context.environment.currentTarget, x) then 100 else 2100) = SloadCost s x := by simp [SloadCost]
  have warms : (if s.warmSlots.contains (s.context.environment.currentTarget, x) then s.warmSlots else (s.context.environment.currentTarget, x) :: s.warmSlots) = SloadWarm s x := by simp [SloadWarm]
  simp only [sload, pop, cost, warms, charge, Gas.charge, ite_eq_left gas, value, read, push]

/-- Success is equivalent to a popped operand, affordable gas and all output fields. -/
theorem sload_success_iff (s t : State) :
    sload s = .continue t ↔ ∃ (rest : Stack) (x : Word),
      s.stack.val = x :: rest.val ∧ SloadCost s x ≤ s.gas ∧
      Advances { s with warmSlots := SloadWarm s x, tracker := SloadRead s x }
        t (s.pc + 1) (s.gas - SloadCost s x)
        (SloadValue s x :: rest.val) := by
  constructor
  · intro run
    cases items : s.stack.val with
    | nil =>
      have bad := sload_underflow s items
      rw [run] at bad
      cases bad
    | cons x xs =>
      let rest : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
      have items' : s.stack.val = x :: rest.val := items
      by_cases gas : SloadCost s x ≤ s.gas
      · let stack : Stack := ⟨SloadValue s x :: xs, by
          have bound := s.stack.property; rw [items] at bound; simp at bound; simp; omega⟩
        let target : State := { s with tracker := SloadRead s x, warmSlots := SloadWarm s x, stack, pc := s.pc + 1, gas := s.gas - SloadCost s x }
        have fields : Advances { s with warmSlots := SloadWarm s x, tracker := SloadRead s x }
            target (s.pc + 1) (s.gas - SloadCost s x)
            (SloadValue s x :: rest.val) := by
          simp [Advances, target, stack, rest]
        have eq := sload_success s target rest x items' gas fields
        rw [run] at eq
        have eqTarget : t = target := Outcome.continue.inj eq
        subst t
        exact ⟨rest, x, rfl, gas, fields⟩
      · have bad := sload_gas s rest x items' (Nat.lt_of_not_ge gas)
        rw [run] at bad
        cases bad
  · rintro ⟨rest, x, items, gas, fields⟩
    exact sload_success s t rest x items gas fields

/-- All failures are either underflow or a charge failure after warming. -/
theorem sload_exception_iff (s input : State) (reason : Exception) :
    sload s = .exception input reason ↔
      (s.stack.val = [] ∧ input = s ∧ reason = .stackUnderflow) ∨
      (∃ (rest : Stack) (x : Word), s.stack.val = x :: rest.val ∧
        s.gas < SloadCost s x ∧
        input = { s with stack := rest, warmSlots := SloadWarm s x } ∧
        reason = .outOfGas) := by
  cases items : s.stack.val with
  | nil =>
    rw [sload_underflow s items]
    simp [eq_comm]
  | cons x xs =>
    let rest : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
    have items' : s.stack.val = x :: rest.val := items
    by_cases gas : SloadCost s x ≤ s.gas
    · let stack : Stack := ⟨SloadValue s x :: xs, by
        have bound := s.stack.property; rw [items] at bound; simp at bound; simp; omega⟩
      let target : State := { s with tracker := SloadRead s x, warmSlots := SloadWarm s x, stack, pc := s.pc + 1, gas := s.gas - SloadCost s x }
      have fields : Advances { s with warmSlots := SloadWarm s x, tracker := SloadRead s x }
          target (s.pc + 1) (s.gas - SloadCost s x)
          (SloadValue s x :: rest.val) := by simp [Advances, target, stack, rest]
      rw [sload_success s target rest x items' gas fields]
      simp only [reduceCtorEq, false_iff]
      rintro (⟨empty, _, _⟩ | ⟨r, y, equal, low, _, _⟩)
      · cases empty
      · have eq : x = y := (List.cons.inj equal).1
        rw [← eq] at low
        omega
    · rw [sload_gas s rest x items' (Nat.lt_of_not_ge gas)]
      constructor
      · intro eq
        cases eq
        exact Or.inr ⟨rest, x, rfl, Nat.lt_of_not_ge gas, rfl, rfl⟩
      · rintro (⟨empty, _, _⟩ | ⟨r, y, equal, _, eqInput, eqReason⟩)
        · cases empty
        · have both : x = y ∧ rest.val = r.val := by simpa [items, rest] using equal
          have restEq : rest = r := Subtype.ext both.2
          rcases both with ⟨rfl, _⟩
          cases restEq
          subst input
          subst reason
          rfl

/-- Slot warming adds exactly the current-target key pair. -/
theorem sload_warm_membership (s : State) (key : Word) (slot : World.Address × Word) :
    slot ∈ SloadWarm s key ↔ slot = (s.context.environment.currentTarget, key) ∨ slot ∈ s.warmSlots := by
  by_cases warm : (s.context.environment.currentTarget, key) ∈ s.warmSlots
  · simp [SloadWarm, warm]; intro eq; subst slot; exact warm
  · simp [SloadWarm, warm]

/-- Amsterdam classifies warm and cold slot gas from the prior set. -/
theorem sload_cost_cases (s : State) (key : Word) :
    ((s.context.environment.currentTarget, key) ∈ s.warmSlots → SloadCost s key = 100) ∧
    ((s.context.environment.currentTarget, key) ∉ s.warmSlots → SloadCost s key = 2100) := by
  simp [SloadCost]

/-- Every other instruction preserves the whole warm-slot list. -/
theorem outcome_slots_unchanged_of_not_sload {s : State} {out : Outcome}
    (notSload : ¬ At s (some .sload)) (rule : Rule s out) :
    out.frame.warmSlots = s.warmSlots := by
  cases rule <;> simp_all [Outcome.frame, Advances, AdvancesMemory]

/-- Every rule retains all previously warm slots. -/
theorem outcome_slots_monotone {s : State} {out : Outcome} (rule : Rule s out)
    (slot : World.Address × Word) (warm : slot ∈ s.warmSlots) : slot ∈ out.frame.warmSlots := by
  cases rule <;> simp_all [Outcome.frame, Advances, AdvancesMemory, SloadWarm] <;> split <;> simp_all

/-- Effective storage follows the independent tracker map and set reference. -/
theorem sload_storage_value (s : State) (key : Word) :
    TransactionTracker.StorageValue (TransactionState.Reference.observe s.tracker)
      s.context.environment.currentTarget key (SloadValue s key) := by
  have spec := (TransactionTracker.getStorage_spec s.tracker s.context.environment.currentTarget key).1
  have value : (TransactionTracker.getStorage s.tracker s.context.environment.currentTarget key).1 = SloadValue s key := by
    unfold TransactionTracker.getStorage SloadValue
    cases h : s.tracker.writes.storageWrites.lookup (s.context.environment.currentTarget, key) <;> simp [h]
  rw [value] at spec
  exact spec

/-- Opcode 0x54 dispatches to the helper. -/
theorem step_sload (s : State) (at_ : At s (some .sload)) : step s = sload s := by
  obtain ⟨bounds, decoded⟩ := at_
  simp only [step, dite_eq_left bounds, decoded]

end EthLib.EVM.Frame
