module

public import EthLib.EVM.Proofs.Frame.Balance

/-! Source-order contracts for Amsterdam `environment.py`, `extcodehash`. -/

@[expose] public section
namespace EthLib.EVM.Frame

/-- An empty stack fails before warming or charging. -/
theorem extCodeHash_underflow (s : State) (empty : s.stack.val = []) :
    extCodeHash s = .exception s .stackUnderflow := by
  have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr empty
  simp [extCodeHash, pop, failStack]

/-- A failed charge preserves the popped stack and the warmed address. -/
theorem extCodeHash_gas (s : State) (rest : Stack) (x : Word)
    (items : s.stack.val = x :: rest.val) (gas : s.gas < BalanceCost s (BalanceAddress x)) :
    extCodeHash s = .exception { s with stack := rest, warmAddresses := BalanceWarm s (BalanceAddress x) } .outOfGas := by
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have address : balanceAddress x = BalanceAddress x := rfl
  have cost : (if s.warmAddresses.contains (BalanceAddress x) then 100 else 3000) = BalanceCost s (BalanceAddress x) := by simp [BalanceCost]
  have warms : (if s.warmAddresses.contains (BalanceAddress x) then s.warmAddresses else BalanceAddress x :: s.warmAddresses) = BalanceWarm s (BalanceAddress x) := by simp [BalanceWarm]
  simp only [extCodeHash, pop, address, cost, warms, charge, Gas.charge,
    ite_eq_right (Nat.not_le_of_gt gas)]

/-- A charged read fixes the full resulting frame. -/
theorem extCodeHash_success (s t : State) (rest : Stack) (x : Word)
    (items : s.stack.val = x :: rest.val) (gas : BalanceCost s (BalanceAddress x) ≤ s.gas)
    (fields : Advances { s with warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x) }
      t (s.pc + 1) (s.gas - BalanceCost s (BalanceAddress x))
      (ExtCodeHashValue s (BalanceAddress x) :: rest.val)) :
    extCodeHash s = .continue t := by
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have room : rest.val.length < 1024 := by have bound := s.stack.property; rw [items] at bound; simp at bound; omega
  let stack : Stack := ⟨ExtCodeHashValue s (BalanceAddress x) :: rest.val, by simp; omega⟩
  have push : rest.push (ExtCodeHashValue s (BalanceAddress x)) = .ok stack :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨room, rfl⟩
  have eq := advances_eq { s with warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x) } t
    (s.pc + 1) (s.gas - BalanceCost s (BalanceAddress x)) stack fields
  subst t
  have value : (if (TransactionTracker.getAccount s.tracker (BalanceAddress x)).1 == World.emptyAccount then 0 else (TransactionTracker.getAccount s.tracker (BalanceAddress x)).1.codeHash) = ExtCodeHashValue s (BalanceAddress x) := by simp [ExtCodeHashValue, BalanceAccount, TransactionTracker.getAccount, TransactionTracker.getAccountOptional, World.getAccountOptional]; rfl
  have read : (TransactionTracker.getAccount s.tracker (BalanceAddress x)).2 = BalanceRead s (BalanceAddress x) := rfl
  have address : balanceAddress x = BalanceAddress x := rfl
  have cost : (if s.warmAddresses.contains (BalanceAddress x) then 100 else 3000) = BalanceCost s (BalanceAddress x) := by simp [BalanceCost]
  have warms : (if s.warmAddresses.contains (BalanceAddress x) then s.warmAddresses else BalanceAddress x :: s.warmAddresses) = BalanceWarm s (BalanceAddress x) := by simp [BalanceWarm]
  simp only [extCodeHash, pop, address, cost, warms, charge, Gas.charge, ite_eq_left gas, value, read, push]

/-- Success is equivalent to a popped operand, affordable gas and all output fields. -/
theorem extCodeHash_success_iff (s t : State) :
    extCodeHash s = .continue t ↔ ∃ (rest : Stack) (x : Word),
      s.stack.val = x :: rest.val ∧ BalanceCost s (BalanceAddress x) ≤ s.gas ∧
      Advances { s with warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x) }
        t (s.pc + 1) (s.gas - BalanceCost s (BalanceAddress x))
        (ExtCodeHashValue s (BalanceAddress x) :: rest.val) := by
  constructor
  · intro run
    cases items : s.stack.val with
    | nil =>
      have bad := extCodeHash_underflow s items
      rw [run] at bad
      cases bad
    | cons x xs =>
      let rest : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
      have items' : s.stack.val = x :: rest.val := items
      by_cases gas : BalanceCost s (BalanceAddress x) ≤ s.gas
      · let stack : Stack := ⟨ExtCodeHashValue s (BalanceAddress x) :: xs, by
          have bound := s.stack.property; rw [items] at bound; simp at bound; simp; omega⟩
        let target : State := { s with tracker := BalanceRead s (BalanceAddress x), warmAddresses := BalanceWarm s (BalanceAddress x), stack, pc := s.pc + 1, gas := s.gas - BalanceCost s (BalanceAddress x) }
        have fields : Advances { s with warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x) }
            target (s.pc + 1) (s.gas - BalanceCost s (BalanceAddress x))
            (ExtCodeHashValue s (BalanceAddress x) :: rest.val) := by
          simp [Advances, target, stack, rest]
        have eq := extCodeHash_success s target rest x items' gas fields
        rw [run] at eq
        have eqTarget : t = target := Outcome.continue.inj eq
        subst t
        exact ⟨rest, x, rfl, gas, fields⟩
      · have bad := extCodeHash_gas s rest x items' (Nat.lt_of_not_ge gas)
        rw [run] at bad
        cases bad
  · rintro ⟨rest, x, items, gas, fields⟩
    exact extCodeHash_success s t rest x items gas fields

/-- All failures are either underflow or a charge failure after warming. -/
theorem extCodeHash_exception_iff (s input : State) (reason : Exception) :
    extCodeHash s = .exception input reason ↔
      (s.stack.val = [] ∧ input = s ∧ reason = .stackUnderflow) ∨
      (∃ (rest : Stack) (x : Word), s.stack.val = x :: rest.val ∧
        s.gas < BalanceCost s (BalanceAddress x) ∧
        input = { s with stack := rest, warmAddresses := BalanceWarm s (BalanceAddress x) } ∧
        reason = .outOfGas) := by
  cases items : s.stack.val with
  | nil =>
    rw [extCodeHash_underflow s items]
    simp [eq_comm]
  | cons x xs =>
    let rest : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
    have items' : s.stack.val = x :: rest.val := items
    by_cases gas : BalanceCost s (BalanceAddress x) ≤ s.gas
    · let stack : Stack := ⟨ExtCodeHashValue s (BalanceAddress x) :: xs, by
        have bound := s.stack.property; rw [items] at bound; simp at bound; simp; omega⟩
      let target : State := { s with tracker := BalanceRead s (BalanceAddress x), warmAddresses := BalanceWarm s (BalanceAddress x), stack, pc := s.pc + 1, gas := s.gas - BalanceCost s (BalanceAddress x) }
      have fields : Advances { s with warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x) }
          target (s.pc + 1) (s.gas - BalanceCost s (BalanceAddress x))
          (ExtCodeHashValue s (BalanceAddress x) :: rest.val) := by simp [Advances, target, stack, rest]
      rw [extCodeHash_success s target rest x items' gas fields]
      simp only [reduceCtorEq, false_iff]
      rintro (⟨empty, _, _⟩ | ⟨r, y, equal, low, _, _⟩)
      · cases empty
      · have eq : x = y := (List.cons.inj equal).1
        rw [← eq] at low
        omega
    · rw [extCodeHash_gas s rest x items' (Nat.lt_of_not_ge gas)]
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

end EthLib.EVM.Frame
