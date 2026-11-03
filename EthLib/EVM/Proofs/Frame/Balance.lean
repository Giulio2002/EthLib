module

public import EthLib.EVM.Proofs.Frame.SelfBalance
import Aesop

/-!
# BALANCE

Amsterdam `vm/instructions/environment.py`, `balance`, pops the operand,
warms a cold address before charging, then records the account read.
-/

@[expose] public section
namespace EthLib.EVM.Frame

/-- An empty stack fails before warming or charging. -/
theorem balance_underflow (s : State) (empty : s.stack.val = []) :
    balance s = .exception s .stackUnderflow := by
  have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr empty
  simp [balance, pop, failStack]

/-- A failed charge preserves the popped stack and the warmed address. -/
theorem balance_gas (s : State) (rest : Stack) (x : Word)
    (items : s.stack.val = x :: rest.val) (gas : s.gas < BalanceCost s (BalanceAddress x)) :
    balance s = .exception { s with stack := rest, warmAddresses := BalanceWarm s (BalanceAddress x) } .outOfGas := by
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have address : balanceAddress x = BalanceAddress x := rfl
  have cost : (if s.warmAddresses.contains (BalanceAddress x) then 100 else 3000) = BalanceCost s (BalanceAddress x) := by simp [BalanceCost]
  have warms : (if s.warmAddresses.contains (BalanceAddress x) then s.warmAddresses else BalanceAddress x :: s.warmAddresses) = BalanceWarm s (BalanceAddress x) := by simp [BalanceWarm]
  simp only [balance, pop, address, cost, warms, charge, Gas.charge,
    ite_eq_right (Nat.not_le_of_gt gas)]

/-- A charged read fixes the full resulting frame. -/
theorem balance_success (s t : State) (rest : Stack) (x : Word)
    (items : s.stack.val = x :: rest.val) (gas : BalanceCost s (BalanceAddress x) ≤ s.gas)
    (fields : Advances { s with warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x) }
      t (s.pc + 1) (s.gas - BalanceCost s (BalanceAddress x))
      ((BalanceAccount s (BalanceAddress x)).balance :: rest.val)) :
    balance s = .continue t := by
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have room : rest.val.length < 1024 := by have bound := s.stack.property; rw [items] at bound; simp at bound; omega
  let stack : Stack := ⟨(BalanceAccount s (BalanceAddress x)).balance :: rest.val, by simp; omega⟩
  have push : rest.push (BalanceAccount s (BalanceAddress x)).balance = .ok stack :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨room, rfl⟩
  have eq := advances_eq { s with warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x) } t
    (s.pc + 1) (s.gas - BalanceCost s (BalanceAddress x)) stack fields
  subst t
  have value : (TransactionTracker.getAccount s.tracker (BalanceAddress x)).1 = BalanceAccount s (BalanceAddress x) := rfl
  have read : (TransactionTracker.getAccount s.tracker (BalanceAddress x)).2 = BalanceRead s (BalanceAddress x) := rfl
  have address : balanceAddress x = BalanceAddress x := rfl
  have cost : (if s.warmAddresses.contains (BalanceAddress x) then 100 else 3000) = BalanceCost s (BalanceAddress x) := by simp [BalanceCost]
  have warms : (if s.warmAddresses.contains (BalanceAddress x) then s.warmAddresses else BalanceAddress x :: s.warmAddresses) = BalanceWarm s (BalanceAddress x) := by simp [BalanceWarm]
  simp only [balance, pop, address, cost, warms, charge, Gas.charge, ite_eq_left gas, value, read, push]

/-- Success is equivalent to a popped operand, affordable gas and all output fields. -/
theorem balance_success_iff (s t : State) :
    balance s = .continue t ↔ ∃ (rest : Stack) (x : Word),
      s.stack.val = x :: rest.val ∧ BalanceCost s (BalanceAddress x) ≤ s.gas ∧
      Advances { s with warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x) }
        t (s.pc + 1) (s.gas - BalanceCost s (BalanceAddress x))
        ((BalanceAccount s (BalanceAddress x)).balance :: rest.val) := by
  constructor
  · intro run
    cases items : s.stack.val with
    | nil =>
      have bad := balance_underflow s items
      rw [run] at bad
      cases bad
    | cons x xs =>
      let rest : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
      have items' : s.stack.val = x :: rest.val := items
      by_cases gas : BalanceCost s (BalanceAddress x) ≤ s.gas
      · let stack : Stack := ⟨(BalanceAccount s (BalanceAddress x)).balance :: xs, by
          have bound := s.stack.property; rw [items] at bound; simp at bound; simp; omega⟩
        let target : State := { s with tracker := BalanceRead s (BalanceAddress x), warmAddresses := BalanceWarm s (BalanceAddress x), stack, pc := s.pc + 1, gas := s.gas - BalanceCost s (BalanceAddress x) }
        have fields : Advances { s with warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x) }
            target (s.pc + 1) (s.gas - BalanceCost s (BalanceAddress x))
            ((BalanceAccount s (BalanceAddress x)).balance :: rest.val) := by
          simp [Advances, target, stack, rest]
        have eq := balance_success s target rest x items' gas fields
        rw [run] at eq
        have eqTarget : t = target := Outcome.continue.inj eq
        subst t
        exact ⟨rest, x, rfl, gas, fields⟩
      · have bad := balance_gas s rest x items' (Nat.lt_of_not_ge gas)
        rw [run] at bad
        cases bad
  · rintro ⟨rest, x, items, gas, fields⟩
    exact balance_success s t rest x items gas fields

/-- All failures are either underflow or a charge failure after warming. -/
theorem balance_exception_iff (s input : State) (reason : Exception) :
    balance s = .exception input reason ↔
      (s.stack.val = [] ∧ input = s ∧ reason = .stackUnderflow) ∨
      (∃ (rest : Stack) (x : Word), s.stack.val = x :: rest.val ∧
        s.gas < BalanceCost s (BalanceAddress x) ∧
        input = { s with stack := rest, warmAddresses := BalanceWarm s (BalanceAddress x) } ∧
        reason = .outOfGas) := by
  cases items : s.stack.val with
  | nil =>
    rw [balance_underflow s items]
    simp [eq_comm]
  | cons x xs =>
    let rest : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
    have items' : s.stack.val = x :: rest.val := items
    by_cases gas : BalanceCost s (BalanceAddress x) ≤ s.gas
    · let stack : Stack := ⟨(BalanceAccount s (BalanceAddress x)).balance :: xs, by
        have bound := s.stack.property; rw [items] at bound; simp at bound; simp; omega⟩
      let target : State := { s with tracker := BalanceRead s (BalanceAddress x), warmAddresses := BalanceWarm s (BalanceAddress x), stack, pc := s.pc + 1, gas := s.gas - BalanceCost s (BalanceAddress x) }
      have fields : Advances { s with warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x) }
          target (s.pc + 1) (s.gas - BalanceCost s (BalanceAddress x))
          ((BalanceAccount s (BalanceAddress x)).balance :: rest.val) := by simp [Advances, target, stack, rest]
      rw [balance_success s target rest x items' gas fields]
      simp only [reduceCtorEq, false_iff]
      rintro (⟨empty, _, _⟩ | ⟨r, y, equal, low, _, _⟩)
      · cases empty
      · have eq : x = y := (List.cons.inj equal).1
        rw [← eq] at low
        omega
    · rw [balance_gas s rest x items' (Nat.lt_of_not_ge gas)]
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

/-- The warm-set transition adds exactly the selected address. -/
theorem balance_warm_membership (s : State) (a b : World.Address) :
    b ∈ BalanceWarm s a ↔ b = a ∨ b ∈ s.warmAddresses := by
  by_cases warm : a ∈ s.warmAddresses
  · simp [BalanceWarm, warm]; intro eq; subst b; exact warm
  · simp [BalanceWarm, warm]

/-- The source gas classifications use the initial warm set. -/
theorem balance_cost_cases (s : State) (a : World.Address) :
    (a ∈ s.warmAddresses → BalanceCost s a = 100) ∧
    (a ∉ s.warmAddresses → BalanceCost s a = 3000) := by
  simp [BalanceCost]

/-- Instructions other than BALANCE preserve the entire warm list. -/
theorem outcome_warm_unchanged_of_not_balance {s : State} {out : Outcome}
    (notBalance : ¬ At s (some .balance)) (rule : Rule s out) :
    out.frame.warmAddresses = s.warmAddresses := by
  cases rule <;> simp_all [Outcome.frame, Advances, AdvancesMemory, SstoreReady, SstoreReadFields,
    SstoreCreditFields, SstoreExecutionFields, SstoreChargeFields, SstoreMeterRetained, SstoreWriteFields] <;> aesop

/-- Every rule retains all addresses that were already warm. -/
theorem outcome_warm_monotone {s : State} {out : Outcome} (rule : Rule s out)
    (a : World.Address) (warm : a ∈ s.warmAddresses) : a ∈ out.frame.warmAddresses := by
  cases rule <;> simp_all [Outcome.frame, Advances, AdvancesMemory, BalanceWarm, SstoreReady, SstoreReadFields,
    SstoreCreditFields, SstoreExecutionFields, SstoreChargeFields, SstoreMeterRetained, SstoreWriteFields] <;>
    (try split) <;> (try simp_all) <;> aesop

/-- The account selection refines the independent tracker maps. -/
theorem balance_account_value (s : State) (a : World.Address) :
    (∀ x, (TransactionState.Reference.observe s.tracker).writes.accounts a = some x →
      BalanceAccount s a = x.getD World.emptyAccount) ∧
    ((TransactionState.Reference.observe s.tracker).writes.accounts a = none →
      BalanceAccount s a = ((TransactionState.Reference.observe s.tracker).parentAccounts a).getD World.emptyAccount) :=
  TransactionTracker.getAccount_value s.tracker a

/-- Opcode 0x31 invokes the same helper at the current boundary. -/
theorem step_balance (s : State) (at_ : At s (some .balance)) : step s = balance s := by
  obtain ⟨bounds, decoded⟩ := at_
  simp only [step, dite_eq_left bounds, decoded]

end EthLib.EVM.Frame
