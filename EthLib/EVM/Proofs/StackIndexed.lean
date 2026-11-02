module

public import EthLib.EVM.Stack
import Mathlib.Tactic

/-! Contracts for arbitrary zero-based stack positions. -/

@[expose] public section

namespace EthLib.EVM.Proofs.StackIndexed

open EthLib.EVM

/-- Duplication rejects a missing position before checking capacity. -/
theorem dup_underflow_iff (s : Stack) (i : Nat) :
    s.dupAt i = .error .underflow ↔ s.height ≤ i := by
  by_cases h : i < s.val.length
  · by_cases room : s.val.length < 1024 <;> simp [Stack.dupAt, Stack.height, h, room]
  · simp [Stack.dupAt, Stack.height, h]; omega

/-- Duplication overflows exactly when the entry exists and the stack is full. -/
theorem dup_overflow_iff (s : Stack) (i : Nat) :
    s.dupAt i = .error .overflow ↔ i < s.height ∧ s.height = 1024 := by
  have bound := s.property
  by_cases h : i < s.val.length
  · by_cases room : s.val.length < 1024 <;>
      simp [Stack.dupAt, Stack.height, h, room] <;> omega
  · simp [Stack.dupAt, Stack.height, h]

/-- Successful duplication copies exactly the requested entry. -/
theorem dup_ok_iff (s t : Stack) (i : Nat) :
    s.dupAt i = .ok t ↔
      ∃ h : i < s.height, s.height < 1024 ∧
        t.toList = s.toList[i]'h :: s.toList := by
  by_cases h : i < s.val.length
  · by_cases room : s.val.length < 1024
    · simp only [Stack.dupAt, h, room, dite_true, Except.ok.injEq,
        Stack.height, Stack.toList, true_and]
      constructor
      · intro e; exact ⟨trivial, congrArg Subtype.val e.symm⟩
      · rintro ⟨_, e⟩; exact Subtype.ext e.symm
    · simp [Stack.dupAt, Stack.height, h, room]
  · simp [Stack.dupAt, Stack.height, h]

/-- Exchange rejects exactly when at least one position is absent. -/
theorem exchange_underflow_iff (s : Stack) (i j : Nat) :
    s.exchangeAt i j = .error .underflow ↔ s.height ≤ i ∨ s.height ≤ j := by
  by_cases hi : i < s.val.length <;> by_cases hj : j < s.val.length <;>
    simp [Stack.exchangeAt, Stack.height, hi, hj] <;> omega

/-- Successful exchange changes exactly the two requested positions. -/
theorem exchange_ok_iff (s t : Stack) (i j : Nat) :
    s.exchangeAt i j = .ok t ↔
      ∃ (hi : i < s.height) (hj : j < s.height),
        t.toList = (s.toList.set i (s.toList[j]'hj)).set j (s.toList[i]'hi) := by
  by_cases hi : i < s.val.length
  · by_cases hj : j < s.val.length
    · simp only [Stack.exchangeAt, hi, hj, dite_true, Except.ok.injEq,
        Stack.height, Stack.toList]
      constructor
      · intro e; exact ⟨trivial, trivial, congrArg Subtype.val e.symm⟩
      · rintro ⟨_, _, e⟩; exact Subtype.ext e.symm
    · simp [Stack.exchangeAt, Stack.height, hi, hj]
  · simp [Stack.exchangeAt, Stack.height, hi]

/-- Exchange preserves the stack height. -/
theorem exchange_height (s t : Stack) (i j : Nat) (h : s.exchangeAt i j = .ok t) :
    t.height = s.height := by
  obtain ⟨_, _, eq⟩ := (exchange_ok_iff s t i j).mp h
  change t.toList.length = s.toList.length
  simp [eq]

/-- Duplication increases the stack height by one. -/
theorem dup_height (s t : Stack) (i : Nat) (h : s.dupAt i = .ok t) :
    t.height = s.height + 1 := by
  obtain ⟨_, _, eq⟩ := (dup_ok_iff s t i).mp h
  change t.toList.length = s.toList.length + 1
  simp [eq]

/-- Exchange never reports overflow. -/
theorem exchange_no_overflow (s : Stack) (i j : Nat) :
    s.exchangeAt i j ≠ .error .overflow := by
  by_cases hi : i < s.val.length <;> by_cases hj : j < s.val.length <;>
    simp [Stack.exchangeAt, hi, hj]

/-- Duplication succeeds exactly when its entry exists and capacity remains. -/
theorem dup_success_iff (s : Stack) (i : Nat) :
    (∃ t, s.dupAt i = .ok t) ↔ i < s.height ∧ s.height < 1024 := by
  by_cases h : i < s.val.length
  · by_cases room : s.val.length < 1024 <;> simp [Stack.dupAt, Stack.height, h, room]
  · simp [Stack.dupAt, Stack.height, h]

/-- Exchange succeeds exactly when both positions exist. -/
theorem exchange_success_iff (s : Stack) (i j : Nat) :
    (∃ t, s.exchangeAt i j = .ok t) ↔ i < s.height ∧ j < s.height := by
  by_cases hi : i < s.val.length <;> by_cases hj : j < s.val.length <;>
    simp [Stack.exchangeAt, Stack.height, hi, hj]

/-- Exchanging a position with itself leaves the stack unchanged. -/
theorem exchange_self (s : Stack) (i : Nat) (h : i < s.height) :
    s.exchangeAt i i = .ok s := by
  apply (exchange_ok_iff s s i i).mpr
  refine ⟨h, h, ?_⟩
  rw [List.set_set]
  exact (List.set_getElem_self h).symm

end EthLib.EVM.Proofs.StackIndexed
