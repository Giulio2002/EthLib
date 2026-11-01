module

public import EthLib.EVM.Stack

@[expose] public section

namespace EthLib.EVM.Proofs.Stack

open EthLib.EVM

/-- Every stack satisfies the protocol limit. -/
theorem height_bound (s : Stack) : s.height ≤ 1024 := s.property

/-- Ordered contents determine the stack independently of proof terms. -/
theorem ext (s t : Stack) : s.toList = t.toList → s = t := Subtype.ext

/-- Successful construction preserves exactly the input list. -/
theorem ofList_ok_iff (xs : List Word) (s : Stack) :
    Stack.ofList xs = .ok s ↔ xs.length ≤ 1024 ∧ s.toList = xs := by
  by_cases h : xs.length ≤ 1024
  · rw [Stack.ofList, dite_eq_left h]
    simp only [Except.ok.injEq, h, true_and]
    constructor
    · intro e; cases e; rfl
    · intro e; apply Subtype.ext; exact e.symm
  · simp [Stack.ofList, h]

/-- Construction succeeds exactly for lists within the limit. -/
theorem ofList_success_iff (xs : List Word) :
    (∃ s, Stack.ofList xs = .ok s) ↔ xs.length ≤ 1024 := by
  constructor
  · rintro ⟨s, h⟩; exact ((ofList_ok_iff xs s).mp h).1
  · intro h; exact ⟨⟨xs, h⟩, (ofList_ok_iff _ _).mpr ⟨h, rfl⟩⟩

/-- Oversized input produces the boundary error. -/
theorem ofList_error_iff (xs : List Word) :
    Stack.ofList xs = .error .tooManyEntries ↔ 1024 < xs.length := by
  by_cases h : xs.length ≤ 1024
  · simp [Stack.ofList, h, Nat.not_lt_of_ge h]
  · have h' : 1024 < xs.length := Nat.lt_of_not_ge h
    simp [Stack.ofList, h, h']

/-- Push overflows exactly at the limit. -/
theorem push_overflow_iff (s : Stack) (x : Word) :
    s.push x = .error .overflow ↔ s.height = 1024 := by
  have bound := s.property
  by_cases h : s.val.length < 1024 <;> simp [Stack.push, Stack.height, h] <;> omega

/-- Successful push adds exactly one top entry. -/
theorem push_ok_iff (s t : Stack) (x : Word) :
    s.push x = .ok t ↔ s.height < 1024 ∧ t.toList = x :: s.toList := by
  by_cases h : s.val.length < 1024
  · rw [Stack.push, dite_eq_left h]
    simp only [Except.ok.injEq, Stack.height, h, true_and]
    constructor
    · intro e; cases e; rfl
    · intro e; apply Subtype.ext; exact e.symm
  · simp [Stack.push, Stack.height, h]

/-- Pop underflows exactly on the empty stack. -/
theorem pop_underflow_iff (s : Stack) :
    s.pop = .error .underflow ↔ s.toList = [] := by
  cases s with
  | mk xs bound => cases xs <;> simp [Stack.pop, Stack.toList]

/-- Successful pop removes exactly the top entry. -/
theorem pop_ok_iff (s t : Stack) (x : Word) :
    s.pop = .ok (x, t) ↔ s.toList = x :: t.toList := by
  cases s with
  | mk xs bound =>
    cases xs with
    | nil => simp [Stack.pop, Stack.toList]
    | cons y ys =>
      simp only [Stack.pop, Except.ok.injEq, Prod.mk.injEq, Stack.toList, List.cons.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, h⟩; exact ⟨rfl, Subtype.ext h⟩

/-- A successful push is undone by pop. -/
theorem pop_push (s t : Stack) (x : Word) (h : s.push x = .ok t) :
    t.pop = .ok (x, s) := (pop_ok_iff t s x).mpr ((push_ok_iff s t x).mp h).2

/-- A successful pop is undone by push. -/
theorem push_pop (s t : Stack) (x : Word) (h : s.pop = .ok (x, t)) :
    t.push x = .ok s := by
  have eq := (pop_ok_iff s t x).mp h
  apply (push_ok_iff t s x).mpr
  constructor
  -- Removing a head leaves room to restore it.
  · have bound := s.property
    change s.toList.length ≤ 1024 at bound
    rw [eq] at bound
    simp only [List.length_cons] at bound
    change t.toList.length < 1024
    omega
  · exact eq

/-- Push increases the height by one. -/
theorem push_height (s t : Stack) (x : Word) (h : s.push x = .ok t) :
    t.height = s.height + 1 := by
  have eq := (push_ok_iff s t x).mp h |>.2
  change t.toList.length = s.toList.length + 1
  simp [eq]

/-- Pop decreases the height by one. -/
theorem pop_height (s t : Stack) (x : Word) (h : s.pop = .ok (x, t)) :
    s.height = t.height + 1 := by
  have eq := (pop_ok_iff s t x).mp h
  change s.toList.length = t.toList.length + 1
  simp [eq]

/-! The reference list has the source's bottom-first order.

These pure results model the inspected Python helper rules.
They do not execute Python or its exceptions.
-/
namespace Reference

/-- Model Cancun `vm/stack.py`, `push` on a well-formed source list. -/
def push (p : List Word) (x : Word) : Except StackError (List Word) :=
  if p.length = 1024 then .error .overflow else .ok (p ++ [x])

/-- Model Cancun `vm/stack.py`, `pop` by removing the last entry. -/
def pop (p : List Word) : Except StackError (Word × List Word) :=
  match p.reverse with
  | [] => .error .underflow
  | x :: xs => .ok (x, xs.reverse)

end Reference

/-- The source list stores the top at its end. -/
def Related (s : Stack) (p : List Word) : Prop := p = s.toList.reverse

/-- Push agrees with append and preserves both success and overflow. -/
theorem push_refines (s : Stack) (p : List Word) (x : Word) (h : Related s p) :
    (s.push x).map (fun t => t.toList.reverse) = Reference.push p x := by
  subst p
  have bound := s.property
  -- The invariant makes every non-full stack strictly smaller than the limit.
  by_cases full : s.val.length = 1024
  · have fail := (push_overflow_iff s x).mpr full
    simp [fail, Reference.push, Stack.toList, full, Except.map]
  · have room : s.height < 1024 := by
      change s.val.length < 1024
      omega
    let t : Stack := ⟨x :: s.val, by simp only [List.length_cons]; omega⟩
    have ok : s.push x = .ok t := (push_ok_iff s t x).mpr ⟨room, rfl⟩
    simp [ok, Reference.push, Stack.toList, full, t, Except.map]

/-- Pop agrees with removal of the last entry, including underflow. -/
theorem pop_refines (s : Stack) (p : List Word) (h : Related s p) :
    (s.pop).map (fun q => (q.1, q.2.toList.reverse)) = Reference.pop p := by
  subst p
  cases s with
  | mk xs bound =>
    cases xs <;> simp [Stack.pop, Stack.toList, Reference.pop, Except.map]

/-- Empty pop is rejected. -/
theorem empty_pop : Stack.empty.pop = .error .underflow := by
  rfl

/-- A single pushed value can be popped with the original stack. -/
theorem one_item :
    Stack.empty.push 1 = .ok (⟨[1], by decide⟩ : Stack) ∧
    Stack.pop (⟨[1], by decide⟩ : Stack) = .ok (1, Stack.empty) := by
  constructor <;> rfl

/-- Distinct values remain in top-first order. -/
theorem order_example :
    Stack.pop (⟨[2, 1], by decide⟩ : Stack) = .ok (2, ⟨[1], by decide⟩) := by rfl

/-- A push at height 1023 reaches the limit. -/
theorem push_boundary :
    Stack.push (⟨List.replicate 1023 (0 : Word), by simp only [List.length_replicate]; omega⟩ : Stack) 1 =
      .ok ⟨1 :: List.replicate 1023 0, by simp only [List.length_cons, List.length_replicate]; omega⟩ := by
  apply (push_ok_iff _ _ _).mpr
  simp only [Stack.height, Stack.toList, List.length_replicate]; decide

/-- A push at height 1024 fails. -/
theorem overflow_boundary :
    Stack.push (⟨List.replicate 1024 (0 : Word), by simp only [List.length_replicate]; omega⟩ : Stack) 1 =
      .error .overflow := by
  apply (push_overflow_iff _ _).mpr
  simp only [Stack.height, List.length_replicate]

/-- A list of 1025 entries is rejected at the boundary. -/
theorem input_boundary :
    Stack.ofList (List.replicate 1025 (0 : Word)) = .error .tooManyEntries := by
  apply (ofList_error_iff _).mpr
  simp only [List.length_replicate]; omega

end EthLib.EVM.Proofs.Stack
