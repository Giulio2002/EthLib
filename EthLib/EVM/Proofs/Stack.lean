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

/-- DUP underflows exactly when the requested entry is absent. -/
theorem dup_underflow_iff (s : Stack) (i : Fin 16) :
    s.dup i = .error .underflow ↔ s.height ≤ i.val := by
  by_cases h : i.val < s.val.length
  · by_cases room : s.val.length < 1024 <;> simp [Stack.dup, Stack.height, h, room] <;> omega
  · simp [Stack.dup, Stack.height, h]; omega

/-- DUP overflows exactly when the stack is full. -/
theorem dup_overflow_iff (s : Stack) (i : Fin 16) :
    s.dup i = .error .overflow ↔ s.height = 1024 := by
  have bound := s.property
  have ib := i.isLt
  by_cases h : i.val < s.val.length
  · by_cases room : s.val.length < 1024 <;>
      simp [Stack.dup, Stack.height, h, room] <;> omega
  · simp [Stack.dup, Stack.height, h]
    omega

/-- A successful DUP copies the indexed entry and leaves the old list in order. -/
theorem dup_ok_iff (s t : Stack) (i : Fin 16) :
    s.dup i = .ok t ↔
      ∃ h : i.val < s.height, s.height < 1024 ∧
        t.toList = s.toList[i.val]'h :: s.toList := by
  by_cases h : i.val < s.val.length
  · by_cases room : s.val.length < 1024
    · simp only [Stack.dup, h, room, dite_true, Except.ok.injEq,
        Stack.height, Stack.toList, true_and]
      constructor
      · intro e; exact ⟨trivial, congrArg Subtype.val e.symm⟩
      · rintro ⟨_, e⟩; exact Subtype.ext e.symm
    · simp [Stack.dup, Stack.height, h, room]
  · simp [Stack.dup, Stack.height, h]

/-- SWAP underflows exactly when the requested entry is absent. -/
theorem swap_underflow_iff (s : Stack) (i : Fin 16) :
    s.swap i = .error .underflow ↔ s.height ≤ i.val + 1 := by
  by_cases h : i.val + 1 < s.val.length <;>
    simp [Stack.swap, Stack.height, h] <;> omega

/-- A successful SWAP exchanges exactly the two specified entries. -/
theorem swap_ok_iff (s t : Stack) (i : Fin 16) :
    s.swap i = .ok t ↔
      ∃ h : i.val + 1 < s.height,
        t.toList = (s.toList.set 0 ((s.toList)[i.val + 1]'h)).set
          (i.val + 1) ((s.toList)[0]'(by change 0 < s.height; omega)) := by
  by_cases h : i.val + 1 < s.val.length
  · simp only [Stack.swap, h, dite_true, Except.ok.injEq, Stack.height, Stack.toList]
    constructor
    · intro e; exact ⟨trivial, congrArg Subtype.val e.symm⟩
    · rintro ⟨_, e⟩; exact Subtype.ext e.symm
  · simp [Stack.swap, Stack.height, h]

/-- SWAP preserves the height. -/
theorem swap_height (s t : Stack) (i : Fin 16) (h : s.swap i = .ok t) :
    t.height = s.height := by
  obtain ⟨_, eq⟩ := (swap_ok_iff s t i).mp h
  change t.toList.length = s.toList.length
  simp [eq]

/-- DUP increases the height by one. -/
theorem dup_height (s t : Stack) (i : Fin 16) (h : s.dup i = .ok t) :
    t.height = s.height + 1 := by
  obtain ⟨_, _, eq⟩ := (dup_ok_iff s t i).mp h
  change t.toList.length = s.toList.length + 1
  simp [eq]

/-- DUP succeeds exactly when the entry exists and there is room. -/
theorem dup_success_iff (s : Stack) (i : Fin 16) :
    (∃ t, s.dup i = .ok t) ↔ i.val < s.height ∧ s.height < 1024 := by
  by_cases h : i.val < s.val.length
  · by_cases room : s.val.length < 1024 <;> simp [Stack.dup, Stack.height, h, room]
  · simp [Stack.dup, Stack.height, h]

/-- SWAP succeeds exactly when both entries exist. -/
theorem swap_success_iff (s : Stack) (i : Fin 16) :
    (∃ t, s.swap i = .ok t) ↔ i.val + 1 < s.height := by
  by_cases h : i.val + 1 < s.val.length <;> simp [Stack.swap, Stack.height, h]

/-- SWAP never overflows. -/
theorem swap_no_overflow (s : Stack) (i : Fin 16) :
    s.swap i ≠ .error .overflow := by
  by_cases h : i.val + 1 < s.val.length <;> simp [Stack.swap, h]

/-- Entries outside the two exchanged positions are unchanged. -/
theorem swap_unaffected (s t : Stack) (i : Fin 16) (h : s.swap i = .ok t)
    (j : Nat) (hj : j < s.height) (h0 : j ≠ 0) (hi : j ≠ i.val + 1) :
    t.toList[j]'(by have := swap_height s t i h; change j < t.height; omega) = s.toList[j]'hj := by
  obtain ⟨_, eq⟩ := (swap_ok_iff s t i).mp h
  simp only [eq, List.getElem_set, ite_eq_right (Ne.symm hi), ite_eq_right (Ne.symm h0)]
  rfl
/-- Repeating a successful SWAP restores the stack. -/
theorem swap_involution (s t : Stack) (i : Fin 16) (h : s.swap i = .ok t) : t.swap i = .ok s := by
  obtain ⟨idx, eq⟩ := (swap_ok_iff s t i).mp h
  apply (swap_ok_iff t s i).mpr
  have ht : t.height = s.height := swap_height s t i h
  have valid : i.val + 1 < t.height := by omega
  refine ⟨valid, ?_⟩
  apply List.ext_getElem
  · simp [eq]
  · intro j hj hj'
    simp only [eq, List.getElem_set]
    by_cases h0 : j = 0
    · subst j; simp <;> rfl
    · by_cases hi : j = i.val + 1
      · subst j; simp <;> rfl
      · simp [Ne.symm h0, Ne.symm hi]

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

/-- Model Cancun `dup_n` on a bottom-first source list. -/
def dup (p : List Word) (i : Fin 16) : Except StackError (List Word) :=
  if h : i.val < p.length then
    if p.length = 1024 then .error .overflow
    else .ok (p ++ [p[p.length - 1 - i.val]'(by omega)])
  else .error .underflow

/-- Model Cancun `swap_n` on a bottom-first source list. -/
def swap (p : List Word) (i : Fin 16) : Except StackError (List Word) :=
  if h : i.val + 1 < p.length then
    .ok ((p.set (p.length - 1) (p[p.length - 2 - i.val]'(by omega))).set
      (p.length - 2 - i.val) (p[p.length - 1]'(by omega)))
  else .error .underflow


end Reference

/-- The source list stores the top at its end. -/
def Related (s : Stack) (p : List Word) : Prop := p = s.toList.reverse

/-- Reversing a list moves an updated position to its reflected index. -/
private theorem reverse_set_index {α : Type} (xs : List α) (k : Nat) (x : α) (hk : k < xs.length) :
    (xs.set k x).reverse = xs.reverse.set (xs.length - 1 - k) x := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp only [List.length_reverse, List.length_set] at hj hj'
    simp only [List.getElem_reverse, List.getElem_set, List.length_set]
    have key : (k = xs.length - 1 - j) ↔ (xs.length - 1 - k = j) := by omega
    simp only [key]

/-- SWAP agrees with the source order and source underflow. -/
theorem swap_refines (s : Stack) (i : Fin 16) :
    (s.swap i).map (fun t => t.toList.reverse) = Reference.swap s.toList.reverse i := by
  by_cases h : i.val + 1 < s.val.length
  · let t : Stack := ⟨(s.val.set 0 (s.val[i.val + 1])).set (i.val + 1) (s.val[0]'(by omega)), by simpa using s.property⟩
    have ht : s.swap i = .ok t := by simp [Stack.swap, h, t]
    simp only [ht, Except.map, Reference.swap, Stack.toList, List.length_reverse, h, dite_true, t]
    rw [reverse_set_index, reverse_set_index] <;> try (simp only [List.length_set] at *; omega) <;> try omega
    simp only [List.length_set]
    have htop : s.val.reverse[s.val.length - 1]'(by simp; omega) = s.val[0]'(by omega) := by
      rw [List.getElem_reverse]
      congr 1 <;> omega
    have hother : s.val.reverse[s.val.length - 2 - i.val]'(by simp; omega) = s.val[i.val + 1]'h := by
      rw [List.getElem_reverse]
      congr 1 <;> omega
    simp only [htop, hother]
    all_goals (try (congr 2)) <;> omega
  · simp [Stack.swap, Reference.swap, Stack.toList, h, Except.map]

/-- DUP agrees with the source order and both source errors. -/
theorem dup_refines (s : Stack) (i : Fin 16) :
    (s.dup i).map (fun t => t.toList.reverse) = Reference.dup s.toList.reverse i := by
  have bound := s.property
  have ib := i.isLt
  by_cases h : i.val < s.val.length
  · by_cases room : s.val.length < 1024
    · have eq : s.toList.reverse[s.height - 1 - i.val]'(by simp [Stack.height, Stack.toList] at *; omega) = s.toList[i.val]'h := by
        change i.val < s.val.length at h
        rw [List.getElem_reverse]
        simp only [Stack.height, Stack.toList]
        congr 1 <;> omega
      simp only [Stack.height, Stack.toList, List.getElem_reverse] at eq
      simp [Stack.dup, Reference.dup, h, room, Nat.ne_of_lt room, Stack.toList, Except.map, eq]
    · have full : s.val.length = 1024 := by omega
      have ih : i.val < 1024 := by omega
      simp [Stack.dup, Reference.dup, Stack.toList, full, ih, Except.map]
  · simp [Stack.dup, Reference.dup, h, Stack.toList, Except.map]

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
