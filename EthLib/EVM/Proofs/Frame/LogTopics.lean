module

public import EthLib.EVM.Frame
public import EthLib.EVM.Proofs.Stack
import Mathlib.Tactic

@[expose] public section
namespace EthLib.EVM.Frame

/-- Sufficient stack entries yield precisely the requested topics in pop order. -/
theorem popLogTopics_ok (topics : List Word) (stack tail : Stack)
    (entries : stack.val = topics ++ tail.val) :
    popLogTopics topics.length stack = .ok (topics, tail) := by
  induction topics generalizing stack with
  | nil =>
    have eq : stack = tail := Subtype.ext (by simpa using entries)
    subst stack
    rfl
  | cons topic topics ih =>
    let rest : Stack := ⟨topics ++ tail.val, by have h := stack.property; rw [entries] at h; simp only [List.cons_append, List.length_cons] at h; omega⟩
    have p : stack.pop = .ok (topic, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr entries
    have next := ih rest rfl
    simp [popLogTopics, p, next]

/-- An insufficient stack is exhausted before the topic-pop error. -/
theorem popLogTopics_underflow (count : Nat) (stack : Stack)
    (short : stack.val.length < count) : popLogTopics count stack = .error Stack.empty := by
  induction count generalizing stack with
  | zero => simp at short
  | succ count ih =>
    cases entries : stack.val with
    | nil =>
      have eq : stack = Stack.empty := Subtype.ext (by simpa [Stack.empty] using entries)
      subst stack
      rfl
    | cons topic topics =>
      let rest : Stack := ⟨topics, by have h := stack.property; rw [entries] at h; simp at h; omega⟩
      have p : stack.pop = .ok (topic, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr entries
      have bound : rest.val.length < count := by simp [rest, entries] at short ⊢; omega
      simp [popLogTopics, p, ih rest bound]

end EthLib.EVM.Frame
