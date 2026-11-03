module

public import EthLib.EVM.Proofs.Frame.Sload
public import EthLib.EVM.Proofs.TransactionTracker

/-! Source-order facts for Amsterdam `storage.py`, `tload` and `tstore`. -/

@[expose] public section
namespace EthLib.EVM.Frame

/-- TLOAD checks its first operand before charging. -/
theorem tload_underflow (s : State) (empty : s.stack.val = []) :
    tload s = .exception s .stackUnderflow := by
  have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr empty
  simp [tload, pop, failStack]

/-- A failed TLOAD charge keeps the popped stack. -/
theorem tload_gas (s : State) (rest : Stack) (key : Word)
    (items : s.stack.val = key :: rest.val) (gas : s.gas < 100) :
    tload s = .exception { s with stack := rest } .outOfGas := by
  have pop : s.stack.pop = .ok (key, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  simp only [tload, pop, charge, Gas.charge, ite_eq_right (Nat.not_le_of_gt gas)]

/-- TSTORE rejects static execution before touching the stack. -/
theorem tstore_static (s : State) (static : s.isStatic = true) :
    tstore s = .exception s .writeInStaticContext := by
  simp [tstore, static]

/-- TSTORE checks its first operand before charging. -/
theorem tstore_underflow (s : State) (static : s.isStatic = false)
    (empty : s.stack.val = []) : tstore s = .exception s .stackUnderflow := by
  have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr empty
  simp [tstore, static, pop, failStack]

/-- TSTORE retains its first pop if its second operand is absent. -/
theorem tstore_second_underflow (s : State) (rest : Stack) (key : Word)
    (static : s.isStatic = false) (items : s.stack.val = key :: rest.val)
    (empty : rest.val = []) :
    tstore s = .exception { s with stack := rest } .stackUnderflow := by
  have pop : s.stack.pop = .ok (key, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have pop' : rest.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr empty
  simp [tstore, static, pop, pop', failStack]

/-- A failed TSTORE charge keeps both pops and leaves the tracker untouched. -/
theorem tstore_gas (s : State) (first rest : Stack) (key value : Word)
    (static : s.isStatic = false) (items : s.stack.val = key :: first.val)
    (items' : first.val = value :: rest.val) (gas : s.gas < 100) :
    tstore s = .exception { s with stack := rest } .outOfGas := by
  have pop : s.stack.pop = .ok (key, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have pop' : first.pop = .ok (value, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items'
  simp only [tstore, static, Bool.false_eq_true, ↓reduceIte, pop, pop', charge, Gas.charge,
    ite_eq_right (Nat.not_le_of_gt gas)]

/-- TLOAD selects the first matching transient entry, defaulting to zero. -/
def TransientValue (s : State) (key : Word) : Word :=
  (s.tracker.writes.transientStorage.lookup (s.context.environment.currentTarget, key)).getD 0

/-- An affordable TLOAD has the stated value and preserves all other fields. -/
theorem tload_success (s t : State) (rest : Stack) (key : Word)
    (items : s.stack.val = key :: rest.val) (gas : 100 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 100) (TransientValue s key :: rest.val)) :
    tload s = .continue t := by
  have pop : s.stack.pop = .ok (key, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have room : rest.val.length < 1024 := by
    have bound := s.stack.property
    rw [items] at bound
    simp at bound
    omega
  let stack : Stack := ⟨TransientValue s key :: rest.val, by simp; omega⟩
  have push : rest.push (TransientValue s key) = .ok stack :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨room, rfl⟩
  have eq := advances_eq s t (s.pc + 1) (s.gas - 100) stack fields
  subst t
  have value : TransactionTracker.getTransientStorage s.tracker s.context.environment.currentTarget key =
      TransientValue s key := rfl
  simp only [tload, pop, charge, Gas.charge, ite_eq_left gas, value, push]

/-- An affordable TSTORE writes after both pops and advances the counter. -/
theorem tstore_success (s : State) (first rest : Stack) (key value : Word)
    (static : s.isStatic = false) (items : s.stack.val = key :: first.val)
    (items' : first.val = value :: rest.val) (gas : 100 ≤ s.gas) :
    tstore s = .continue { s with stack := rest, gas := s.gas - 100, pc := s.pc + 1, tracker := TransactionTracker.setTransientStorage s.tracker s.context.environment.currentTarget key value } := by
  have pop : s.stack.pop = .ok (key, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have pop' : first.pop = .ok (value, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items'
  simp only [tstore, static, Bool.false_eq_true, ↓reduceIte, pop, pop', charge, Gas.charge,
    ite_eq_left gas]

/-- TLOAD success determines its operand, gas check, value and complete frame. -/
theorem tload_success_iff (s t : State) :
    tload s = .continue t ↔ ∃ (rest : Stack) (key : Word),
      s.stack.val = key :: rest.val ∧ 100 ≤ s.gas ∧
      Advances s t (s.pc + 1) (s.gas - 100) (TransientValue s key :: rest.val) := by
  constructor
  · intro run
    cases items : s.stack.val with
    | nil =>
      have bad := tload_underflow s items
      rw [run] at bad
      cases bad
    | cons key xs =>
      let rest : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
      have items' : s.stack.val = key :: rest.val := items
      by_cases gas : 100 ≤ s.gas
      · let stack : Stack := ⟨TransientValue s key :: xs, by
          have bound := s.stack.property; rw [items] at bound; simp at bound; simp; omega⟩
        let target : State := { s with stack, pc := s.pc + 1, gas := s.gas - 100 }
        have fields : Advances s target (s.pc + 1) (s.gas - 100)
            (TransientValue s key :: rest.val) := by simp [Advances, target, stack, rest]
        have eq := tload_success s target rest key items' gas fields
        rw [run] at eq
        have eqTarget : t = target := Outcome.continue.inj eq
        subst t
        exact ⟨rest, key, rfl, gas, fields⟩
      · have bad := tload_gas s rest key items' (Nat.lt_of_not_ge gas)
        rw [run] at bad
        cases bad
  · rintro ⟨rest, key, items, gas, fields⟩
    exact tload_success s t rest key items gas fields

/-- TLOAD failures are exactly first-pop underflow or a failed charge. -/
theorem tload_exception_iff (s input : State) (reason : Exception) :
    tload s = .exception input reason ↔
      (s.stack.val = [] ∧ input = s ∧ reason = .stackUnderflow) ∨
      (∃ (rest : Stack) (key : Word), s.stack.val = key :: rest.val ∧
        s.gas < 100 ∧ input = { s with stack := rest } ∧ reason = .outOfGas) := by
  cases items : s.stack.val with
  | nil =>
    rw [tload_underflow s items]
    simp [eq_comm]
  | cons key xs =>
    let rest : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
    have items' : s.stack.val = key :: rest.val := items
    by_cases gas : 100 ≤ s.gas
    · let stack : Stack := ⟨TransientValue s key :: xs, by
        have bound := s.stack.property; rw [items] at bound; simp at bound; simp; omega⟩
      let target : State := { s with stack, pc := s.pc + 1, gas := s.gas - 100 }
      have fields : Advances s target (s.pc + 1) (s.gas - 100)
          (TransientValue s key :: rest.val) := by simp [Advances, target, stack, rest]
      rw [tload_success s target rest key items' gas fields]
      simp only [reduceCtorEq, false_iff]
      rintro (⟨empty, _, _⟩ | ⟨r, y, equal, low, _, _⟩)
      · cases empty
      · omega
    · rw [tload_gas s rest key items' (Nat.lt_of_not_ge gas)]
      constructor
      · intro eq
        cases eq
        exact Or.inr ⟨rest, key, rfl, Nat.lt_of_not_ge gas, rfl, rfl⟩
      · rintro (⟨empty, _, _⟩ | ⟨r, y, equal, _, eqInput, eqReason⟩)
        · cases empty
        · have both : key = y ∧ rest.val = r.val := by simpa [items, rest] using equal
          have restEq : rest = r := Subtype.ext both.2
          cases restEq
          subst input
          subst reason
          rfl

/-- A successful TSTORE requires dynamic execution, two operands and 100 gas. -/
theorem tstore_success_iff (s t : State) :
    tstore s = .continue t ↔ ∃ (first rest : Stack) (key value : Word),
      s.isStatic = false ∧ s.stack.val = key :: first.val ∧
      first.val = value :: rest.val ∧ 100 ≤ s.gas ∧
      t = { s with stack := rest, gas := s.gas - 100, pc := s.pc + 1, tracker := TransactionTracker.setTransientStorage s.tracker s.context.environment.currentTarget key value } := by
  constructor
  · intro run
    by_cases static : s.isStatic = true
    · have bad := tstore_static s static
      rw [run] at bad
      cases bad
    · have dynamic : s.isStatic = false := by cases h : s.isStatic <;> simp_all
      cases items : s.stack.val with
      | nil =>
        have bad := tstore_underflow s dynamic items
        rw [run] at bad
        cases bad
      | cons key xs =>
        let first : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
        have items' : s.stack.val = key :: first.val := items
        cases second : first.val with
        | nil =>
          have bad := tstore_second_underflow s first key dynamic items' second
          rw [run] at bad
          cases bad
        | cons value ys =>
          let rest : Stack := ⟨ys, by have bound := first.property; rw [second] at bound; simp at bound; omega⟩
          have second' : first.val = value :: rest.val := second
          by_cases gas : 100 ≤ s.gas
          · have good := tstore_success s first rest key value dynamic items' second' gas
            rw [run] at good
            exact ⟨first, rest, key, value, dynamic, rfl, second', gas, Outcome.continue.inj good⟩
          · have bad := tstore_gas s first rest key value dynamic items' second' (Nat.lt_of_not_ge gas)
            rw [run] at bad
            cases bad
  · rintro ⟨first, rest, key, value, dynamic, items, items', gas, rfl⟩
    exact tstore_success s first rest key value dynamic items items' gas

/-- Observational transient write, independent of association-list representation. -/
def TransientWriteEffect (s t : TransactionState.State) (a : World.Address) (key value : Word) : Prop :=
  let before := TransactionState.Reference.observe s
  let after := TransactionState.Reference.observe t
  TransactionTracker.ContextPreserved before after ∧
    (∀ p, after.writes.transient p =
      if p = (a, key) then (if value = 0 then none else some value) else before.writes.transient p) ∧
    after.writes.accounts = before.writes.accounts ∧ after.writes.storage = before.writes.storage ∧
    after.writes.code = before.writes.code ∧ after.writes.clears = before.writes.clears

/-- Every successful TSTORE refines the total-map write and retains all context observations. -/
theorem tstore_success_observation (s t : State) (run : tstore s = .continue t) :
    ∃ (first rest : Stack) (key value : Word),
      s.isStatic = false ∧ s.stack.val = key :: first.val ∧ first.val = value :: rest.val ∧
      100 ≤ s.gas ∧ TransientWriteEffect s.tracker t.tracker s.context.environment.currentTarget key value := by
  obtain ⟨first, rest, key, value, static, items, second, gas, eq⟩ := (tstore_success_iff s t).mp run
  subst t
  exact ⟨first, rest, key, value, static, items, second, gas,
    TransactionTracker.setTransientStorage_spec s.tracker s.context.environment.currentTarget key value⟩

/-- Independent source-order cases for TSTORE at any code and program counter. -/
inductive TstoreLocal : State → Outcome → Prop where
  | static (s) : s.isStatic = true → TstoreLocal s (.exception s .writeInStaticContext)
  | empty (s) : s.isStatic = false → s.stack.val = [] → TstoreLocal s (.exception s .stackUnderflow)
  | second (s : State) (first : Stack) (key : Word) : s.isStatic = false →
      s.stack.val = key :: first.val → first.val = [] →
      TstoreLocal s (.exception { s with stack := first } .stackUnderflow)
  | gas (s : State) (first rest : Stack) (key value : Word) : s.isStatic = false →
      s.stack.val = key :: first.val → first.val = value :: rest.val → s.gas < 100 →
      TstoreLocal s (.exception { s with stack := rest } .outOfGas)
  | success (s t : State) (first rest : Stack) (key value : Word) (tracker : TransactionState.State) :
      s.isStatic = false → s.stack.val = key :: first.val → first.val = value :: rest.val →
      100 ≤ s.gas → TransientWriteFields s.tracker tracker s.context.environment.currentTarget key value →
      Advances { s with tracker } t (s.pc + 1) (s.gas - 100) rest.val → TstoreLocal s (.continue t)

/-- Each independent TSTORE case implies the corresponding helper outcome. -/
theorem tstore_local_sound {s : State} {out : Outcome} (rule : TstoreLocal s out) : tstore s = out := by
  cases rule with
  | static h => exact tstore_static _ h
  | empty dynamic empty => exact tstore_underflow _ dynamic empty
  | second first key dynamic items empty => exact tstore_second_underflow _ first key dynamic items empty
  | gas first rest key value dynamic items second gas => exact tstore_gas _ first rest key value dynamic items second gas
  | success t first rest key value tracker dynamic items second gas writes fields =>
    have trackerEq := transient_write_fields_unique s.tracker tracker s.context.environment.currentTarget key value writes
    subst tracker
    have frameEq := advances_eq { s with tracker := TransactionTracker.setTransientStorage s.tracker s.context.environment.currentTarget key value }
      t (s.pc + 1) (s.gas - 100) rest fields
    subst t
    exact tstore_success s first rest key value dynamic items second gas

/-- Every state satisfies one of the TSTORE source-order cases. -/
theorem tstore_local_total (s : State) : ∃ out, TstoreLocal s out := by
  by_cases static : s.isStatic = true
  · exact ⟨_, .static s static⟩
  · have dynamic : s.isStatic = false := by cases h : s.isStatic <;> simp_all
    cases items : s.stack.val with
    | nil => exact ⟨_, .empty s dynamic items⟩
    | cons key xs =>
      let first : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
      have items' : s.stack.val = key :: first.val := items
      cases second : first.val with
      | nil => exact ⟨_, .second s first key dynamic items' second⟩
      | cons value ys =>
        let rest : Stack := ⟨ys, by have b := first.property; rw [second] at b; simp at b; omega⟩
        have second' : first.val = value :: rest.val := second
        by_cases gas : 100 ≤ s.gas
        · let tracker := TransactionTracker.setTransientStorage s.tracker s.context.environment.currentTarget key value
          let t := { s with tracker, stack := rest, pc := s.pc + 1, gas := s.gas - 100 }
          exact ⟨_, .success s t first rest key value tracker dynamic items' second' gas
            (transient_write_fields _ _ _ _) (by simp [Advances, t])⟩
        · exact ⟨_, .gas s first rest key value dynamic items' second' (Nat.lt_of_not_ge gas)⟩

/-- TSTORE execution is equivalent to the independent source-order cases. -/
theorem tstore_iff_local (s : State) (out : Outcome) : tstore s = out ↔ TstoreLocal s out := by
  constructor
  · intro run
    obtain ⟨result, rule⟩ := tstore_local_total s
    have sound := tstore_local_sound rule
    rw [run] at sound
    subst result
    exact rule
  · exact tstore_local_sound

/-- A tracker snapshot restores transient writes after an arbitrary transient update. -/
theorem transient_snapshot_rollback (s : TransactionState.State) (a : World.Address) (key value : Word) :
    TransactionState.rollback (TransactionTracker.setTransientStorage (TransactionState.snapshot s) a key value) = .ok s := by
  cases s
  rfl

end EthLib.EVM.Frame
