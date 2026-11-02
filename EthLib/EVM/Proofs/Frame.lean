module

public import EthLib.EVM.Frame.Rules
public import EthLib.EVM.Proofs.Stack
public import EthLib.EVM.Proofs.JumpDest

/-!
# Frame invariants

These type invariants do not prove that the executable step refines Cancun.
-/

@[expose] public section
namespace EthLib.EVM.Frame

/-- Every frame carries a valid allocated memory. -/
theorem memory_valid (s : State) : Memory.Allocation.Valid s.memory := s.memoryValid

/-- Every frame carries a bounded stack. -/
theorem stack_bounded (s : State) : s.stack.val.length ≤ 1024 := s.stack.property

/-- Exceptional gas is zero regardless of the diagnostic input. -/
theorem settle_exception (s : State) (e : Exception) :
    settle (.exception s e) = some (.exceptional 0 e) := rfl

/-- A successful stop retains its remaining gas. -/
theorem settle_stop (s : State) : settle (.stop s) = some (.stopped s.gas) := rfl

/-- Tooling results are not message-boundary outcomes. -/
theorem settle_unsupported (s : State) (op : Opcode) :
    settle (.unsupported s op) = none := rfl

/-- A continuing step has not reached a message boundary. -/
theorem settle_continue (s : State) : settle (.continue s) = none := rfl

/-- A manually constructed revert preserves its supplied gas and output. -/
theorem settle_revert (s : State) (gas : Nat) (output : ByteArray) :
    settle (.revert s gas output) = some (.reverted gas output) := rfl

/-- End of code is a normal stop and leaves the frame unchanged. -/
theorem step_end (s : State) (h : s.code.size ≤ s.pc) : step s = .stop s := by
  simp [step, Nat.not_lt.mpr h]

/-- STOP advances its program counter once. -/
theorem step_stop (s : State) (h : At s (some .stop)) :
    step s = .stop { s with pc := s.pc + 1 } := by
  obtain ⟨bounds, decoded⟩ := h
  simp [step, bounds, decoded]

/-- An unassigned byte produces an invalid-opcode exception. -/
theorem step_unassigned (s : State) (h : At s none) :
    step s = .exception s .invalidOpcode := by
  obtain ⟨bounds, decoded⟩ := h
  simp [step, bounds, decoded]

/-- The designated INVALID instruction produces an invalid-opcode exception. -/
theorem step_invalid (s : State) (h : At s (some .invalid)) :
    step s = .exception s .invalidOpcode := by
  obtain ⟨bounds, decoded⟩ := h
  simp [step, bounds, decoded]

/-- PUSH checks gas before stack capacity. -/
theorem step_push_gas (s : State) (n : Fin 33) (h : At s (some (.push n)))
    (gas : s.gas < (if n.val = 0 then 2 else 3)) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  have ng : ¬ (if n.val = 0 then 2 else 3) ≤ s.gas := Nat.not_le.mpr gas
  simp only [step, dite_eq_left bounds, decoded, charge, Gas.charge, ite_eq_right ng]

/-- DUP checks gas before stack depth. -/
theorem step_dup_gas (s : State) (i : Fin 16) (h : At s (some (.dup i)))
    (gas : s.gas < 3) : step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  simp [step, bounds, decoded, charge, Gas.charge, Nat.not_le.mpr gas]

/-- SWAP checks gas before stack depth. -/
theorem step_swap_gas (s : State) (i : Fin 16) (h : At s (some (.swap i)))
    (gas : s.gas < 3) : step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  simp [step, bounds, decoded, charge, Gas.charge, Nat.not_le.mpr gas]

/-- POP checks stack depth before gas. -/
theorem step_pop_empty (s : State) (h : At s (some .pop)) (empty : s.stack.val = []) :
    step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  have pop : s.stack.pop = .error .underflow :=
    (Proofs.Stack.pop_underflow_iff s.stack).mpr empty
  simp [step, bounds, decoded, pop, failStack]

/-- PUSH overflows after a successful gas check. -/
theorem step_push_full (s : State) (n : Fin 33) (h : At s (some (.push n)))
    (gas : (if n.val = 0 then 2 else 3) ≤ s.gas) (full : s.stack.val.length = 1024) :
    step s = .exception s .stackOverflow := by
  obtain ⟨bounds, decoded⟩ := h
  have push : s.stack.push (PushImmediate.value s.code s.pc n) = .error .overflow :=
    (Proofs.Stack.push_overflow_iff _ _).mpr full
  simp only [step, dite_eq_left bounds, decoded, charge, Gas.charge, ite_eq_left gas, push,
    failStack]

/-- DUP reports underflow after charging gas. -/
theorem step_dup_empty (s : State) (i : Fin 16) (h : At s (some (.dup i)))
    (gas : 3 ≤ s.gas) (empty : s.stack.val.length ≤ i.val) :
    step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  have dup : s.stack.dup i = .error .underflow :=
    (Proofs.Stack.dup_underflow_iff _ _).mpr empty
  simp [step, bounds, decoded, charge, Gas.charge, gas, dup, failStack]

/-- DUP reports overflow on a full stack after charging gas. -/
theorem step_dup_full (s : State) (i : Fin 16) (h : At s (some (.dup i)))
    (gas : 3 ≤ s.gas) (full : s.stack.val.length = 1024) :
    step s = .exception s .stackOverflow := by
  obtain ⟨bounds, decoded⟩ := h
  have dup : s.stack.dup i = .error .overflow :=
    (Proofs.Stack.dup_overflow_iff _ _).mpr full
  simp [step, bounds, decoded, charge, Gas.charge, gas, dup, failStack]

/-- SWAP reports underflow after charging gas. -/
theorem step_swap_empty (s : State) (i : Fin 16) (h : At s (some (.swap i)))
    (gas : 3 ≤ s.gas) (empty : s.stack.val.length ≤ i.val + 1) :
    step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  have swap : s.stack.swap i = .error .underflow :=
    (Proofs.Stack.swap_underflow_iff _ _).mpr empty
  simp [step, bounds, decoded, charge, Gas.charge, gas, swap, failStack]

/-- Exact field observations determine a frame update. -/
theorem advances_eq (s t : State) (pc gas : Nat) (stack : Stack)
    (h : Advances s t pc gas stack.val) :
    t = { s with pc, gas, stack } := by
  rcases h with ⟨code, memory, pcEq, gasEq, stackEq, contextEq, returnDataEq⟩
  have stackEq' : t.stack = stack := Subtype.ext stackEq
  cases s
  cases t
  simp_all

/-- A successful PUSH has the stated stack, gas, and program counter. -/
theorem step_push (s t : State) (n : Fin 33) (h : At s (some (.push n)))
    (gas : (if n.val = 0 then 2 else 3) ≤ s.gas) (room : s.stack.val.length < 1024)
    (fields : Advances s t (PushImmediate.nextPC s.pc n)
      (s.gas - (if n.val = 0 then 2 else 3))
      (PushImmediate.value s.code s.pc n :: s.stack.val)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let stack : Stack := ⟨PushImmediate.value s.code s.pc n :: s.stack.val, by simp; omega⟩
  have push : s.stack.push (PushImmediate.value s.code s.pc n) = .ok stack :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨room, rfl⟩
  have update := advances_eq s t (PushImmediate.nextPC s.pc n)
    (s.gas - (if n.val = 0 then 2 else 3)) stack fields
  simp only [step, dite_eq_left bounds, decoded, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- A successful DUP copies the selected entry. -/
theorem step_dup (s t : State) (i : Fin 16) (h : At s (some (.dup i)))
    (depth : i.val < s.stack.val.length) (gas : 3 ≤ s.gas)
    (room : s.stack.val.length < 1024)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (s.stack.val[i.val] :: s.stack.val)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let stack : Stack := ⟨s.stack.val[i.val] :: s.stack.val, by simp; omega⟩
  have dup : s.stack.dup i = .ok stack :=
    (Proofs.Stack.dup_ok_iff _ _ _).mpr ⟨depth, room, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 3) stack fields
  simp only [step, dite_eq_left bounds, decoded, charge, Gas.charge, ite_eq_left gas, dup]
  rw [update]

/-- A successful SWAP exchanges the top and the selected entry. -/
theorem step_swap (s t : State) (i : Fin 16) (h : At s (some (.swap i)))
    (depth : i.val + 1 < s.stack.val.length) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3)
      ((s.stack.val.set 0 s.stack.val[i.val + 1]).set (i.val + 1)
        (s.stack.val[0]'(by omega)))) : step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let stack : Stack := ⟨(s.stack.val.set 0 s.stack.val[i.val + 1]).set (i.val + 1)
    (s.stack.val[0]'(by omega)), by simpa using s.stack.property⟩
  have swap : s.stack.swap i = .ok stack :=
    (Proofs.Stack.swap_ok_iff _ _ _).mpr ⟨depth, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 3) stack fields
  simp only [step, dite_eq_left bounds, decoded, charge, Gas.charge, ite_eq_left gas, swap]
  rw [update]

/-- POP with a nonempty stack checks gas next. -/
theorem step_pop_gas (s : State) (x : Word) (xs : List Word)
    (h : At s (some .pop)) (items : s.stack.val = x :: xs) (gas : s.gas < 2) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let stack : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  simp [step, bounds, decoded, pop, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful POP removes exactly the top entry. -/
theorem step_pop (s t : State) (x : Word) (xs : List Word)
    (h : At s (some .pop)) (items : s.stack.val = x :: xs) (gas : 2 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 2) xs) : step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let stack : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have update := advances_eq s t (s.pc + 1) (s.gas - 2) stack fields
  simp only [step, dite_eq_left bounds, decoded, pop, charge, Gas.charge, ite_eq_left gas]
  rw [update]

/-- ADD checks both operands before gas. -/
theorem step_add_empty (s : State) (h : At s (some .add))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- ADD with two operands checks gas before computing the result. -/
theorem step_add_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .add)) (items : s.stack.val = x :: y :: xs) (gas : s.gas < 3) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful ADD replaces the first two entries by their modular sum. -/
theorem step_add (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .add)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.add x y :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  let final : Stack := ⟨Word.add x y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : second.push (Word.add x y) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 3) final fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- EXP checks both operands before gas. -/
theorem step_exp_empty (s : State) (h : At s (some .exp))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- EXP with two operands checks gas before computing the result. -/
theorem step_exp_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .exp)) (items : s.stack.val = x :: y :: xs) (gas : s.gas < Gas.expCost y) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful EXP replaces the base and exponent with their modular power. -/
theorem step_exp (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .exp)) (items : s.stack.val = x :: y :: xs) (gas : Gas.expCost y ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - Gas.expCost y) (Word.exp x y :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  let final : Stack := ⟨Word.exp x y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : second.push (Word.exp x y) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - Gas.expCost y) final fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- ADDMOD checks all three operands before gas. -/
theorem step_addmod_empty (s : State) (h : At s (some .addmod))
    (short : s.stack.val.length < 3) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have p : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, p, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let first : Stack := Stack.empty
      have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have p2 : first.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, p1, p2, failStack]
    | cons y ys =>
      cases ys with
      | nil =>
        let first : Stack := ⟨[y], by simp⟩
        let second : Stack := Stack.empty
        have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
        have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
        have p3 : second.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
        simp [step, bounds, decoded, p1, p2, p3, failStack]
      | cons z zs => simp [items] at short; omega

/-- ADDMOD checks gas after obtaining three operands. -/
theorem step_addmod_gas (s : State) (x y m : Word) (xs : List Word)
    (h : At s (some .addmod)) (items : s.stack.val = x :: y :: m :: xs) (gas : s.gas < 8) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: m :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let second : Stack := ⟨m :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let third : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have p3 : second.pop = .ok (m, third) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, p3, charge, Gas.charge, Nat.not_le.mpr gas]

/-- Successful ADDMOD replaces three operands with one result. -/
theorem step_addmod (s t : State) (x y m : Word) (xs : List Word)
    (h : At s (some .addmod)) (items : s.stack.val = x :: y :: m :: xs) (gas : 8 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 8) (Word.addmod x y m :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: m :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let second : Stack := ⟨m :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let third : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  let final : Stack := ⟨Word.addmod x y m :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have p3 : second.pop = .ok (m, third) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : third.push (Word.addmod x y m) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 8) final fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, p3, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- MULMOD checks all three operands before gas. -/
theorem step_mulmod_empty (s : State) (h : At s (some .mulmod))
    (short : s.stack.val.length < 3) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have p : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, p, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let first : Stack := Stack.empty
      have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have p2 : first.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, p1, p2, failStack]
    | cons y ys =>
      cases ys with
      | nil =>
        let first : Stack := ⟨[y], by simp⟩
        let second : Stack := Stack.empty
        have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
        have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
        have p3 : second.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
        simp [step, bounds, decoded, p1, p2, p3, failStack]
      | cons z zs => simp [items] at short; omega

/-- MULMOD checks gas after obtaining three operands. -/
theorem step_mulmod_gas (s : State) (x y m : Word) (xs : List Word)
    (h : At s (some .mulmod)) (items : s.stack.val = x :: y :: m :: xs) (gas : s.gas < 8) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: m :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let second : Stack := ⟨m :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let third : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have p3 : second.pop = .ok (m, third) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, p3, charge, Gas.charge, Nat.not_le.mpr gas]

/-- Successful MULMOD replaces three operands with one result. -/
theorem step_mulmod (s t : State) (x y m : Word) (xs : List Word)
    (h : At s (some .mulmod)) (items : s.stack.val = x :: y :: m :: xs) (gas : 8 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 8) (Word.mulmod x y m :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: m :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let second : Stack := ⟨m :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let third : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  let final : Stack := ⟨Word.mulmod x y m :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have p3 : second.pop = .ok (m, third) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : third.push (Word.mulmod x y m) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 8) final fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, p3, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- LT checks both operands before gas. -/
theorem step_lt_empty (s : State) (h : At s (some .lt))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- LT with two operands checks gas before computing the result. -/
theorem step_lt_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .lt)) (items : s.stack.val = x :: y :: xs) (gas : s.gas < 3) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful LT replaces the first two entries by the result. -/
theorem step_lt (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .lt)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.ltResult x y :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  let final : Stack := ⟨Word.ltResult x y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : second.push (Word.ltResult x y) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 3) final fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- GT checks both operands before gas. -/
theorem step_gt_empty (s : State) (h : At s (some .gt))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- GT with two operands checks gas before computing the result. -/
theorem step_gt_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .gt)) (items : s.stack.val = x :: y :: xs) (gas : s.gas < 3) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful GT replaces the first two entries by the result. -/
theorem step_gt (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .gt)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.gtResult x y :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  let final : Stack := ⟨Word.gtResult x y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : second.push (Word.gtResult x y) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 3) final fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- SLT checks both operands before gas. -/
theorem step_slt_empty (s : State) (h : At s (some .slt))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- SLT with two operands checks gas before computing the result. -/
theorem step_slt_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .slt)) (items : s.stack.val = x :: y :: xs) (gas : s.gas < 3) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful SLT replaces the first two entries by the result. -/
theorem step_slt (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .slt)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.sltResult x y :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  let final : Stack := ⟨Word.sltResult x y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : second.push (Word.sltResult x y) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 3) final fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- SGT checks both operands before gas. -/
theorem step_sgt_empty (s : State) (h : At s (some .sgt))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- SGT with two operands checks gas before computing the result. -/
theorem step_sgt_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .sgt)) (items : s.stack.val = x :: y :: xs) (gas : s.gas < 3) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful SGT replaces the first two entries by the result. -/
theorem step_sgt (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .sgt)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.sgtResult x y :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  let final : Stack := ⟨Word.sgtResult x y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : second.push (Word.sgtResult x y) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 3) final fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- EQ checks both operands before gas. -/
theorem step_eq_empty (s : State) (h : At s (some .eq))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- EQ with two operands checks gas before computing the result. -/
theorem step_eq_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .eq)) (items : s.stack.val = x :: y :: xs) (gas : s.gas < 3) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful EQ replaces the first two entries by the result. -/
theorem step_eq (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .eq)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.eqResult x y :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  let final : Stack := ⟨Word.eqResult x y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : second.push (Word.eqResult x y) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 3) final fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- AND checks both operands before gas. -/
theorem step_and_empty (s : State) (h : At s (some .and))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- AND with two operands checks gas before computing the result. -/
theorem step_and_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .and)) (items : s.stack.val = x :: y :: xs) (gas : s.gas < 3) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful AND replaces the first two entries by the result. -/
theorem step_and (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .and)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.bitwiseAnd x y :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  let final : Stack := ⟨Word.bitwiseAnd x y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : second.push (Word.bitwiseAnd x y) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 3) final fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- SHL checks both operands before gas. -/
theorem step_shl_empty (s : State) (h : At s (some .shl))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- SHL with two operands checks gas before computing the result. -/
theorem step_shl_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .shl)) (items : s.stack.val = x :: y :: xs) (gas : s.gas < 3) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful SHL replaces the first two entries by the result. -/
theorem step_shl (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .shl)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.shl x y :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  let final : Stack := ⟨Word.shl x y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : second.push (Word.shl x y) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 3) final fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- SHR checks both operands before gas. -/
theorem step_shr_empty (s : State) (h : At s (some .shr))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- SHR with two operands checks gas before computing the result. -/
theorem step_shr_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .shr)) (items : s.stack.val = x :: y :: xs) (gas : s.gas < 3) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful SHR replaces the first two entries by the result. -/
theorem step_shr (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .shr)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.shr x y :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  let final : Stack := ⟨Word.shr x y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : second.push (Word.shr x y) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 3) final fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- SAR checks both operands before gas. -/
theorem step_sar_empty (s : State) (h : At s (some .sar))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- SAR with two operands checks gas before computing the result. -/
theorem step_sar_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .sar)) (items : s.stack.val = x :: y :: xs) (gas : s.gas < 3) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful SAR replaces the first two entries by the result. -/
theorem step_sar (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .sar)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.sar x y :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  let final : Stack := ⟨Word.sar x y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : second.push (Word.sar x y) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 3) final fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- BYTE checks both operands before gas. -/
theorem step_byte_empty (s : State) (h : At s (some .byte))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- BYTE with two operands checks gas before computing the result. -/
theorem step_byte_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .byte)) (items : s.stack.val = x :: y :: xs) (gas : s.gas < 3) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful BYTE replaces the first two entries by the result. -/
theorem step_byte (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .byte)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.byte x y :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  let final : Stack := ⟨Word.byte x y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : second.push (Word.byte x y) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 3) final fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- SIGNEXTEND checks both operands before gas. -/
theorem step_signextend_empty (s : State) (h : At s (some .signextend))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- SIGNEXTEND with two operands checks gas before computing the result. -/
theorem step_signextend_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .signextend)) (items : s.stack.val = x :: y :: xs) (gas : s.gas < 5) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful SIGNEXTEND replaces the first two entries by the result. -/
theorem step_signextend (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .signextend)) (items : s.stack.val = x :: y :: xs) (gas : 5 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 5) (Word.signextend x y :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  let final : Stack := ⟨Word.signextend x y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : second.push (Word.signextend x y) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 5) final fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- OR checks both operands before gas. -/
theorem step_or_empty (s : State) (h : At s (some .or))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- OR with two operands checks gas before computing the result. -/
theorem step_or_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .or)) (items : s.stack.val = x :: y :: xs) (gas : s.gas < 3) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful OR replaces the first two entries by the result. -/
theorem step_or (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .or)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.bitwiseOr x y :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  let final : Stack := ⟨Word.bitwiseOr x y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : second.push (Word.bitwiseOr x y) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 3) final fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- XOR checks both operands before gas. -/
theorem step_xor_empty (s : State) (h : At s (some .xor))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- XOR with two operands checks gas before computing the result. -/
theorem step_xor_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .xor)) (items : s.stack.val = x :: y :: xs) (gas : s.gas < 3) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful XOR replaces the first two entries by the result. -/
theorem step_xor (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .xor)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.bitwiseXor x y :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  let final : Stack := ⟨Word.bitwiseXor x y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : second.push (Word.bitwiseXor x y) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 3) final fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- CALLDATALOAD checks its operand before gas. -/
theorem step_calldataload_empty (s : State) (h : At s (some .calldataload)) (empty : s.stack.val = []) :
    step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr empty
  simp [step, bounds, decoded, pop, failStack]

/-- CALLDATALOAD checks gas after popping its operand. -/
theorem step_calldataload_gas (s : State) (x : Word) (xs : List Word)
    (h : At s (some .calldataload)) (items : s.stack.val = x :: xs) (gas : s.gas < 3) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let rest : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  simp [step, bounds, decoded, pop, charge, Gas.charge, Nat.not_le.mpr gas]

/-- CALLDATALOAD replaces its operand with the result. -/
theorem step_calldataload (s t : State) (x : Word) (xs : List Word)
    (h : At s (some .calldataload)) (items : s.stack.val = x :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (CallData.load s.context x :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let rest : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  let final : Stack := ⟨CallData.load s.context x :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have push : rest.push (CallData.load s.context x) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 3) final fields
  simp only [step, dite_eq_left bounds, decoded, pop, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- BLOBHASH checks its operand before gas. -/
theorem step_blobhash_empty (s : State) (h : At s (some .blobhash)) (empty : s.stack.val = []) :
    step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr empty
  simp [step, bounds, decoded, blobHash, pop, failStack]

/-- BLOBHASH checks gas after popping its operand. -/
theorem step_blobhash_gas (s : State) (x : Word) (xs : List Word)
    (h : At s (some .blobhash)) (items : s.stack.val = x :: xs) (gas : s.gas < 3) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let rest : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  simp [step, bounds, decoded, blobHash, pop, charge, Gas.charge, Nat.not_le.mpr gas]

/-- BLOBHASH replaces its operand with the result. -/
theorem step_blobhash (s t : State) (x : Word) (xs : List Word)
    (h : At s (some .blobhash)) (items : s.stack.val = x :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Environment.blobHash s.context.environment x :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let rest : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  let final : Stack := ⟨Environment.blobHash s.context.environment x :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have push : rest.push (Environment.blobHash s.context.environment x) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 3) final fields
  simp only [step, dite_eq_left bounds, decoded, blobHash, pop, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- BLOCKHASH checks its operand before gas. -/
theorem step_blockhash_empty (s : State) (h : At s (some .blockhash)) (empty : s.stack.val = []) :
    step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr empty
  simp [step, bounds, decoded, blockHash, pop, failStack]

/-- BLOCKHASH checks gas after popping its operand. -/
theorem step_blockhash_gas (s : State) (x : Word) (xs : List Word)
    (h : At s (some .blockhash)) (items : s.stack.val = x :: xs) (gas : s.gas < 20) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let rest : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  simp [step, bounds, decoded, blockHash, pop, charge, Gas.charge, Nat.not_le.mpr gas]

/-- BLOCKHASH replaces its operand with the result. -/
theorem step_blockhash (s t : State) (x : Word) (xs : List Word)
    (h : At s (some .blockhash)) (items : s.stack.val = x :: xs) (gas : 20 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 20) (Environment.blockHash s.context.environment.blockHashes s.context.environment.number x :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let rest : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  let final : Stack := ⟨Environment.blockHash s.context.environment.blockHashes s.context.environment.number x :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have push : rest.push (Environment.blockHash s.context.environment.blockHashes s.context.environment.number x) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 20) final fields
  simp only [step, dite_eq_left bounds, decoded, blockHash, pop, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- ISZERO checks its operand before gas. -/
theorem step_iszero_empty (s : State) (h : At s (some .iszero)) (empty : s.stack.val = []) :
    step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr empty
  simp [step, bounds, decoded, pop, failStack]

/-- ISZERO checks gas after popping its operand. -/
theorem step_iszero_gas (s : State) (x : Word) (xs : List Word)
    (h : At s (some .iszero)) (items : s.stack.val = x :: xs) (gas : s.gas < 3) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let rest : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  simp [step, bounds, decoded, pop, charge, Gas.charge, Nat.not_le.mpr gas]

/-- ISZERO replaces its operand with the result. -/
theorem step_iszero (s t : State) (x : Word) (xs : List Word)
    (h : At s (some .iszero)) (items : s.stack.val = x :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.iszeroResult x :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let rest : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  let final : Stack := ⟨Word.iszeroResult x :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have push : rest.push (Word.iszeroResult x) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 3) final fields
  simp only [step, dite_eq_left bounds, decoded, pop, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- CLZ checks its operand before gas. -/
theorem step_clz_empty (s : State) (h : At s (some .clz)) (empty : s.stack.val = []) :
    step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr empty
  simp [step, bounds, decoded, clz, pop, failStack]

/-- CLZ checks gas after popping its operand. -/
theorem step_clz_gas (s : State) (x : Word) (xs : List Word)
    (h : At s (some .clz)) (items : s.stack.val = x :: xs) (gas : s.gas < 5) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let rest : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  simp [step, bounds, decoded, clz, pop, charge, Gas.charge, Nat.not_le.mpr gas]

/-- CLZ replaces its operand with the result. -/
theorem step_clz (s t : State) (x : Word) (xs : List Word)
    (h : At s (some .clz)) (items : s.stack.val = x :: xs) (gas : 5 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 5) (Word.countLeadingZeros x :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let rest : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  let final : Stack := ⟨Word.countLeadingZeros x :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have push : rest.push (Word.countLeadingZeros x) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 5) final fields
  simp only [step, dite_eq_left bounds, decoded, clz, pop, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- NOT checks its operand before gas. -/
theorem step_not_empty (s : State) (h : At s (some .not)) (empty : s.stack.val = []) :
    step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr empty
  simp [step, bounds, decoded, pop, failStack]

/-- NOT checks gas after popping its operand. -/
theorem step_not_gas (s : State) (x : Word) (xs : List Word)
    (h : At s (some .not)) (items : s.stack.val = x :: xs) (gas : s.gas < 3) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let rest : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  simp [step, bounds, decoded, pop, charge, Gas.charge, Nat.not_le.mpr gas]

/-- NOT replaces its operand with the result. -/
theorem step_not (s t : State) (x : Word) (xs : List Word)
    (h : At s (some .not)) (items : s.stack.val = x :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.bitwiseNot x :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let rest : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  let final : Stack := ⟨Word.bitwiseNot x :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have push : rest.push (Word.bitwiseNot x) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 3) final fields
  simp only [step, dite_eq_left bounds, decoded, pop, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- MUL checks both operands before gas. -/
theorem step_mul_empty (s : State) (h : At s (some .mul))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- MUL with two operands checks gas before computing the result. -/
theorem step_mul_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .mul)) (items : s.stack.val = x :: y :: xs) (gas : s.gas < 5) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful MUL replaces the first two entries by their mul result. -/
theorem step_mul (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .mul)) (items : s.stack.val = x :: y :: xs) (gas : 5 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 5) (Word.mul x y :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  let final : Stack := ⟨Word.mul x y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : second.push (Word.mul x y) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 5) final fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- SUB checks both operands before gas. -/
theorem step_sub_empty (s : State) (h : At s (some .sub))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- SUB with two operands checks gas before computing the result. -/
theorem step_sub_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .sub)) (items : s.stack.val = x :: y :: xs) (gas : s.gas < 3) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful SUB replaces the first two entries by their sub result. -/
theorem step_sub (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .sub)) (items : s.stack.val = x :: y :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3) (Word.sub x y :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  let final : Stack := ⟨Word.sub x y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : second.push (Word.sub x y) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 3) final fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- DIV checks both operands before gas. -/
theorem step_div_empty (s : State) (h : At s (some .div))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- DIV with two operands checks gas before computing the result. -/
theorem step_div_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .div)) (items : s.stack.val = x :: y :: xs) (gas : s.gas < 5) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful DIV replaces the first two entries by their div result. -/
theorem step_div (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .div)) (items : s.stack.val = x :: y :: xs) (gas : 5 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 5) (Word.div x y :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  let final : Stack := ⟨Word.div x y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : second.push (Word.div x y) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 5) final fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- MOD checks both operands before gas. -/
theorem step_mod_empty (s : State) (h : At s (some .mod))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- MOD with two operands checks gas before computing the result. -/
theorem step_mod_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .mod)) (items : s.stack.val = x :: y :: xs) (gas : s.gas < 5) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful MOD replaces the first two entries by their mod result. -/
theorem step_mod (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .mod)) (items : s.stack.val = x :: y :: xs) (gas : 5 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 5) (Word.mod x y :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  let final : Stack := ⟨Word.mod x y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : second.push (Word.mod x y) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 5) final fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- SDIV checks both operands before gas. -/
theorem step_sdiv_empty (s : State) (h : At s (some .sdiv))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- SDIV with two operands checks gas before computing the result. -/
theorem step_sdiv_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .sdiv)) (items : s.stack.val = x :: y :: xs) (gas : s.gas < 5) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful SDIV replaces the first two entries by their sdiv result. -/
theorem step_sdiv (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .sdiv)) (items : s.stack.val = x :: y :: xs) (gas : 5 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 5) (Word.sdiv x y :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  let final : Stack := ⟨Word.sdiv x y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : second.push (Word.sdiv x y) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 5) final fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- SMOD checks both operands before gas. -/
theorem step_smod_empty (s : State) (h : At s (some .smod))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- SMOD with two operands checks gas before computing the result. -/
theorem step_smod_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .smod)) (items : s.stack.val = x :: y :: xs) (gas : s.gas < 5) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful SMOD replaces the first two entries by their smod result. -/
theorem step_smod (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .smod)) (items : s.stack.val = x :: y :: xs) (gas : 5 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 5) (Word.smod x y :: xs)) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  let final : Stack := ⟨Word.smod x y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : second.push (Word.smod x y) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 5) final fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- The source-oriented frame boundary relation matches the scanner proof relation. -/
theorem jumpBoundary_iff (code : ByteArray) (pc x : Nat) :
    JumpBoundaryFrom code pc x ↔ Proofs.JumpDest.BoundaryFrom code pc x := by
  constructor
  · intro h
    induction h with
    | here pc inside => exact .here pc inside
    | step pc x inside _ ih =>
      exact .step pc x inside (by simpa [jumpSourceLength, Proofs.JumpDest.sourceLength] using ih)
  · intro h
    induction h with
    | here pc inside => exact .here pc inside
    | step pc x inside _ ih =>
      exact .step pc x inside (by simpa [jumpSourceLength, Proofs.JumpDest.sourceLength] using ih)

/-- Executable target lookup is equivalent to the independent boundary rule. -/
theorem validJumpDest_iff (code : ByteArray) (pc : Nat) :
    JumpDest.contains code pc = true ↔ ValidJumpDest code pc := by
  rw [Proofs.JumpDest.contains_iff_boundary]
  simp only [ValidJumpDest, Proofs.JumpDest.Boundary, jumpBoundary_iff]

/-- JUMP checks stack depth before gas. -/
theorem step_jump_empty (s : State) (h : At s (some .jump)) (empty : s.stack.val = []) :
    step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  have pop : s.stack.pop = .error .underflow :=
    (Proofs.Stack.pop_underflow_iff s.stack).mpr empty
  simp [step, bounds, decoded, pop, failStack]

/-- JUMP checks gas after the operand. -/
theorem step_jump_gas (s : State) (x : Word) (xs : List Word)
    (h : At s (some .jump)) (items : s.stack.val = x :: xs) (gas : s.gas < 8) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let stack : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  simp [step, bounds, decoded, pop, charge, Gas.charge, Nat.not_le.mpr gas]

/-- JUMPI checks both operands before gas. -/
theorem step_jumpi_empty (s : State) (h : At s (some .jumpi))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- JUMPI checks gas after both operands. -/
theorem step_jumpi_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .jumpi)) (items : s.stack.val = x :: y :: xs) (gas : s.gas < 10) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have bound := s.stack.property; rw [items] at bound; simp at bound ⊢; omega⟩
  let second : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- JUMP rejects a non-boundary target after the gas check. -/
theorem step_jump_invalid (s : State) (x : Word) (xs : List Word)
    (h : At s (some .jump)) (items : s.stack.val = x :: xs) (gas : 8 ≤ s.gas)
    (invalid : ¬ ValidJumpDest s.code x.toNat) : step s = .exception s .invalidJumpDestination := by
  obtain ⟨bounds, decoded⟩ := h
  let stack : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have target : JumpDest.contains s.code x.toNat = false := by
    cases h : JumpDest.contains s.code x.toNat with
    | false => rfl
    | true => exact False.elim (invalid ((validJumpDest_iff _ _).mp h))
  simp [step, bounds, decoded, pop, charge, Gas.charge, gas, target]

/-- JUMP consumes its destination and transfers control to it. -/
theorem step_jump (s t : State) (x : Word) (xs : List Word)
    (h : At s (some .jump)) (items : s.stack.val = x :: xs) (gas : 8 ≤ s.gas)
    (valid : ValidJumpDest s.code x.toNat) (fields : Advances s t x.toNat (s.gas - 8) xs) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let stack : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have target := (validJumpDest_iff s.code x.toNat).mpr valid
  have update := advances_eq s t x.toNat (s.gas - 8) stack fields
  simp only [step, dite_eq_left bounds, decoded, pop, charge, Gas.charge, ite_eq_left gas, target, ↓reduceIte]
  rw [update]

/-- JUMPI invalid case follows the source check order. -/
theorem step_jumpi_invalid (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .jumpi)) (items : s.stack.val = x :: y :: xs) (gas : 10 ≤ s.gas)
    (cond : y.toNat ≠ 0) (invalid : ¬ ValidJumpDest s.code x.toNat) : step s = .exception s .invalidJumpDestination := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let second : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have target : JumpDest.contains s.code x.toNat = false := by
    cases h : JumpDest.contains s.code x.toNat with
    | false => rfl
    | true => exact False.elim (invalid ((validJumpDest_iff _ _).mp h))
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, gas, cond, target]

/-- JUMPI false case follows the source check order. -/
theorem step_jumpi_false (s : State) (t : State) (x y : Word) (xs : List Word)
    (h : At s (some .jumpi)) (items : s.stack.val = x :: y :: xs) (gas : 10 ≤ s.gas)
    (cond : y.toNat = 0)  (fields : Advances s t (s.pc + 1) (s.gas - 10) xs) : step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let second : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have update := advances_eq s t (s.pc + 1) (s.gas - 10) second fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas, cond, ↓reduceIte]
  rw [update]

/-- JUMPI true case follows the source check order. -/
theorem step_jumpi_true (s : State) (t : State) (x y : Word) (xs : List Word)
    (h : At s (some .jumpi)) (items : s.stack.val = x :: y :: xs) (gas : 10 ≤ s.gas)
    (cond : y.toNat ≠ 0) (valid : ValidJumpDest s.code x.toNat) (fields : Advances s t (x.toNat) (s.gas - 10) xs) : step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let second : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have target := (validJumpDest_iff s.code x.toNat).mpr valid
  have update := advances_eq s t x.toNat (s.gas - 10) second fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas, cond, ↓reduceIte, target]
  rw [update]

/-- JUMPDEST reports insufficient gas. -/
theorem step_jumpdest_gas (s : State) (h : At s (some .jumpdest)) (gas : s.gas < 1) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  simp [step, bounds, decoded, charge, Gas.charge, Nat.not_le.mpr gas]

/-- JUMPDEST consumes one gas and advances one byte. -/
theorem step_jumpdest (s t : State) (h : At s (some .jumpdest)) (gas : 1 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 1) s.stack.val) : step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  have update := advances_eq s t (s.pc + 1) (s.gas - 1) s.stack fields
  simp only [step, dite_eq_left bounds, decoded, charge, Gas.charge, ite_eq_left gas]
  rw [update]

/-- Observation conversion is reduction modulo the word modulus on all inputs. -/
theorem observationWord_toNat (n : Nat) :
    (observationWord n).toNat = n % Word.modulus := by
  simp [observationWord, Word.modulus]

/-- Within the source U256 domain the conversion is exact. -/
theorem observationWord_exact (n : Nat) (h : n < Word.modulus) :
    (observationWord n).toNat = n := by
  rw [observationWord_toNat, Nat.mod_eq_of_lt h]

/-- The checked public constructor agrees in the source U256 domain. -/
theorem observationWord_checked (n : Nat) (h : n < Word.modulus) :
    Word.ofNat n = .ok (observationWord n) := by
  simp only [Word.ofNat, dite_eq_left h, Except.ok.injEq]
  apply BitVec.eq_of_toNat_eq
  rw [observationWord_exact n h]
  rfl

/-- Every source-representable observation has its exact natural value. -/
theorem observation_value_exact (o : Observation) (s : State)
    (h : o.value s < Word.modulus) :
    (observationWord (o.value s)).toNat = o.value s :=
  observationWord_exact _ h

/-- The observation helper checks gas before stack capacity for every value function. -/
theorem observe_gas (s : State) (value : Nat → Nat) (h : s.gas < 2) :
    observe s value = .exception s .outOfGas := by
  simp [observe, charge, Gas.charge, Nat.not_le.mpr h]

/-- The observation helper rejects a full stack after charging. -/
theorem observe_full (s : State) (value : Nat → Nat) (gas : 2 ≤ s.gas)
    (full : s.stack.val.length = 1024) : observe s value = .exception s .stackOverflow := by
  have push : s.stack.push (observationWord (value (s.gas - 2))) = .error .overflow :=
    (Proofs.Stack.push_overflow_iff _ _).mpr full
  simp [observe, charge, Gas.charge, gas, push, failStack]

/-- The observation helper pushes its value and preserves all other fields. -/
theorem observe_success (s t : State) (value : Nat → Nat) (gas : 2 ≤ s.gas)
    (room : s.stack.val.length < 1024)
    (fields : Advances s t (s.pc + 1) (s.gas - 2)
      (observationWord (value (s.gas - 2)) :: s.stack.val)) :
    observe s value = .continue t := by
  let stack : Stack := ⟨observationWord (value (s.gas - 2)) :: s.stack.val, by simp; omega⟩
  have push : s.stack.push (observationWord (value (s.gas - 2))) = .ok stack :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨room, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 2) stack fields
  simp only [observe, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- Gas is checked before the observation can overflow the stack. -/
theorem step_observation_gas (s : State) (o : Observation)
    (h : At s (some o.opcode)) (gas : s.gas < 2) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  cases o <;> simp_all [Observation.opcode, step, blobBaseFee, observe, charge, Gas.charge,
    Nat.not_le.mpr gas]

/-- A full stack overflows after the gas check. -/
theorem step_observation_full (s : State) (o : Observation)
    (h : At s (some o.opcode)) (gas : 2 ≤ s.gas) (full : s.stack.val.length = 1024) :
    step s = .exception s .stackOverflow := by
  obtain ⟨bounds, decoded⟩ := h
  have push (w : Word) : s.stack.push w = .error .overflow :=
    (Proofs.Stack.push_overflow_iff _ _).mpr full
  cases o <;> simp_all [Observation.opcode, step, blobBaseFee, observe, charge, Gas.charge, failStack]

/-- An observation pushes its value and advances once. -/
theorem step_observation (s t : State) (o : Observation)
    (h : At s (some o.opcode)) (gas : 2 ≤ s.gas) (room : s.stack.val.length < 1024)
    (fields : Advances s t (s.pc + 1) (s.gas - 2)
      (BitVec.ofNat 256 (o.value s) :: s.stack.val)) : step s = .continue t := by
  let stack : Stack := ⟨BitVec.ofNat 256 (o.value s) :: s.stack.val, by simp; omega⟩
  have push : s.stack.push (BitVec.ofNat 256 (o.value s)) = .ok stack :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨room, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 2) stack fields
  obtain ⟨bounds, decoded⟩ := h
  cases o <;> simp_all [Observation.opcode, Observation.value, step, blobBaseFee, observe, charge,
    Gas.charge, observationWord]

/-- A successful observation puts the observed word on the resulting stack. -/
theorem step_observation_stack (s t : State) (o : Observation)
    (h : At s (some o.opcode)) (run : step s = .continue t) :
    t.stack.val = observationWord (o.value s) :: s.stack.val := by
  -- A continuing step cannot be the out-of-gas case.
  have gas : 2 ≤ s.gas := by
    by_cases hg : 2 ≤ s.gas
    · exact hg
    have bad := step_observation_gas s o h (by omega)
    rw [run] at bad
    cases bad
  -- The stack bound makes lack of room exactly the overflow case.
  have room : s.stack.val.length < 1024 := by
    by_cases hr : s.stack.val.length < 1024
    · exact hr
    have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
    have bad := step_observation_full s o h gas full
    rw [run] at bad
    cases bad
  -- Build the unique successful target and compare the two outcomes.
  let st : Stack := ⟨observationWord (o.value s) :: s.stack.val, by simp; omega⟩
  let target : State := { s with stack := st, pc := s.pc + 1, gas := s.gas - 2 }
  have fields : Advances s target (s.pc + 1) (s.gas - 2)
      (BitVec.ofNat 256 (o.value s) :: s.stack.val) := by
    simp [Advances, target, st, observationWord]
  have ok := step_observation s target o h gas room fields
  rw [run] at ok
  have eq : t = target := Outcome.continue.inj ok
  rw [eq]

/-- A successful observation determines the complete resulting frame. -/
theorem step_observation_actual (s t : State) (o : Observation)
    (at_ : At s (some o.opcode)) (run : step s = .continue t) :
    2 ≤ s.gas ∧ s.stack.val.length < 1024 ∧
      Advances s t (s.pc + 1) (s.gas - 2)
        (observationWord (o.value s) :: s.stack.val) := by
  have gas : 2 ≤ s.gas := by
    by_cases h : 2 ≤ s.gas
    · exact h
    have bad := step_observation_gas s o at_ (by omega)
    rw [run] at bad
    cases bad
  have room : s.stack.val.length < 1024 := by
    by_cases h : s.stack.val.length < 1024
    · exact h
    have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
    have bad := step_observation_full s o at_ gas full
    rw [run] at bad
    cases bad
  let stack : Stack := ⟨observationWord (o.value s) :: s.stack.val, by simp; omega⟩
  let target : State := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
  have fields : Advances s target (s.pc + 1) (s.gas - 2)
      (observationWord (o.value s) :: s.stack.val) := by simp [Advances, target, stack]
  have ok := step_observation s target o at_ gas room (by simpa [observationWord] using fields)
  rw [run] at ok
  have eq : t = target := Outcome.continue.inj ok
  exact ⟨gas, room, eq ▸ fields⟩

/-- The resulting stack head is the observation modulo the word modulus. -/
theorem step_observation_stack_mod (s t : State) (o : Observation)
    (h : At s (some o.opcode)) (run : step s = .continue t) :
    ∃ w, t.stack.val = w :: s.stack.val ∧ w.toNat = o.value s % Word.modulus := by
  exact ⟨observationWord (o.value s), step_observation_stack s t o h run, observationWord_toNat _⟩

/-- In the source U256 domain, the resulting stack head is exact. -/
theorem step_observation_stack_exact (s t : State) (o : Observation)
    (h : At s (some o.opcode)) (run : step s = .continue t)
    (bound : o.value s < Word.modulus) :
    ∃ w, t.stack.val = w :: s.stack.val ∧ w.toNat = o.value s := by
  exact ⟨observationWord (o.value s), step_observation_stack s t o h run, observationWord_exact _ bound⟩

/-- An assigned opcode outside this slice yields the tooling result. -/
theorem step_unsupported (s : State) (op : Opcode) (h : At s (some op))
    (unsupported : Unsupported op) : step s = .unsupported s op := by
  obtain ⟨bounds, decoded⟩ := h
  cases op <;> simp_all [Unsupported, step]

/-- Fields determine a memory-effect frame up to proof irrelevance. -/
theorem advancesMemory_eq (s t : State) (memory : Memory.Allocation.State)
    (valid : Memory.Allocation.Valid memory) (pc gas : Nat) (stack : Stack)
    (h : AdvancesMemory s t memory pc gas stack.val) :
    t = { s with memory, memoryValid := valid, pc, gas, stack } := by
  rcases h with ⟨code, mem, pcEq, gasEq, stackEq, contextEq⟩
  have stackEq' : t.stack = stack := Subtype.ext stackEq
  cases s
  cases t
  simp_all

/-- MLOAD checks the stack before gas. -/
theorem step_mload_empty (s : State) (h : At s (some .mload))
    (empty : s.stack.val = []) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr empty
  simp [step, bounds, decoded, pop, failStack]

/-- MLOAD charges the full expansion cost. -/
theorem step_mload_gas (s : State) (x : Word) (xs : List Word)
    (h : At s (some .mload)) (items : s.stack.val = x :: xs)
    (gas : s.gas < 3 + Gas.rangeCost s.memory.words x.toNat 32) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let stack : Stack := ⟨xs, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
  have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  simp [step, bounds, decoded, pop, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful MLOAD reads the selected word and expands memory. -/
theorem step_mload (s t : State) (x : Word) (xs : List Word)
    (h : At s (some .mload)) (items : s.stack.val = x :: xs)
    (gas : 3 + Gas.rangeCost s.memory.words x.toNat 32 ≤ s.gas)
    (fields : AdvancesMemory s t (Memory.Allocation.loadWord s.memory x.toNat).2
      (s.pc + 1) (s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 32))
      ((Memory.Allocation.loadWord s.memory x.toNat).1 :: xs)) : step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let stack : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  let final : Stack := ⟨(Memory.Allocation.loadWord s.memory x.toNat).1 :: xs,
    by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have push : stack.push (Memory.Allocation.loadWord s.memory x.toNat).1 = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advancesMemory_eq s t _ (Memory.Allocation.expand_valid_for_frame _ _ _ s.memoryValid)
    (s.pc + 1) (s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 32)) final fields
  simp only [step, dite_eq_left bounds, decoded, pop, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]
  rfl

/-- MSTORE checks both operands before gas. -/
theorem step_mstore_empty (s : State) (h : At s (some .mstore))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- MSTORE fails when gas cannot cover expansion. -/
theorem step_mstore_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .mstore)) (items : s.stack.val = x :: y :: xs)
    (gas : s.gas < 3 + Gas.rangeCost s.memory.words x.toNat 32) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let second : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- Successful MSTORE stores the value and expands memory. -/
theorem step_mstore (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .mstore)) (items : s.stack.val = x :: y :: xs)
    (gas : 3 + Gas.rangeCost s.memory.words x.toNat 32 ≤ s.gas)
    (fields : AdvancesMemory s t (Memory.Allocation.storeWord s.memory x.toNat y)
      (s.pc + 1) (s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 32)) xs) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let second : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have update := advancesMemory_eq s t _ (Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid)
    (s.pc + 1) (s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 32)) second fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas]
  rw [update]
  rfl

/-- MSTORE8 checks both operands before gas. -/
theorem step_mstore8_empty (s : State) (h : At s (some .mstore8))
    (short : s.stack.val.length < 2) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, pop, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let stack : Stack := Stack.empty
      have pop : s.stack.pop = .ok (x, stack) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have pop2 : stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, pop, pop2, failStack]
    | cons y ys => simp [items] at short; omega

/-- MSTORE8 fails when gas cannot cover expansion. -/
theorem step_mstore8_gas (s : State) (x y : Word) (xs : List Word)
    (h : At s (some .mstore8)) (items : s.stack.val = x :: y :: xs)
    (gas : s.gas < 3 + Gas.rangeCost s.memory.words x.toNat 1) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let second : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, charge, Gas.charge, Nat.not_le.mpr gas]

/-- Successful MSTORE8 stores the value and expands memory. -/
theorem step_mstore8 (s t : State) (x y : Word) (xs : List Word)
    (h : At s (some .mstore8)) (items : s.stack.val = x :: y :: xs)
    (gas : 3 + Gas.rangeCost s.memory.words x.toNat 1 ≤ s.gas)
    (fields : AdvancesMemory s t (Memory.Allocation.storeByte s.memory x.toNat y)
      (s.pc + 1) (s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 1)) xs) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let second : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have update := advancesMemory_eq s t _ (Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid)
    (s.pc + 1) (s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 1)) second fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, charge, Gas.charge, ite_eq_left gas]
  rw [update]
  rfl

/-- MCOPY checks all operands before charging gas. -/
theorem step_mcopy_empty (s : State) (h : At s (some .mcopy))
    (short : s.stack.val.length < 3) : step s = .exception s .stackUnderflow := by
  obtain ⟨bounds, decoded⟩ := h
  cases items : s.stack.val with
  | nil =>
    have p : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [step, bounds, decoded, p, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let first : Stack := Stack.empty
      have p : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have q : first.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [step, bounds, decoded, p, q, failStack]
    | cons y ys =>
      cases ys with
      | nil =>
        let first : Stack := ⟨[y], by simp⟩
        let second : Stack := Stack.empty
        have p : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
        have q : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
        have r : second.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
        simp [step, bounds, decoded, p, q, r, failStack]
      | cons z zs => simp [items] at short; omega

/-- MCOPY fails before copying when its gas is insufficient. -/
theorem step_mcopy_gas (s : State) (x y z : Word) (xs : List Word)
    (h : At s (some .mcopy)) (items : s.stack.val = x :: y :: z :: xs)
    (gas : s.gas < Gas.mcopyCost s.memory.words x.toNat y.toNat z.toNat) :
    step s = .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: z :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let second : Stack := ⟨z :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let third : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have p3 : second.pop = .ok (z, third) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [step, bounds, decoded, p1, p2, p3, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful MCOPY uses the input memory snapshot. -/
theorem step_mcopy (s t : State) (x y z : Word) (xs : List Word)
    (h : At s (some .mcopy)) (items : s.stack.val = x :: y :: z :: xs)
    (gas : Gas.mcopyCost s.memory.words x.toNat y.toNat z.toNat ≤ s.gas)
    (fields : AdvancesMemory s t (Memory.Allocation.copy s.memory x.toNat y.toNat z.toNat)
      (s.pc + 1) (s.gas - Gas.mcopyCost s.memory.words x.toNat y.toNat z.toNat) xs) :
    step s = .continue t := by
  obtain ⟨bounds, decoded⟩ := h
  let first : Stack := ⟨y :: z :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let second : Stack := ⟨z :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let third : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have p3 : second.pop = .ok (z, third) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have update := advancesMemory_eq s t _ (Memory.Allocation.copy_valid_for_frame _ _ _ _ s.memoryValid)
    (s.pc + 1) (s.gas - Gas.mcopyCost s.memory.words x.toNat y.toNat z.toNat) third fields
  simp only [step, dite_eq_left bounds, decoded, p1, p2, p3, charge, Gas.charge, ite_eq_left gas]
  rw [update]

/-- Return-data copying checks all operands before charging gas. -/
theorem returnDataCopy_helper_empty (s : State)
    (short : s.stack.val.length < 3) : returnDataCopy s = .exception s .stackUnderflow := by
  cases items : s.stack.val with
  | nil =>
    have p : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [returnDataCopy, p, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let first : Stack := Stack.empty
      have p : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have q : first.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [returnDataCopy, p, q, failStack]
    | cons y ys =>
      cases ys with
      | nil =>
        let first : Stack := ⟨[y], by simp⟩
        let second : Stack := Stack.empty
        have p : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
        have q : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
        have r : second.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
        simp [returnDataCopy, p, q, r, failStack]
      | cons z zs => simp [items] at short; omega

/-- Return-data copying fails before reading when gas is insufficient. -/
theorem returnDataCopy_helper_gas (s : State) (x y z : Word) (xs : List Word)
    (items : s.stack.val = x :: y :: z :: xs)
    (gas : s.gas < Gas.inputCopyCost s.memory.words x.toNat z.toNat) :
    returnDataCopy s = .exception s .outOfGas := by
  let first : Stack := ⟨y :: z :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let second : Stack := ⟨z :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let third : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have p3 : second.pop = .ok (z, third) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [returnDataCopy, p1, p2, p3, charge, Gas.charge, Nat.not_le.mpr gas]


/-- Dispatch selects the corresponding immutable source. -/
theorem step_inputCopy_dispatch (s : State) (source : InputSource)
    (h : At s (some source.opcode)) : step s = inputCopy s (source.bytes s) := by
  obtain ⟨bounds, decoded⟩ := h
  cases source <;> simp_all [InputSource.opcode, InputSource.bytes, step]

/-- Input copying checks all operands before charging gas. -/
theorem inputCopy_helper_empty (s : State) (data : ByteArray)
    (short : s.stack.val.length < 3) : inputCopy s data = .exception s .stackUnderflow := by
  cases items : s.stack.val with
  | nil =>
    have p : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [inputCopy, p, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let first : Stack := Stack.empty
      have p : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have q : first.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [inputCopy, p, q, failStack]
    | cons y ys =>
      cases ys with
      | nil =>
        let first : Stack := ⟨[y], by simp⟩
        let second : Stack := Stack.empty
        have p : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
        have q : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
        have r : second.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
        simp [inputCopy, p, q, r, failStack]
      | cons z zs => simp [items] at short; omega

/-- Input copying fails before copying when its gas is insufficient. -/
theorem inputCopy_helper_gas (s : State) (data : ByteArray) (x y z : Word) (xs : List Word)
    (items : s.stack.val = x :: y :: z :: xs)
    (gas : s.gas < Gas.inputCopyCost s.memory.words x.toNat z.toNat) :
    inputCopy s data = .exception s .outOfGas := by
  let first : Stack := ⟨y :: z :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let second : Stack := ⟨z :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let third : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have p3 : second.pop = .ok (z, third) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp [inputCopy, p1, p2, p3, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful helper call copies from the supplied immutable bytes. -/
theorem inputCopy_helper_success (s t : State) (data : ByteArray) (x y z : Word) (xs : List Word)
    (items : s.stack.val = x :: y :: z :: xs)
    (gas : Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas)
    (fields : AdvancesMemory s t (Memory.Allocation.write s.memory x.toNat (CallData.readRange data y.toNat z.toNat))
      (s.pc + 1) (s.gas - Gas.inputCopyCost s.memory.words x.toNat z.toNat) xs) :
    inputCopy s data = .continue t := by
  let first : Stack := ⟨y :: z :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let second : Stack := ⟨z :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let third : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have p3 : second.pop = .ok (z, third) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have update := advancesMemory_eq s t _ (Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid)
    (s.pc + 1) (s.gas - Gas.inputCopyCost s.memory.words x.toNat z.toNat) third fields
  simp only [inputCopy, p1, p2, p3, charge, Gas.charge, ite_eq_left gas]
  rw [update]

/-- Input copying checks all operands before charging gas. -/
theorem step_inputCopy_empty (s : State) (source : InputSource) (h : At s (some source.opcode))
    (short : s.stack.val.length < 3) : step s = .exception s .stackUnderflow := by
  rw [step_inputCopy_dispatch s source h]
  exact inputCopy_helper_empty s (source.bytes s) short

/-- Input copying fails before copying when its gas is insufficient. -/
theorem step_inputCopy_gas (s : State) (source : InputSource) (x y z : Word) (xs : List Word)
    (h : At s (some source.opcode)) (items : s.stack.val = x :: y :: z :: xs)
    (gas : s.gas < Gas.inputCopyCost s.memory.words x.toNat z.toNat) :
    step s = .exception s .outOfGas := by
  rw [step_inputCopy_dispatch s source h]
  exact inputCopy_helper_gas s (source.bytes s) x y z xs items gas

/-- A successful input-copy instruction reads its immutable source. -/
theorem step_inputCopy (s t : State) (source : InputSource) (x y z : Word) (xs : List Word)
    (h : At s (some source.opcode)) (items : s.stack.val = x :: y :: z :: xs)
    (gas : Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas)
    (fields : AdvancesMemory s t (Memory.Allocation.write s.memory x.toNat (CallData.readRange (source.bytes s) y.toNat z.toNat))
      (s.pc + 1) (s.gas - Gas.inputCopyCost s.memory.words x.toNat z.toNat) xs) :
    step s = .continue t := by
  rw [step_inputCopy_dispatch s source h]
  exact inputCopy_helper_success s t (source.bytes s) x y z xs items gas fields

/-- The checked return-data copy follows its operand, gas and bounds checks. -/
theorem returnDataCopy_helper_result (s : State) (x y z : Word) (xs : List Word)
    (items : s.stack.val = x :: y :: z :: xs) :
    returnDataCopy s =
      if Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas then
        if y.toNat + z.toNat ≤ s.returnData.size then
          .continue { s with stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩, pc := s.pc + 1, gas := s.gas - Gas.inputCopyCost s.memory.words x.toNat z.toNat, memory := Memory.Allocation.write s.memory x.toNat ((s.returnData.data.toList.drop y.toNat).take z.toNat), memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid }
        else .exception s .outOfBoundsRead
      else .exception s .outOfGas := by
  let first : Stack := ⟨y :: z :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let second : Stack := ⟨z :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let third : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, second) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have p3 : second.pop = .ok (z, third) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  simp only [returnDataCopy, p1, p2, p3, charge, Gas.charge, ReturnData.read]
  by_cases hg : Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas <;> by_cases hb : y.toNat + z.toNat ≤ s.returnData.size <;> simp [hg, hb, third]

/-- A charged copy rejects an out-of-bounds source range. -/
theorem returnDataCopy_helper_bounds (s : State) (x y z : Word) (xs : List Word)
    (items : s.stack.val = x :: y :: z :: xs)
    (gas : Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas)
    (bounds : s.returnData.size < y.toNat + z.toNat) :
    returnDataCopy s = .exception s .outOfBoundsRead := by
  rw [returnDataCopy_helper_result s x y z xs items]
  simp [gas, Nat.not_le.mpr bounds]

/-- A valid and affordable copy produces exactly the stated frame fields. -/
theorem returnDataCopy_helper_success (s t : State) (x y z : Word) (xs : List Word)
    (items : s.stack.val = x :: y :: z :: xs)
    (gas : Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas)
    (bounds : y.toNat + z.toNat ≤ s.returnData.size)
    (fields : AdvancesMemory s t (Memory.Allocation.write s.memory x.toNat
      ((s.returnData.data.toList.drop y.toNat).take z.toNat))
      (s.pc + 1) (s.gas - Gas.inputCopyCost s.memory.words x.toNat z.toNat) xs) :
    returnDataCopy s = .continue t := by
  rw [returnDataCopy_helper_result s x y z xs items]
  simp only [ite_eq_left gas, ite_eq_left bounds]
  have update := advancesMemory_eq s t _ (Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid)
    (s.pc + 1) (s.gas - Gas.inputCopyCost s.memory.words x.toNat z.toNat)
    ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩ fields
  rw [update]

/-- A continuing helper call determines affordability, bounds and every frame field. -/
theorem returnDataCopy_helper_actual (s t : State) (x y z : Word) (xs : List Word)
    (items : s.stack.val = x :: y :: z :: xs) (run : returnDataCopy s = .continue t) :
    Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas ∧
    y.toNat + z.toNat ≤ s.returnData.size ∧
    AdvancesMemory s t (Memory.Allocation.write s.memory x.toNat
      ((s.returnData.data.toList.drop y.toNat).take z.toNat))
      (s.pc + 1) (s.gas - Gas.inputCopyCost s.memory.words x.toNat z.toNat) xs := by
  rw [returnDataCopy_helper_result s x y z xs items] at run
  by_cases gas : Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas
  · by_cases bounds : y.toNat + z.toNat ≤ s.returnData.size
    · simp only [ite_eq_left gas, ite_eq_left bounds] at run
      cases run
      exact ⟨gas, bounds, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp [gas, bounds] at run
  · simp [gas] at run

/-- Complete source-oriented outcomes of the public return-data copy helper. -/
inductive ReturnDataCopyRule : State → Outcome → Prop where
  | underflow (s) : s.stack.val.length < 3 → ReturnDataCopyRule s (.exception s .stackUnderflow)
  | gas (s x y z xs) : s.stack.val = x :: y :: z :: xs →
      s.gas < Gas.inputCopyCost s.memory.words x.toNat z.toNat →
      ReturnDataCopyRule s (.exception s .outOfGas)
  | bounds (s x y z xs) : s.stack.val = x :: y :: z :: xs →
      Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas →
      s.returnData.size < y.toNat + z.toNat → ReturnDataCopyRule s (.exception s .outOfBoundsRead)
  | success (s t x y z xs) : s.stack.val = x :: y :: z :: xs →
      Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas →
      y.toNat + z.toNat ≤ s.returnData.size →
      AdvancesMemory s t (Memory.Allocation.write s.memory x.toNat
        ((s.returnData.data.toList.drop y.toNat).take z.toNat))
        (s.pc + 1) (s.gas - Gas.inputCopyCost s.memory.words x.toNat z.toNat) xs →
      ReturnDataCopyRule s (.continue t)

/-- Every helper rule is executed by the public helper. -/
theorem returnDataCopy_helper_rule_sound {s : State} {out : Outcome}
    (rule : ReturnDataCopyRule s out) : returnDataCopy s = out := by
  cases rule with
  | underflow short => exact returnDataCopy_helper_empty _ short
  | gas x y z xs items gas => exact returnDataCopy_helper_gas _ x y z xs items gas
  | bounds x y z xs items gas bounds => exact returnDataCopy_helper_bounds _ x y z xs items gas bounds
  | success t x y z xs items gas bounds fields =>
    exact returnDataCopy_helper_success _ t x y z xs items gas bounds fields

/-- Every input frame has one of the helper's four outcomes. -/
theorem returnDataCopy_helper_rule_total (s : State) : ∃ out, ReturnDataCopyRule s out := by
  cases items : s.stack.val with
  | nil => exact ⟨_, .underflow s (by simp [items])⟩
  | cons x ys =>
    cases ys with
    | nil => exact ⟨_, .underflow s (by simp [items])⟩
    | cons y zs =>
      cases zs with
      | nil => exact ⟨_, .underflow s (by simp [items])⟩
      | cons z xs =>
        by_cases gas : Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas
        · by_cases bounds : y.toNat + z.toNat ≤ s.returnData.size
          · let stack : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
            let t : State := { s with stack, pc := s.pc + 1, gas := s.gas - Gas.inputCopyCost s.memory.words x.toNat z.toNat, memory := Memory.Allocation.write s.memory x.toNat ((s.returnData.data.toList.drop y.toNat).take z.toNat), memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid }
            exact ⟨_, .success s t x y z xs items gas bounds (by simp [AdvancesMemory, t, stack])⟩
          · exact ⟨_, .bounds s x y z xs items gas (Nat.lt_of_not_ge bounds)⟩
        · exact ⟨_, .gas s x y z xs items (Nat.lt_of_not_ge gas)⟩

/-- The helper executes exactly the four rules, for every input frame and outcome. -/
theorem returnDataCopy_helper_iff_rule (s : State) (out : Outcome) :
    returnDataCopy s = out ↔ ReturnDataCopyRule s out := by
  constructor
  · intro run
    obtain ⟨result, rule⟩ := returnDataCopy_helper_rule_total s
    have same := returnDataCopy_helper_rule_sound rule
    rw [run] at same
    cases same
    exact rule
  · exact returnDataCopy_helper_rule_sound

/-- Every helper bounds exception comes from an affordable, out-of-bounds copy. -/
theorem returnDataCopy_helper_bounds_actual {s input : State}
    (run : returnDataCopy s = .exception input .outOfBoundsRead) :
    input = s ∧ ∃ x y z xs, s.stack.val = x :: y :: z :: xs ∧
      Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas ∧
      s.returnData.size < y.toNat + z.toNat := by
  have rule := (returnDataCopy_helper_iff_rule s _).mp run
  cases rule with
  | bounds x y z xs items gas bounds => exact ⟨rfl, x, y, z, xs, items, gas, bounds⟩

/-- The checked return-data copy follows its operand, gas and bounds checks. -/
theorem step_returnDataCopy (s : State) (x y z : Word) (xs : List Word)
    (at_ : At s (some .returndatacopy)) (items : s.stack.val = x :: y :: z :: xs) :
    step s =
      if Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas then
        if y.toNat + z.toNat ≤ s.returnData.size then
          .continue { s with stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩, pc := s.pc + 1, gas := s.gas - Gas.inputCopyCost s.memory.words x.toNat z.toNat, memory := Memory.Allocation.write s.memory x.toNat ((s.returnData.data.toList.drop y.toNat).take z.toNat), memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid }
        else .exception s .outOfBoundsRead
      else .exception s .outOfGas := by
  obtain ⟨bounds, decoded⟩ := at_
  simp only [step, dite_eq_left bounds, decoded]
  exact returnDataCopy_helper_result s x y z xs items

/-- Two operands leave room for the digest on the bounded stack. -/
theorem keccak_helper_result (s : State) (x y : Word) (xs : List Word)
    (items : s.stack.val = x :: y :: xs) :
    keccak s =
      if Gas.keccakCost s.memory.words x.toNat y.toNat ≤ s.gas then
        .continue { s with
          stack := ⟨digestWord (EthLib.Cryptography.Hash.Keccak.keccak256
            ⟨(Memory.readRange s.memory.store x.toNat y.toNat).toArray⟩) :: xs,
              by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
          pc := s.pc + 1
          gas := s.gas - Gas.keccakCost s.memory.words x.toNat y.toNat
          memory := Memory.Allocation.expand s.memory x.toNat y.toNat
          memoryValid := Memory.Allocation.expand_valid_for_frame _ _ _ s.memoryValid }
      else .exception s .outOfGas := by
  let first : Stack := ⟨y :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let rest : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  let digest := digestWord (EthLib.Cryptography.Hash.Keccak.keccak256
    ⟨(Memory.readRange s.memory.store x.toNat y.toNat).toArray⟩)
  let pushed : Stack := ⟨digest :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  have p1 : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have p2 : first.pop = .ok (y, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr rfl
  have push : rest.push digest = .ok pushed :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  dsimp [digest] at push
  by_cases gas : Gas.keccakCost s.memory.words x.toNat y.toNat ≤ s.gas <;>
    simp [keccak, p1, p2, charge, Gas.charge, gas, push, pushed, digest]

/-- Missing operands are detected before gas is charged. -/
theorem keccak_helper_empty (s : State) (short : s.stack.val.length < 2) :
    keccak s = .exception s .stackUnderflow := by
  cases items : s.stack.val with
  | nil =>
    have p : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr items
    simp [keccak, p, failStack]
  | cons x xs =>
    cases xs with
    | nil =>
      let first : Stack := Stack.empty
      have p : s.stack.pop = .ok (x, first) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
      have q : first.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr rfl
      simp [keccak, p, q, failStack]
    | cons y ys => simp [items] at short; omega

/-- The successful helper result determines every frame field from the input. -/
theorem keccak_helper_actual (s t : State) (x y : Word) (xs : List Word)
    (items : s.stack.val = x :: y :: xs) (run : keccak s = .continue t) :
    Gas.keccakCost s.memory.words x.toNat y.toNat ≤ s.gas ∧
    AdvancesMemory s t (Memory.Allocation.expand s.memory x.toNat y.toNat)
      (s.pc + 1) (s.gas - Gas.keccakCost s.memory.words x.toNat y.toNat)
      (digestWord (EthLib.Cryptography.Hash.Keccak.keccak256
        ⟨(Memory.readRange s.memory.store x.toNat y.toNat).toArray⟩) :: xs) := by
  rw [keccak_helper_result s x y xs items] at run
  by_cases gas : Gas.keccakCost s.memory.words x.toNat y.toNat ≤ s.gas
  · simp only [ite_eq_left gas, Outcome.continue.injEq] at run
    subst t
    exact ⟨gas, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp [gas] at run

/-- Expansion performed by a successful hash preserves every raw store byte. -/
theorem keccak_helper_store (s t : State) (x y : Word) (xs : List Word)
    (items : s.stack.val = x :: y :: xs) (run : keccak s = .continue t) :
    t.memory.store = s.memory.store := by
  have fields := (keccak_helper_actual s t x y xs items run).2
  rw [fields.2.1]
  rfl

/-- Every relational rule is accepted by the executable step. -/
theorem blockHashValue_iff (history : List Word) (current index value : Word) :
    BlockHashValue history current index value ↔
      value = Environment.blockHash history current index := by
  by_cases window : index.toNat < current.toNat ∧ current.toNat ≤ index.toNat + 256
  · by_cases available : current.toNat - index.toNat ≤ history.length
    · have bound : history.length - (current.toNat - index.toNat) < history.length := by omega
      simp [BlockHashValue, Environment.blockHash, window, available, bound]
      omega
    · have missing : history.length < current.toNat - index.toNat := by omega
      simp [BlockHashValue, Environment.blockHash, window, available, missing]
  · have outside : current.toNat ≤ index.toNat ∨ index.toNat + 256 < current.toNat := by omega
    simp only [BlockHashValue, Environment.blockHash, ite_eq_right window]
    constructor
    · intro h
      rcases h with h | h
      · exact False.elim (window ⟨h.1, h.2.1⟩)
      · exact h.2
    · intro h
      exact Or.inr ⟨outside.elim Or.inl (fun h => Or.inr (Or.inl h)), h⟩

theorem rule_sound {s : State} {out : Outcome} (h : Rule s out) : step s = out := by
  cases h with
  | endCode end_ => exact step_end _ end_
  | stop at_ => exact step_stop _ at_
  | invalid at_ => rcases at_ with h | h; exact step_unassigned _ h; exact step_invalid _ h
  | unsupported op at_ unsupported => exact step_unsupported _ op at_ unsupported
  | keccakEmpty at_ empty =>
    obtain ⟨bounds, decoded⟩ := at_
    simp only [step, dite_eq_left bounds, decoded]
    exact keccak_helper_empty _ empty
  | keccakGas x y xs at_ items gas =>
    obtain ⟨bounds, decoded⟩ := at_
    simp only [step, dite_eq_left bounds, decoded]
    rw [keccak_helper_result _ x y xs items]
    simp [Nat.not_le.mpr gas]
  | keccak t x y xs at_ items gas fields =>
    obtain ⟨bounds, decoded⟩ := at_
    simp only [step, dite_eq_left bounds, decoded]
    rw [keccak_helper_result _ x y xs items]
    simp only [ite_eq_left gas]
    apply congrArg Outcome.continue
    symm
    apply advancesMemory_eq
    exact fields
  | calldataloadEmpty at_ empty => exact step_calldataload_empty _ at_ empty
  | calldataloadGas x xs at_ items gas => exact step_calldataload_gas _ x xs at_ items gas
  | calldataload t x xs at_ items gas fields => exact step_calldataload _ t x xs at_ items gas fields
  | blockhashEmpty at_ empty => exact step_blockhash_empty _ at_ empty
  | blockhashGas x xs at_ items gas => exact step_blockhash_gas _ x xs at_ items gas
  | blockhash t x xs value at_ items gas lookup fields =>
    have eq := (blockHashValue_iff _ _ _ _).mp lookup
    subst value
    exact step_blockhash _ t x xs at_ items gas fields
  | blobhashEmpty at_ empty => exact step_blobhash_empty _ at_ empty
  | blobhashGas x xs at_ items gas => exact step_blobhash_gas _ x xs at_ items gas
  | blobhash t x xs at_ items gas fields => exact step_blobhash _ t x xs at_ items gas fields
  | returnDataCopyEmpty at_ empty =>
    obtain ⟨bounds, decoded⟩ := at_
    simp only [step, dite_eq_left bounds, decoded]
    exact returnDataCopy_helper_empty _ empty
  | returnDataCopyGas x y z xs at_ items gas =>
    rw [step_returnDataCopy _ x y z xs at_ items]
    simp [Nat.not_le.mpr gas]
  | returnDataCopyBounds x y z xs at_ items gas bounds =>
    rw [step_returnDataCopy _ x y z xs at_ items]
    simp [gas, Nat.not_le.mpr bounds]
  | returnDataCopy t x y z xs at_ items gas bounds fields =>
    rw [step_returnDataCopy _ x y z xs at_ items]
    simp only [ite_eq_left gas, ite_eq_left bounds]
    have update := advancesMemory_eq _ t _ (Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid)
      (s.pc + 1) (s.gas - Gas.inputCopyCost s.memory.words x.toNat z.toNat)
      ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩ fields
    rw [update]
  | inputCopyEmpty source at_ empty => exact step_inputCopy_empty _ source at_ empty
  | inputCopyGas source x y z xs at_ items gas => exact step_inputCopy_gas _ source x y z xs at_ items gas
  | inputCopy t source x y z xs at_ items gas fields => exact step_inputCopy _ t source x y z xs at_ items gas fields
  | mcopyEmpty at_ empty => exact step_mcopy_empty _ at_ empty
  | mcopyGas x y z xs at_ items gas => exact step_mcopy_gas _ x y z xs at_ items gas
  | mcopy t x y z xs at_ items gas fields => exact step_mcopy _ t x y z xs at_ items gas fields
  | mloadEmpty at_ empty => exact step_mload_empty _ at_ empty
  | mloadGas x xs at_ items gas => exact step_mload_gas _ x xs at_ items gas
  | mload t x xs at_ items gas fields => exact step_mload _ t x xs at_ items gas fields
  | mstoreEmpty at_ empty => exact step_mstore_empty _ at_ empty
  | mstoreGas x y xs at_ items gas => exact step_mstore_gas _ x y xs at_ items gas
  | mstore t x y xs at_ items gas fields => exact step_mstore _ t x y xs at_ items gas fields
  | mstore8Empty at_ empty => exact step_mstore8_empty _ at_ empty
  | mstore8Gas x y xs at_ items gas => exact step_mstore8_gas _ x y xs at_ items gas
  | mstore8 t x y xs at_ items gas fields => exact step_mstore8 _ t x y xs at_ items gas fields
  | jumpEmpty at_ empty => exact step_jump_empty _ at_ empty
  | jumpGas x xs at_ items gas => exact step_jump_gas _ x xs at_ items gas
  | jumpInvalid x xs at_ items gas invalid => exact step_jump_invalid _ x xs at_ items gas invalid
  | jump t x xs at_ items gas valid fields => exact step_jump _ t x xs at_ items gas valid fields
  | jumpiEmpty at_ empty => exact step_jumpi_empty _ at_ empty
  | jumpiGas x y xs at_ items gas => exact step_jumpi_gas _ x y xs at_ items gas
  | jumpiInvalid x y xs at_ items gas cond invalid => exact step_jumpi_invalid _ x y xs at_ items gas cond invalid
  | jumpiFalse t x y xs at_ items gas cond fields => exact step_jumpi_false _ t x y xs at_ items gas cond fields
  | jumpiTrue t x y xs at_ items gas cond valid fields => exact step_jumpi_true _ t x y xs at_ items gas cond valid fields
  | jumpdestGas at_ gas => exact step_jumpdest_gas _ at_ gas
  | jumpdest t at_ gas fields => exact step_jumpdest _ t at_ gas fields
  | observationGas o at_ gas => exact step_observation_gas _ o at_ gas
  | observationFull o at_ gas full => exact step_observation_full _ o at_ gas full
  | observation t o at_ gas room fields => exact step_observation _ t o at_ gas room fields
  | pushGas n at_ gas => exact step_push_gas _ n at_ gas
  | pushFull n at_ gas full => exact step_push_full _ n at_ gas full
  | push t n at_ gas room fields => exact step_push _ t n at_ gas room fields
  | popEmpty at_ empty => exact step_pop_empty _ at_ empty
  | popGas x xs at_ items gas => exact step_pop_gas _ x xs at_ items gas
  | pop t x xs at_ items gas fields => exact step_pop _ t x xs at_ items gas fields
  | addEmpty at_ short => exact step_add_empty _ at_ short
  | addGas x y xs at_ items gas => exact step_add_gas _ x y xs at_ items gas
  | add t x y xs at_ items gas fields => exact step_add _ t x y xs at_ items gas fields
  | addmodEmpty at_ short => exact step_addmod_empty _ at_ short
  | addmodGas x y m xs at_ items gas => exact step_addmod_gas _ x y m xs at_ items gas
  | addmod t x y m xs at_ items gas fields => exact step_addmod _ t x y m xs at_ items gas fields
  | mulmodEmpty at_ short => exact step_mulmod_empty _ at_ short
  | mulmodGas x y m xs at_ items gas => exact step_mulmod_gas _ x y m xs at_ items gas
  | mulmod t x y m xs at_ items gas fields => exact step_mulmod _ t x y m xs at_ items gas fields
  | expEmpty at_ short => exact step_exp_empty _ at_ short
  | expGas x y xs at_ items gas => exact step_exp_gas _ x y xs at_ items gas
  | exp t x y xs at_ items gas fields => exact step_exp _ t x y xs at_ items gas fields
  | mulEmpty at_ short => exact step_mul_empty _ at_ short
  | mulGas x y xs at_ items gas => exact step_mul_gas _ x y xs at_ items gas
  | mul t x y xs at_ items gas fields => exact step_mul _ t x y xs at_ items gas fields
  | subEmpty at_ short => exact step_sub_empty _ at_ short
  | subGas x y xs at_ items gas => exact step_sub_gas _ x y xs at_ items gas
  | sub t x y xs at_ items gas fields => exact step_sub _ t x y xs at_ items gas fields
  | divEmpty at_ short => exact step_div_empty _ at_ short
  | divGas x y xs at_ items gas => exact step_div_gas _ x y xs at_ items gas
  | div t x y xs at_ items gas fields => exact step_div _ t x y xs at_ items gas fields
  | modEmpty at_ short => exact step_mod_empty _ at_ short
  | modGas x y xs at_ items gas => exact step_mod_gas _ x y xs at_ items gas
  | mod t x y xs at_ items gas fields => exact step_mod _ t x y xs at_ items gas fields
  | sdivEmpty at_ short => exact step_sdiv_empty _ at_ short
  | sdivGas x y xs at_ items gas => exact step_sdiv_gas _ x y xs at_ items gas
  | sdiv t x y xs at_ items gas fields => exact step_sdiv _ t x y xs at_ items gas fields
  | smodEmpty at_ short => exact step_smod_empty _ at_ short
  | smodGas x y xs at_ items gas => exact step_smod_gas _ x y xs at_ items gas
  | smod t x y xs at_ items gas fields => exact step_smod _ t x y xs at_ items gas fields
  | ltEmpty at_ short => exact step_lt_empty _ at_ short
  | ltGas x y xs at_ items gas => exact step_lt_gas _ x y xs at_ items gas
  | lt t x y xs at_ items gas fields => exact step_lt _ t x y xs at_ items gas fields
  | gtEmpty at_ short => exact step_gt_empty _ at_ short
  | gtGas x y xs at_ items gas => exact step_gt_gas _ x y xs at_ items gas
  | gt t x y xs at_ items gas fields => exact step_gt _ t x y xs at_ items gas fields
  | sltEmpty at_ short => exact step_slt_empty _ at_ short
  | sltGas x y xs at_ items gas => exact step_slt_gas _ x y xs at_ items gas
  | slt t x y xs at_ items gas fields => exact step_slt _ t x y xs at_ items gas fields
  | sgtEmpty at_ short => exact step_sgt_empty _ at_ short
  | sgtGas x y xs at_ items gas => exact step_sgt_gas _ x y xs at_ items gas
  | sgt t x y xs at_ items gas fields => exact step_sgt _ t x y xs at_ items gas fields
  | eqEmpty at_ short => exact step_eq_empty _ at_ short
  | eqGas x y xs at_ items gas => exact step_eq_gas _ x y xs at_ items gas
  | eq t x y xs at_ items gas fields => exact step_eq _ t x y xs at_ items gas fields
  | andEmpty at_ short => exact step_and_empty _ at_ short
  | andGas x y xs at_ items gas => exact step_and_gas _ x y xs at_ items gas
  | and t x y xs at_ items gas fields => exact step_and _ t x y xs at_ items gas fields
  | shlEmpty at_ short => exact step_shl_empty _ at_ short
  | shlGas x y xs at_ items gas => exact step_shl_gas _ x y xs at_ items gas
  | shl t x y xs at_ items gas fields => exact step_shl _ t x y xs at_ items gas fields
  | shrEmpty at_ short => exact step_shr_empty _ at_ short
  | shrGas x y xs at_ items gas => exact step_shr_gas _ x y xs at_ items gas
  | shr t x y xs at_ items gas fields => exact step_shr _ t x y xs at_ items gas fields
  | sarEmpty at_ short => exact step_sar_empty _ at_ short
  | sarGas x y xs at_ items gas => exact step_sar_gas _ x y xs at_ items gas
  | sar t x y xs at_ items gas fields => exact step_sar _ t x y xs at_ items gas fields
  | byteEmpty at_ short => exact step_byte_empty _ at_ short
  | byteGas x y xs at_ items gas => exact step_byte_gas _ x y xs at_ items gas
  | byte t x y xs at_ items gas fields => exact step_byte _ t x y xs at_ items gas fields
  | signextendEmpty at_ short => exact step_signextend_empty _ at_ short
  | signextendGas x y xs at_ items gas => exact step_signextend_gas _ x y xs at_ items gas
  | signextend t x y xs at_ items gas fields => exact step_signextend _ t x y xs at_ items gas fields
  | orEmpty at_ short => exact step_or_empty _ at_ short
  | orGas x y xs at_ items gas => exact step_or_gas _ x y xs at_ items gas
  | or t x y xs at_ items gas fields => exact step_or _ t x y xs at_ items gas fields
  | xorEmpty at_ short => exact step_xor_empty _ at_ short
  | xorGas x y xs at_ items gas => exact step_xor_gas _ x y xs at_ items gas
  | xor t x y xs at_ items gas fields => exact step_xor _ t x y xs at_ items gas fields
  | iszeroEmpty at_ short => exact step_iszero_empty _ at_ short
  | iszeroGas x xs at_ items gas => exact step_iszero_gas _ x xs at_ items gas
  | iszero t x xs at_ items gas fields => exact step_iszero _ t x xs at_ items gas fields
  | clzEmpty at_ short => exact step_clz_empty _ at_ short
  | clzGas x xs at_ items gas => exact step_clz_gas _ x xs at_ items gas
  | clz t x xs at_ items gas fields => exact step_clz _ t x xs at_ items gas fields
  | notEmpty at_ short => exact step_not_empty _ at_ short
  | notGas x xs at_ items gas => exact step_not_gas _ x xs at_ items gas
  | not t x xs at_ items gas fields => exact step_not _ t x xs at_ items gas fields
  | dupGas i at_ gas => exact step_dup_gas _ i at_ gas
  | dupEmpty i at_ gas empty => exact step_dup_empty _ i at_ gas empty
  | dupFull i at_ gas depth full => exact step_dup_full _ i at_ gas full
  | dup t i depth at_ gas room fields => exact step_dup _ t i at_ depth gas room fields
  | swapGas i at_ gas => exact step_swap_gas _ i at_ gas
  | swapEmpty i at_ gas empty => exact step_swap_empty _ i at_ gas empty
  | swap t i depth at_ gas fields => exact step_swap _ t i at_ depth gas fields

/-- Every input frame has a source-oriented rule. -/
theorem rule_total (s : State) : ∃ out, Rule s out := by
  by_cases bounds : s.pc < s.code.size
  · cases decoded : Opcode.decode s.code[s.pc] with
    | none => exact ⟨_, .invalid s (Or.inl ⟨bounds, decoded⟩)⟩
    | some op =>
      have at_ : At s (some op) := ⟨bounds, decoded⟩
      cases op with
      | stop => exact ⟨_, .stop s at_⟩
      | invalid => exact ⟨_, .invalid s (Or.inr at_)⟩
      | coinbase =>
        let o := Observation.coinbase
        have atO : At s (some o.opcode) := at_
        by_cases gas : 2 ≤ s.gas
        · by_cases room : s.stack.val.length < 1024
          · let stack : Stack := ⟨BitVec.ofNat 256 (o.value s) :: s.stack.val, by simp; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
            exact ⟨_, .observation s t o atO gas room (by simp [Advances, t, stack])⟩
          · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
            exact ⟨_, .observationFull s o atO gas full⟩
        · exact ⟨_, .observationGas s o atO (Nat.lt_of_not_ge gas)⟩
      | timestamp =>
        let o := Observation.timestamp
        have atO : At s (some o.opcode) := at_
        by_cases gas : 2 ≤ s.gas
        · by_cases room : s.stack.val.length < 1024
          · let stack : Stack := ⟨BitVec.ofNat 256 (o.value s) :: s.stack.val, by simp; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
            exact ⟨_, .observation s t o atO gas room (by simp [Advances, t, stack])⟩
          · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
            exact ⟨_, .observationFull s o atO gas full⟩
        · exact ⟨_, .observationGas s o atO (Nat.lt_of_not_ge gas)⟩
      | number =>
        let o := Observation.number
        have atO : At s (some o.opcode) := at_
        by_cases gas : 2 ≤ s.gas
        · by_cases room : s.stack.val.length < 1024
          · let stack : Stack := ⟨BitVec.ofNat 256 (o.value s) :: s.stack.val, by simp; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
            exact ⟨_, .observation s t o atO gas room (by simp [Advances, t, stack])⟩
          · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
            exact ⟨_, .observationFull s o atO gas full⟩
        · exact ⟨_, .observationGas s o atO (Nat.lt_of_not_ge gas)⟩
      | prevrandao =>
        let o := Observation.prevrandao
        have atO : At s (some o.opcode) := at_
        by_cases gas : 2 ≤ s.gas
        · by_cases room : s.stack.val.length < 1024
          · let stack : Stack := ⟨BitVec.ofNat 256 (o.value s) :: s.stack.val, by simp; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
            exact ⟨_, .observation s t o atO gas room (by simp [Advances, t, stack])⟩
          · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
            exact ⟨_, .observationFull s o atO gas full⟩
        · exact ⟨_, .observationGas s o atO (Nat.lt_of_not_ge gas)⟩
      | gaslimit =>
        let o := Observation.gaslimit
        have atO : At s (some o.opcode) := at_
        by_cases gas : 2 ≤ s.gas
        · by_cases room : s.stack.val.length < 1024
          · let stack : Stack := ⟨BitVec.ofNat 256 (o.value s) :: s.stack.val, by simp; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
            exact ⟨_, .observation s t o atO gas room (by simp [Advances, t, stack])⟩
          · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
            exact ⟨_, .observationFull s o atO gas full⟩
        · exact ⟨_, .observationGas s o atO (Nat.lt_of_not_ge gas)⟩
      | chainid =>
        let o := Observation.chainid
        have atO : At s (some o.opcode) := at_
        by_cases gas : 2 ≤ s.gas
        · by_cases room : s.stack.val.length < 1024
          · let stack : Stack := ⟨BitVec.ofNat 256 (o.value s) :: s.stack.val, by simp; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
            exact ⟨_, .observation s t o atO gas room (by simp [Advances, t, stack])⟩
          · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
            exact ⟨_, .observationFull s o atO gas full⟩
        · exact ⟨_, .observationGas s o atO (Nat.lt_of_not_ge gas)⟩
      | basefee =>
        let o := Observation.basefee
        have atO : At s (some o.opcode) := at_
        by_cases gas : 2 ≤ s.gas
        · by_cases room : s.stack.val.length < 1024
          · let stack : Stack := ⟨BitVec.ofNat 256 (o.value s) :: s.stack.val, by simp; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
            exact ⟨_, .observation s t o atO gas room (by simp [Advances, t, stack])⟩
          · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
            exact ⟨_, .observationFull s o atO gas full⟩
        · exact ⟨_, .observationGas s o atO (Nat.lt_of_not_ge gas)⟩
      | blobbasefee =>
        let o := Observation.blobbasefee
        have atO : At s (some o.opcode) := at_
        by_cases gas : 2 ≤ s.gas
        · by_cases room : s.stack.val.length < 1024
          · let stack : Stack := ⟨BitVec.ofNat 256 (o.value s) :: s.stack.val, by simp; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
            exact ⟨_, .observation s t o atO gas room (by simp [Advances, t, stack])⟩
          · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
            exact ⟨_, .observationFull s o atO gas full⟩
        · exact ⟨_, .observationGas s o atO (Nat.lt_of_not_ge gas)⟩
      | address =>
        let o := Observation.address
        have atO : At s (some o.opcode) := at_
        by_cases gas : 2 ≤ s.gas
        · by_cases room : s.stack.val.length < 1024
          · let stack : Stack := ⟨BitVec.ofNat 256 (o.value s) :: s.stack.val, by simp; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
            exact ⟨_, .observation s t o atO gas room (by simp [Advances, t, stack])⟩
          · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
            exact ⟨_, .observationFull s o atO gas full⟩
        · exact ⟨_, .observationGas s o atO (Nat.lt_of_not_ge gas)⟩
      | origin =>
        let o := Observation.origin
        have atO : At s (some o.opcode) := at_
        by_cases gas : 2 ≤ s.gas
        · by_cases room : s.stack.val.length < 1024
          · let stack : Stack := ⟨BitVec.ofNat 256 (o.value s) :: s.stack.val, by simp; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
            exact ⟨_, .observation s t o atO gas room (by simp [Advances, t, stack])⟩
          · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
            exact ⟨_, .observationFull s o atO gas full⟩
        · exact ⟨_, .observationGas s o atO (Nat.lt_of_not_ge gas)⟩
      | caller =>
        let o := Observation.caller
        have atO : At s (some o.opcode) := at_
        by_cases gas : 2 ≤ s.gas
        · by_cases room : s.stack.val.length < 1024
          · let stack : Stack := ⟨BitVec.ofNat 256 (o.value s) :: s.stack.val, by simp; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
            exact ⟨_, .observation s t o atO gas room (by simp [Advances, t, stack])⟩
          · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
            exact ⟨_, .observationFull s o atO gas full⟩
        · exact ⟨_, .observationGas s o atO (Nat.lt_of_not_ge gas)⟩
      | callvalue =>
        let o := Observation.callvalue
        have atO : At s (some o.opcode) := at_
        by_cases gas : 2 ≤ s.gas
        · by_cases room : s.stack.val.length < 1024
          · let stack : Stack := ⟨BitVec.ofNat 256 (o.value s) :: s.stack.val, by simp; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
            exact ⟨_, .observation s t o atO gas room (by simp [Advances, t, stack])⟩
          · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
            exact ⟨_, .observationFull s o atO gas full⟩
        · exact ⟨_, .observationGas s o atO (Nat.lt_of_not_ge gas)⟩
      | gasprice =>
        let o := Observation.gasprice
        have atO : At s (some o.opcode) := at_
        by_cases gas : 2 ≤ s.gas
        · by_cases room : s.stack.val.length < 1024
          · let stack : Stack := ⟨BitVec.ofNat 256 (o.value s) :: s.stack.val, by simp; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
            exact ⟨_, .observation s t o atO gas room (by simp [Advances, t, stack])⟩
          · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
            exact ⟨_, .observationFull s o atO gas full⟩
        · exact ⟨_, .observationGas s o atO (Nat.lt_of_not_ge gas)⟩
      | calldatasize =>
        let o := Observation.calldatasize
        have atO : At s (some o.opcode) := at_
        by_cases gas : 2 ≤ s.gas
        · by_cases room : s.stack.val.length < 1024
          · let stack : Stack := ⟨BitVec.ofNat 256 (o.value s) :: s.stack.val, by simp; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
            exact ⟨_, .observation s t o atO gas room (by simp [Advances, t, stack])⟩
          · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
            exact ⟨_, .observationFull s o atO gas full⟩
        · exact ⟨_, .observationGas s o atO (Nat.lt_of_not_ge gas)⟩
      | codesize =>
        let o := Observation.codesize
        have atO : At s (some o.opcode) := at_
        by_cases gas : 2 ≤ s.gas
        · by_cases room : s.stack.val.length < 1024
          · let stack : Stack := ⟨BitVec.ofNat 256 (o.value s) :: s.stack.val, by simp; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
            exact ⟨_, .observation s t o atO gas room (by simp [Advances, t, stack])⟩
          · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
            exact ⟨_, .observationFull s o atO gas full⟩
        · exact ⟨_, .observationGas s o atO (Nat.lt_of_not_ge gas)⟩
      | returndatasize =>
        let o := Observation.returndatasize
        have atO : At s (some o.opcode) := at_
        by_cases gas : 2 ≤ s.gas
        · by_cases room : s.stack.val.length < 1024
          · let stack : Stack := ⟨BitVec.ofNat 256 (o.value s) :: s.stack.val, by simp; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
            exact ⟨_, .observation s t o atO gas room (by simp [Advances, t, stack])⟩
          · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
            exact ⟨_, .observationFull s o atO gas full⟩
        · exact ⟨_, .observationGas s o atO (Nat.lt_of_not_ge gas)⟩
      | pc =>
        let o := Observation.pc
        have atO : At s (some o.opcode) := at_
        by_cases gas : 2 ≤ s.gas
        · by_cases room : s.stack.val.length < 1024
          · let stack : Stack := ⟨BitVec.ofNat 256 (o.value s) :: s.stack.val, by simp; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
            exact ⟨_, .observation s t o atO gas room (by simp [Advances, t, stack])⟩
          · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
            exact ⟨_, .observationFull s o atO gas full⟩
        · exact ⟨_, .observationGas s o atO (Nat.lt_of_not_ge gas)⟩
      | msize =>
        let o := Observation.msize
        have atO : At s (some o.opcode) := at_
        by_cases gas : 2 ≤ s.gas
        · by_cases room : s.stack.val.length < 1024
          · let stack : Stack := ⟨BitVec.ofNat 256 (o.value s) :: s.stack.val, by simp; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
            exact ⟨_, .observation s t o atO gas room (by simp [Advances, t, stack])⟩
          · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
            exact ⟨_, .observationFull s o atO gas full⟩
        · exact ⟨_, .observationGas s o atO (Nat.lt_of_not_ge gas)⟩
      | gas =>
        let o := Observation.gas
        have atO : At s (some o.opcode) := at_
        by_cases gas : 2 ≤ s.gas
        · by_cases room : s.stack.val.length < 1024
          · let stack : Stack := ⟨BitVec.ofNat 256 (o.value s) :: s.stack.val, by simp; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
            exact ⟨_, .observation s t o atO gas room (by simp [Advances, t, stack])⟩
          · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
            exact ⟨_, .observationFull s o atO gas full⟩
        · exact ⟨_, .observationGas s o atO (Nat.lt_of_not_ge gas)⟩
      | push n =>
        by_cases gas : (if n.val = 0 then 2 else 3) ≤ s.gas
        · by_cases room : s.stack.val.length < 1024
          · let stack : Stack := ⟨PushImmediate.value s.code s.pc n :: s.stack.val, by simp; omega⟩
            let t := { s with stack, pc := PushImmediate.nextPC s.pc n, gas := s.gas - (if n.val = 0 then 2 else 3) }
            exact ⟨_, .push s t n at_ gas room (by simp [Advances, t, stack])⟩
          · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
            exact ⟨_, .pushFull s n at_ gas full⟩
        · exact ⟨_, .pushGas s n at_ (Nat.lt_of_not_ge gas)⟩
      | jump =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .jumpEmpty s at_ items⟩
        | cons x xs =>
          by_cases gas : 8 ≤ s.gas
          · by_cases valid : ValidJumpDest s.code x.toNat
            · let stack : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
              let t := { s with stack, pc := x.toNat, gas := s.gas - 8 }
              exact ⟨_, .jump s t x xs at_ items gas valid (by simp [Advances, t, stack])⟩
            · exact ⟨_, .jumpInvalid s x xs at_ items gas valid⟩
          · exact ⟨_, .jumpGas s x xs at_ items (Nat.lt_of_not_ge gas)⟩
      | jumpi =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .jumpiEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .jumpiEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : 10 ≤ s.gas
            · by_cases cond : y.toNat = 0
              · let stack : Stack := ⟨ys, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
                let t := { s with stack, pc := s.pc + 1, gas := s.gas - 10 }
                exact ⟨_, .jumpiFalse s t x y ys at_ items gas cond (by simp [Advances, t, stack])⟩
              · by_cases valid : ValidJumpDest s.code x.toNat
                · let stack : Stack := ⟨ys, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
                  let t := { s with stack, pc := x.toNat, gas := s.gas - 10 }
                  exact ⟨_, .jumpiTrue s t x y ys at_ items gas cond valid (by simp [Advances, t, stack])⟩
                · exact ⟨_, .jumpiInvalid s x y ys at_ items gas cond valid⟩
            · exact ⟨_, .jumpiGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | jumpdest =>
        by_cases gas : 1 ≤ s.gas
        · let t := { s with pc := s.pc + 1, gas := s.gas - 1 }
          exact ⟨_, .jumpdest s t at_ gas (by simp [Advances, t])⟩
        · exact ⟨_, .jumpdestGas s at_ (Nat.lt_of_not_ge gas)⟩
      | pop =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .popEmpty s at_ items⟩
        | cons x xs =>
          by_cases gas : 2 ≤ s.gas
          · let stack : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
            exact ⟨_, .pop s t x xs at_ items gas (by simp [Advances, t, stack])⟩
          · exact ⟨_, .popGas s x xs at_ items (Nat.lt_of_not_ge gas)⟩
      | add =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .addEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .addEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : 3 ≤ s.gas
            · let stack : Stack := ⟨Word.add x y :: ys, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
              let t := { s with stack, pc := s.pc + 1, gas := s.gas - 3 }
              exact ⟨_, .add s t x y ys at_ items gas (by simp [Advances, t, stack])⟩
            · exact ⟨_, .addGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | addmod =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .addmodEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .addmodEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            cases ys with
            | nil => exact ⟨_, .addmodEmpty s at_ (by simp [items])⟩
            | cons m zs =>
              by_cases gas : 8 ≤ s.gas
              · let stack : Stack := ⟨Word.addmod x y m :: zs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
                let t := { s with stack, pc := s.pc + 1, gas := s.gas - 8 }
                exact ⟨_, .addmod s t x y m zs at_ items gas (by simp [Advances, t, stack])⟩
              · exact ⟨_, .addmodGas s x y m zs at_ items (Nat.lt_of_not_ge gas)⟩
      | mulmod =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .mulmodEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .mulmodEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            cases ys with
            | nil => exact ⟨_, .mulmodEmpty s at_ (by simp [items])⟩
            | cons m zs =>
              by_cases gas : 8 ≤ s.gas
              · let stack : Stack := ⟨Word.mulmod x y m :: zs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
                let t := { s with stack, pc := s.pc + 1, gas := s.gas - 8 }
                exact ⟨_, .mulmod s t x y m zs at_ items gas (by simp [Advances, t, stack])⟩
              · exact ⟨_, .mulmodGas s x y m zs at_ items (Nat.lt_of_not_ge gas)⟩
      | exp =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .expEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .expEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : Gas.expCost y ≤ s.gas
            · let stack : Stack := ⟨Word.exp x y :: ys, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
              let t := { s with stack, pc := s.pc + 1, gas := s.gas - Gas.expCost y }
              exact ⟨_, .exp s t x y ys at_ items gas (by simp [Advances, t, stack])⟩
            · exact ⟨_, .expGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | mul =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .mulEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .mulEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : 5 ≤ s.gas
            · let stack : Stack := ⟨Word.mul x y :: ys, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
              let t := { s with stack, pc := s.pc + 1, gas := s.gas - 5 }
              exact ⟨_, .mul s t x y ys at_ items gas (by simp [Advances, t, stack])⟩
            · exact ⟨_, .mulGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | sub =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .subEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .subEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : 3 ≤ s.gas
            · let stack : Stack := ⟨Word.sub x y :: ys, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
              let t := { s with stack, pc := s.pc + 1, gas := s.gas - 3 }
              exact ⟨_, .sub s t x y ys at_ items gas (by simp [Advances, t, stack])⟩
            · exact ⟨_, .subGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | div =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .divEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .divEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : 5 ≤ s.gas
            · let stack : Stack := ⟨Word.div x y :: ys, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
              let t := { s with stack, pc := s.pc + 1, gas := s.gas - 5 }
              exact ⟨_, .div s t x y ys at_ items gas (by simp [Advances, t, stack])⟩
            · exact ⟨_, .divGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | mod =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .modEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .modEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : 5 ≤ s.gas
            · let stack : Stack := ⟨Word.mod x y :: ys, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
              let t := { s with stack, pc := s.pc + 1, gas := s.gas - 5 }
              exact ⟨_, .mod s t x y ys at_ items gas (by simp [Advances, t, stack])⟩
            · exact ⟨_, .modGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | sdiv =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .sdivEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .sdivEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : 5 ≤ s.gas
            · let stack : Stack := ⟨Word.sdiv x y :: ys, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
              let t := { s with stack, pc := s.pc + 1, gas := s.gas - 5 }
              exact ⟨_, .sdiv s t x y ys at_ items gas (by simp [Advances, t, stack])⟩
            · exact ⟨_, .sdivGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | smod =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .smodEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .smodEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : 5 ≤ s.gas
            · let stack : Stack := ⟨Word.smod x y :: ys, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
              let t := { s with stack, pc := s.pc + 1, gas := s.gas - 5 }
              exact ⟨_, .smod s t x y ys at_ items gas (by simp [Advances, t, stack])⟩
            · exact ⟨_, .smodGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | lt =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .ltEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .ltEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : 3 ≤ s.gas
            · let stack : Stack := ⟨Word.ltResult x y :: ys, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
              let t := { s with stack, pc := s.pc + 1, gas := s.gas - 3 }
              exact ⟨_, .lt s t x y ys at_ items gas (by simp [Advances, t, stack])⟩
            · exact ⟨_, .ltGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | gt =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .gtEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .gtEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : 3 ≤ s.gas
            · let stack : Stack := ⟨Word.gtResult x y :: ys, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
              let t := { s with stack, pc := s.pc + 1, gas := s.gas - 3 }
              exact ⟨_, .gt s t x y ys at_ items gas (by simp [Advances, t, stack])⟩
            · exact ⟨_, .gtGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | slt =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .sltEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .sltEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : 3 ≤ s.gas
            · let stack : Stack := ⟨Word.sltResult x y :: ys, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
              let t := { s with stack, pc := s.pc + 1, gas := s.gas - 3 }
              exact ⟨_, .slt s t x y ys at_ items gas (by simp [Advances, t, stack])⟩
            · exact ⟨_, .sltGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | sgt =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .sgtEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .sgtEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : 3 ≤ s.gas
            · let stack : Stack := ⟨Word.sgtResult x y :: ys, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
              let t := { s with stack, pc := s.pc + 1, gas := s.gas - 3 }
              exact ⟨_, .sgt s t x y ys at_ items gas (by simp [Advances, t, stack])⟩
            · exact ⟨_, .sgtGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | eq =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .eqEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .eqEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : 3 ≤ s.gas
            · let stack : Stack := ⟨Word.eqResult x y :: ys, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
              let t := { s with stack, pc := s.pc + 1, gas := s.gas - 3 }
              exact ⟨_, .eq s t x y ys at_ items gas (by simp [Advances, t, stack])⟩
            · exact ⟨_, .eqGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | and =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .andEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .andEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : 3 ≤ s.gas
            · let stack : Stack := ⟨Word.bitwiseAnd x y :: ys, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
              let t := { s with stack, pc := s.pc + 1, gas := s.gas - 3 }
              exact ⟨_, .and s t x y ys at_ items gas (by simp [Advances, t, stack])⟩
            · exact ⟨_, .andGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | shl =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .shlEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .shlEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : 3 ≤ s.gas
            · let stack : Stack := ⟨Word.shl x y :: ys, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
              let t := { s with stack, pc := s.pc + 1, gas := s.gas - 3 }
              exact ⟨_, .shl s t x y ys at_ items gas (by simp [Advances, t, stack])⟩
            · exact ⟨_, .shlGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | shr =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .shrEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .shrEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : 3 ≤ s.gas
            · let stack : Stack := ⟨Word.shr x y :: ys, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
              let t := { s with stack, pc := s.pc + 1, gas := s.gas - 3 }
              exact ⟨_, .shr s t x y ys at_ items gas (by simp [Advances, t, stack])⟩
            · exact ⟨_, .shrGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | sar =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .sarEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .sarEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : 3 ≤ s.gas
            · let stack : Stack := ⟨Word.sar x y :: ys, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
              let t := { s with stack, pc := s.pc + 1, gas := s.gas - 3 }
              exact ⟨_, .sar s t x y ys at_ items gas (by simp [Advances, t, stack])⟩
            · exact ⟨_, .sarGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | byte =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .byteEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .byteEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : 3 ≤ s.gas
            · let stack : Stack := ⟨Word.byte x y :: ys, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
              let t := { s with stack, pc := s.pc + 1, gas := s.gas - 3 }
              exact ⟨_, .byte s t x y ys at_ items gas (by simp [Advances, t, stack])⟩
            · exact ⟨_, .byteGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | signextend =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .signextendEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .signextendEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : 5 ≤ s.gas
            · let stack : Stack := ⟨Word.signextend x y :: ys, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
              let t := { s with stack, pc := s.pc + 1, gas := s.gas - 5 }
              exact ⟨_, .signextend s t x y ys at_ items gas (by simp [Advances, t, stack])⟩
            · exact ⟨_, .signextendGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | or =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .orEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .orEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : 3 ≤ s.gas
            · let stack : Stack := ⟨Word.bitwiseOr x y :: ys, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
              let t := { s with stack, pc := s.pc + 1, gas := s.gas - 3 }
              exact ⟨_, .or s t x y ys at_ items gas (by simp [Advances, t, stack])⟩
            · exact ⟨_, .orGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | xor =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .xorEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .xorEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : 3 ≤ s.gas
            · let stack : Stack := ⟨Word.bitwiseXor x y :: ys, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
              let t := { s with stack, pc := s.pc + 1, gas := s.gas - 3 }
              exact ⟨_, .xor s t x y ys at_ items gas (by simp [Advances, t, stack])⟩
            · exact ⟨_, .xorGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | calldataload =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .calldataloadEmpty s at_ items⟩
        | cons x xs =>
          by_cases gas : 3 ≤ s.gas
          · let stack : Stack := ⟨CallData.load s.context x :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 3 }
            exact ⟨_, .calldataload s t x xs at_ items gas (by simp [Advances, t, stack])⟩
          · exact ⟨_, .calldataloadGas s x xs at_ items (Nat.lt_of_not_ge gas)⟩
      | blockhash =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .blockhashEmpty s at_ items⟩
        | cons x xs =>
          by_cases gas : 20 ≤ s.gas
          · let value := Environment.blockHash s.context.environment.blockHashes s.context.environment.number x
            let stack : Stack := ⟨value :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 20 }
            exact ⟨_, .blockhash s t x xs value at_ items gas ((blockHashValue_iff _ _ _ _).mpr rfl) (by simp [Advances, t, stack])⟩
          · exact ⟨_, .blockhashGas s x xs at_ items (Nat.lt_of_not_ge gas)⟩
      | blobhash =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .blobhashEmpty s at_ items⟩
        | cons x xs =>
          by_cases gas : 3 ≤ s.gas
          · let stack : Stack := ⟨Environment.blobHash s.context.environment x :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 3 }
            exact ⟨_, .blobhash s t x xs at_ items gas (by simp [Advances, t, stack])⟩
          · exact ⟨_, .blobhashGas s x xs at_ items (Nat.lt_of_not_ge gas)⟩
      | iszero =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .iszeroEmpty s at_ items⟩
        | cons x xs =>
          by_cases gas : 3 ≤ s.gas
          · let stack : Stack := ⟨Word.iszeroResult x :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 3 }
            exact ⟨_, .iszero s t x xs at_ items gas (by simp [Advances, t, stack])⟩
          · exact ⟨_, .iszeroGas s x xs at_ items (Nat.lt_of_not_ge gas)⟩
      | clz =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .clzEmpty s at_ items⟩
        | cons x xs =>
          by_cases gas : 5 ≤ s.gas
          · let stack : Stack := ⟨Word.countLeadingZeros x :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 5 }
            exact ⟨_, .clz s t x xs at_ items gas (by simp [Advances, t, stack])⟩
          · exact ⟨_, .clzGas s x xs at_ items (Nat.lt_of_not_ge gas)⟩
      | not =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .notEmpty s at_ items⟩
        | cons x xs =>
          by_cases gas : 3 ≤ s.gas
          · let stack : Stack := ⟨Word.bitwiseNot x :: xs, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 3 }
            exact ⟨_, .not s t x xs at_ items gas (by simp [Advances, t, stack])⟩
          · exact ⟨_, .notGas s x xs at_ items (Nat.lt_of_not_ge gas)⟩
      | dup i =>
        by_cases gas : 3 ≤ s.gas
        · by_cases depth : i.val < s.stack.val.length
          · by_cases room : s.stack.val.length < 1024
            · let stack : Stack := ⟨s.stack.val[i.val] :: s.stack.val, by simp; omega⟩
              let t := { s with stack, pc := s.pc + 1, gas := s.gas - 3 }
              exact ⟨_, .dup s t i depth at_ gas room (by simp [Advances, t, stack])⟩
            · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
              exact ⟨_, .dupFull s i at_ gas depth full⟩
          · exact ⟨_, .dupEmpty s i at_ gas (Nat.le_of_not_gt depth)⟩
        · exact ⟨_, .dupGas s i at_ (Nat.lt_of_not_ge gas)⟩
      | swap i =>
        by_cases gas : 3 ≤ s.gas
        · by_cases depth : i.val + 1 < s.stack.val.length
          · let stack : Stack := ⟨(s.stack.val.set 0 s.stack.val[i.val + 1]).set (i.val + 1)
                (s.stack.val[0]'(by omega)), by simpa using s.stack.property⟩
            let t := { s with stack, pc := s.pc + 1, gas := s.gas - 3 }
            exact ⟨_, .swap s t i depth at_ gas (by simp [Advances, t, stack])⟩
          · exact ⟨_, .swapEmpty s i at_ gas (Nat.le_of_not_gt depth)⟩
        · exact ⟨_, .swapGas s i at_ (Nat.lt_of_not_ge gas)⟩
      | calldatacopy =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .inputCopyEmpty s .calldata at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .inputCopyEmpty s .calldata at_ (by simp [items])⟩
          | cons y ys =>
            cases ys with
            | nil => exact ⟨_, .inputCopyEmpty s .calldata at_ (by simp [items])⟩
            | cons z zs =>
              by_cases gas : Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas
              · let stack : Stack := ⟨zs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
                let t : State := { s with stack, pc := s.pc + 1, gas := s.gas - Gas.inputCopyCost s.memory.words x.toNat z.toNat, memory := Memory.Allocation.write s.memory x.toNat (CallData.readRange (InputSource.bytes .calldata s) y.toNat z.toNat), memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid }
                exact ⟨_, .inputCopy s t .calldata x y z zs at_ items gas (by simp [AdvancesMemory, t, stack])⟩
              · exact ⟨_, .inputCopyGas s .calldata x y z zs at_ items (Nat.lt_of_not_ge gas)⟩
      | codecopy =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .inputCopyEmpty s .code at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .inputCopyEmpty s .code at_ (by simp [items])⟩
          | cons y ys =>
            cases ys with
            | nil => exact ⟨_, .inputCopyEmpty s .code at_ (by simp [items])⟩
            | cons z zs =>
              by_cases gas : Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas
              · let stack : Stack := ⟨zs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
                let t : State := { s with stack, pc := s.pc + 1, gas := s.gas - Gas.inputCopyCost s.memory.words x.toNat z.toNat, memory := Memory.Allocation.write s.memory x.toNat (CallData.readRange (InputSource.bytes .code s) y.toNat z.toNat), memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid }
                exact ⟨_, .inputCopy s t .code x y z zs at_ items gas (by simp [AdvancesMemory, t, stack])⟩
              · exact ⟨_, .inputCopyGas s .code x y z zs at_ items (Nat.lt_of_not_ge gas)⟩
      | keccak =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .keccakEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .keccakEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : Gas.keccakCost s.memory.words x.toNat y.toNat ≤ s.gas
            · let stack : Stack := ⟨digestWord (EthLib.Cryptography.Hash.Keccak.keccak256 ⟨(Memory.readRange s.memory.store x.toNat y.toNat).toArray⟩) :: ys, by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
              let t : State := { s with stack, pc := s.pc + 1, gas := s.gas - Gas.keccakCost s.memory.words x.toNat y.toNat, memory := Memory.Allocation.expand s.memory x.toNat y.toNat, memoryValid := Memory.Allocation.expand_valid_for_frame _ _ _ s.memoryValid }
              exact ⟨_, .keccak s t x y ys at_ items gas (by simp [AdvancesMemory, t, stack])⟩
            · exact ⟨_, .keccakGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | mcopy =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .mcopyEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .mcopyEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            cases ys with
            | nil => exact ⟨_, .mcopyEmpty s at_ (by simp [items])⟩
            | cons z zs =>
              by_cases gas : Gas.mcopyCost s.memory.words x.toNat y.toNat z.toNat ≤ s.gas
              · let stack : Stack := ⟨zs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
                let t : State := { s with stack, pc := s.pc + 1, gas := s.gas - Gas.mcopyCost s.memory.words x.toNat y.toNat z.toNat, memory := Memory.Allocation.copy s.memory x.toNat y.toNat z.toNat, memoryValid := Memory.Allocation.copy_valid_for_frame _ _ _ _ s.memoryValid }
                exact ⟨_, .mcopy s t x y z zs at_ items gas (by simp [AdvancesMemory, t, stack])⟩
              · exact ⟨_, .mcopyGas s x y z zs at_ items (Nat.lt_of_not_ge gas)⟩
      | mload =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .mloadEmpty s at_ items⟩
        | cons x xs =>
          by_cases gas : 3 + Gas.rangeCost s.memory.words x.toNat 32 ≤ s.gas
          · let stack : Stack := ⟨(Memory.Allocation.loadWord s.memory x.toNat).1 :: xs,
              by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
            let t : State := { s with stack, pc := s.pc + 1, gas := s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 32), memory := (Memory.Allocation.loadWord s.memory x.toNat).2, memoryValid := Memory.Allocation.expand_valid_for_frame _ _ _ s.memoryValid }
            exact ⟨_, .mload s t x xs at_ items gas (by simp [AdvancesMemory, t, stack])⟩
          · exact ⟨_, .mloadGas s x xs at_ items (Nat.lt_of_not_ge gas)⟩
      | mstore =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .mstoreEmpty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .mstoreEmpty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : 3 + Gas.rangeCost s.memory.words x.toNat 32 ≤ s.gas
            · let stack : Stack := ⟨ys, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
              let t : State := { s with stack, pc := s.pc + 1, gas := s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 32), memory := Memory.Allocation.storeWord s.memory x.toNat y, memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid }
              exact ⟨_, .mstore s t x y ys at_ items gas (by simp [AdvancesMemory, t, stack])⟩
            · exact ⟨_, .mstoreGas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | mstore8 =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .mstore8Empty s at_ (by simp [items])⟩
        | cons x xs =>
          cases xs with
          | nil => exact ⟨_, .mstore8Empty s at_ (by simp [items])⟩
          | cons y ys =>
            by_cases gas : 3 + Gas.rangeCost s.memory.words x.toNat 1 ≤ s.gas
            · let stack : Stack := ⟨ys, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
              let t : State := { s with stack, pc := s.pc + 1, gas := s.gas - (3 + Gas.rangeCost s.memory.words x.toNat 1), memory := Memory.Allocation.storeByte s.memory x.toNat y, memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid }
              exact ⟨_, .mstore8 s t x y ys at_ items gas (by simp [AdvancesMemory, t, stack])⟩
            · exact ⟨_, .mstore8Gas s x y ys at_ items (Nat.lt_of_not_ge gas)⟩
      | returndatacopy =>
        cases items : s.stack.val with
        | nil => exact ⟨_, .returnDataCopyEmpty s at_ (by simp [items])⟩
        | cons x ys =>
          cases ys with
          | nil => exact ⟨_, .returnDataCopyEmpty s at_ (by simp [items])⟩
          | cons y zs =>
            cases zs with
            | nil => exact ⟨_, .returnDataCopyEmpty s at_ (by simp [items])⟩
            | cons z rest =>
              by_cases gas : Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas
              · by_cases bounds : y.toNat + z.toNat ≤ s.returnData.size
                · let stack : Stack := ⟨rest, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
                  let t : State := { s with stack, pc := s.pc + 1, gas := s.gas - Gas.inputCopyCost s.memory.words x.toNat z.toNat, memory := Memory.Allocation.write s.memory x.toNat ((s.returnData.data.toList.drop y.toNat).take z.toNat), memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid }
                  exact ⟨_, .returnDataCopy s t x y z rest at_ items gas bounds (by simp [AdvancesMemory, t, stack])⟩
                · exact ⟨_, .returnDataCopyBounds s x y z rest at_ items gas (Nat.lt_of_not_ge bounds)⟩
              · exact ⟨_, .returnDataCopyGas s x y z rest at_ items (Nat.lt_of_not_ge gas)⟩
      | _ => exact ⟨_, .unsupported s _ at_ (by trivial)⟩
  · exact ⟨_, .endCode s (Nat.le_of_not_gt bounds)⟩

/-- Executable execution is equivalent to the independent frame rules. -/
theorem step_iff_rule (s : State) (out : Outcome) : step s = out ↔ Rule s out := by
  constructor
  · intro eq
    obtain ⟨result, rule⟩ := rule_total s
    have := rule_sound rule
    rw [eq] at this
    cases this
    exact rule
  · exact rule_sound

/-- No rule in the restricted frame semantics produces a revert. -/
theorem rule_not_revert (s input : State) (gas : Nat) (output : ByteArray) :
    ¬ Rule s (.revert input gas output) := by
  intro h
  cases h

/-- The restricted step cannot produce a revert for any input. -/
theorem step_not_revert (s input : State) (gas : Nat) (output : ByteArray) :
    step s ≠ .revert input gas output := by
  intro h
  exact rule_not_revert s input gas output ((step_iff_rule s _).mp h)

/-- Every continuing instruction preserves code. -/
theorem continue_code_unchanged {s t : State} (h : step s = .continue t) :
    t.code = s.code := by
  have rule := (step_iff_rule s _).mp h
  cases rule <;> simp_all [Advances, AdvancesMemory]

/-- Every outcome preserves the input code. -/
theorem outcome_code_unchanged {s : State} {out : Outcome} (h : Rule s out) :
    out.frame.code = s.code := by
  cases h <;> simp_all [Outcome.frame, Advances, AdvancesMemory]

/-- Every independent outcome retains the immutable message context. -/
theorem outcome_context_unchanged {s : State} {out : Outcome} (h : Rule s out) :
    out.frame.context = s.context := by
  cases h <;> simp_all [Outcome.frame, Advances, AdvancesMemory]

/-- Every continuing step retains the immutable message context. -/
theorem continue_context_unchanged {s t : State} (h : step s = .continue t) :
    t.context = s.context :=
  outcome_context_unchanged ((step_iff_rule s _).mp h)

/-- Every outcome retains the frame's return-data buffer. -/
theorem outcome_returnData_unchanged {s : State} {out : Outcome} (h : Rule s out) :
    out.frame.returnData = s.returnData := by
  cases h <;> simp_all [Outcome.frame, Advances, AdvancesMemory]

/-- Every continuing step retains the return-data buffer. -/
theorem continue_returnData_unchanged {s t : State} (h : step s = .continue t) :
    t.returnData = s.returnData :=
  outcome_returnData_unchanged ((step_iff_rule s _).mp h)

/-- A successful return-data copy determines its gas, bound and updated fields. -/
theorem returnDataCopy_actual (s t : State) (x y z : Word) (xs : List Word)
    (at_ : At s (some .returndatacopy)) (items : s.stack.val = x :: y :: z :: xs)
    (run : step s = .continue t) :
    Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas ∧
    y.toNat + z.toNat ≤ s.returnData.size ∧
    AdvancesMemory s t (Memory.Allocation.write s.memory x.toNat
      ((s.returnData.data.toList.drop y.toNat).take z.toNat))
      (s.pc + 1) (s.gas - Gas.inputCopyCost s.memory.words x.toNat z.toNat) xs := by
  rw [step_returnDataCopy s x y z xs at_ items] at run
  by_cases gas : Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas
  · by_cases bounds : y.toNat + z.toNat ≤ s.returnData.size
    · simp only [ite_eq_left gas, ite_eq_left bounds] at run
      cases run
      exact ⟨gas, bounds, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp [gas, bounds] at run
  · simp [gas] at run

/-- A bounds exception can only arise from a charged return-data copy. -/
theorem returnDataCopy_bounds_exception {s input : State}
    (run : step s = .exception input .outOfBoundsRead) :
    input = s ∧ ∃ x y z xs, At s (some .returndatacopy) ∧
      s.stack.val = x :: y :: z :: xs ∧
      Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas ∧
      s.returnData.size < y.toNat + z.toNat := by
  have rule := (step_iff_rule s _).mp run
  cases rule with
  | returnDataCopyBounds x y z xs at_ items gas bound =>
    exact ⟨rfl, x, y, z, xs, at_, items, gas, bound⟩

/-- A successful load determines its gas, stack, and all unchanged fields. -/
theorem calldataload_actual (s t : State) (x : Word) (xs : List Word)
    (at_ : At s (some .calldataload)) (items : s.stack.val = x :: xs)
    (run : step s = .continue t) :
    3 ≤ s.gas ∧ Advances s t (s.pc + 1) (s.gas - 3)
      (CallData.load s.context x :: xs) := by
  have gas : 3 ≤ s.gas := by
    by_cases h : 3 ≤ s.gas
    · exact h
    have bad := step_calldataload_gas s x xs at_ items (by omega)
    rw [run] at bad
    cases bad
  let stack : Stack := ⟨CallData.load s.context x :: xs, by
    have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  let target : State := { s with stack, pc := s.pc + 1, gas := s.gas - 3 }
  have fields : Advances s target (s.pc + 1) (s.gas - 3)
      (CallData.load s.context x :: xs) := by simp [Advances, target, stack]
  have ok := step_calldataload s target x xs at_ items gas fields
  rw [run] at ok
  have eq : t = target := Outcome.continue.inj ok
  exact ⟨gas, eq ▸ fields⟩

/-- Consecutive successful load and size steps expose both observations. -/
theorem load_then_calldatasize_actual (s t u : State) (x : Word) (xs : List Word)
    (loadAt : At s (some .calldataload)) (items : s.stack.val = x :: xs)
    (loadRun : step s = .continue t)
    (sizeAt : At t (some .calldatasize)) (sizeRun : step t = .continue u) :
    t.stack.val = CallData.load s.context x :: xs ∧ t.context = s.context ∧
      u.stack.val = observationWord s.context.data.size :: t.stack.val ∧
      u.context = s.context := by
  have load := (calldataload_actual s t x xs loadAt items loadRun).2
  have size := step_observation_stack t u .calldatasize sizeAt sizeRun
  have context : t.context = s.context := load.2.2.2.2.2.1
  have context2 : u.context = t.context := continue_context_unchanged sizeRun
  exact ⟨load.2.2.2.2.1, context, by simpa [Observation.value, context] using size,
    context2.trans context⟩

/-- A frame whose current instruction is outside the memory access subset. -/
def PureMemoryStep (s : State) : Prop :=
  ¬ At s (some .mload) ∧ ¬ At s (some .mstore) ∧ ¬ At s (some .mstore8) ∧ ¬ At s (some .mcopy) ∧
  ¬ At s (some .calldatacopy) ∧ ¬ At s (some .codecopy) ∧ ¬ At s (some .returndatacopy) ∧ ¬ At s (some .keccak)

/-- A pure instruction preserves memory for every outcome. -/
theorem outcome_memory_unchanged_of_pure {s : State} {out : Outcome}
    (pure : PureMemoryStep s) (h : Rule s out) : out.frame.memory = s.memory := by
  have excluded (source : InputSource) : ¬ At s (some source.opcode) := by
    cases source <;> simp_all [PureMemoryStep, InputSource.opcode]
  cases h <;> simp_all [PureMemoryStep, Outcome.frame, Advances]


/-- A continuing pure instruction preserves memory. -/
theorem continue_memory_unchanged_of_pure {s t : State}
    (pure : PureMemoryStep s) (h : step s = .continue t) : t.memory = s.memory := by
  exact outcome_memory_unchanged_of_pure pure ((step_iff_rule s _).mp h)

end EthLib.EVM.Frame
