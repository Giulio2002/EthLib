module

public import EthLib.EVM.Frame.Rules
public import EthLib.EVM.Proofs.Stack

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
  rcases h with ⟨code, memory, pcEq, gasEq, stackEq⟩
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

/-- An assigned opcode outside this slice yields the tooling result. -/
theorem step_unsupported (s : State) (op : Opcode) (h : At s (some op))
    (unsupported : Unsupported op) : step s = .unsupported s op := by
  obtain ⟨bounds, decoded⟩ := h
  cases op <;> simp_all [Unsupported, step]

/-- Every relational rule is accepted by the executable step. -/
theorem rule_sound {s : State} {out : Outcome} (h : Rule s out) : step s = out := by
  cases h with
  | endCode end_ => exact step_end _ end_
  | stop at_ => exact step_stop _ at_
  | invalid at_ => rcases at_ with h | h; exact step_unassigned _ h; exact step_invalid _ h
  | unsupported op at_ unsupported => exact step_unsupported _ op at_ unsupported
  | pushGas n at_ gas => exact step_push_gas _ n at_ gas
  | pushFull n at_ gas full => exact step_push_full _ n at_ gas full
  | push t n at_ gas room fields => exact step_push _ t n at_ gas room fields
  | popEmpty at_ empty => exact step_pop_empty _ at_ empty
  | popGas x xs at_ items gas => exact step_pop_gas _ x xs at_ items gas
  | pop t x xs at_ items gas fields => exact step_pop _ t x xs at_ items gas fields
  | addEmpty at_ short => exact step_add_empty _ at_ short
  | addGas x y xs at_ items gas => exact step_add_gas _ x y xs at_ items gas
  | add t x y xs at_ items gas fields => exact step_add _ t x y xs at_ items gas fields
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
      | push n =>
        by_cases gas : (if n.val = 0 then 2 else 3) ≤ s.gas
        · by_cases room : s.stack.val.length < 1024
          · let stack : Stack := ⟨PushImmediate.value s.code s.pc n :: s.stack.val, by simp; omega⟩
            let t := { s with stack, pc := PushImmediate.nextPC s.pc n, gas := s.gas - (if n.val = 0 then 2 else 3) }
            exact ⟨_, .push s t n at_ gas room (by simp [Advances, t, stack])⟩
          · have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
            exact ⟨_, .pushFull s n at_ gas full⟩
        · exact ⟨_, .pushGas s n at_ (Nat.lt_of_not_ge gas)⟩
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

/-- Every continuing instruction preserves code and memory. -/
theorem continue_unchanged {s t : State} (h : step s = .continue t) :
    t.code = s.code ∧ t.memory = s.memory := by
  have rule := (step_iff_rule s _).mp h
  cases rule <;> simp_all [Advances]

/-- Every outcome preserves the input code and allocated memory. -/
theorem outcome_unchanged {s : State} {out : Outcome} (h : Rule s out) :
    out.frame.code = s.code ∧ out.frame.memory = s.memory := by
  cases h <;> simp_all [Outcome.frame, Advances]

end EthLib.EVM.Frame
