module

public import EthLib.EVM.Frame
public import EthLib.EVM.Proofs.StackIndexed

/-! All-domain outcomes for the Amsterdam immediate stack helpers. -/

@[expose] public section

namespace EthLib.EVM.Proofs.Frame.StackImmediate

open EthLib.EVM

/-- DUPN reports gas before inspecting code or stack. -/
theorem dupn_gas (s : Frame.State) (h : s.gas < 3) :
    Frame.dupn s = .exception s .outOfGas := by
  simp [Frame.dupn, Frame.charge, Gas.charge, Nat.not_le.mpr h]

/-- SWAPN reports gas before inspecting code or stack. -/
theorem swapn_gas (s : Frame.State) (h : s.gas < 3) :
    Frame.swapn s = .exception s .outOfGas := by
  simp [Frame.swapn, Frame.charge, Gas.charge, Nat.not_le.mpr h]

/-- EXCHANGE reports gas before inspecting code or stack. -/
theorem exchange_gas (s : Frame.State) (h : s.gas < 3) :
    Frame.exchange s = .exception s .outOfGas := by
  simp [Frame.exchange, Frame.charge, Gas.charge, Nat.not_le.mpr h]

/-- DUPN rejects an invalid byte after charging. -/
theorem dupn_invalid (s : Frame.State) (gas : 3 ≤ s.gas)
    (invalid : StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = none) :
    Frame.dupn s = .exception s .invalidParameter := by
  simp [Frame.dupn, Frame.charge, Gas.charge, gas, invalid]

/-- SWAPN rejects an invalid byte after charging. -/
theorem swapn_invalid (s : Frame.State) (gas : 3 ≤ s.gas)
    (invalid : StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = none) :
    Frame.swapn s = .exception s .invalidParameter := by
  simp [Frame.swapn, Frame.charge, Gas.charge, gas, invalid]

/-- EXCHANGE rejects an invalid byte after charging. -/
theorem exchange_invalid (s : Frame.State) (gas : 3 ≤ s.gas)
    (invalid : StackImmediate.decodePair (StackImmediate.byte s.code s.pc) = none) :
    Frame.exchange s = .exception s .invalidParameter := by
  simp [Frame.exchange, Frame.charge, Gas.charge, gas, invalid]

/-- Successful DUPN has the fields produced by the actual stack operation. -/
theorem dupn_ok_iff (s t : Frame.State) : Frame.dupn s = .continue t ↔
    3 ≤ s.gas ∧ ∃ n stack,
      StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = some n ∧
      s.stack.dupAt (n - 1) = .ok stack ∧
      t = { s with stack, gas := s.gas - 3, pc := s.pc + 2 } := by
  by_cases gas : 3 ≤ s.gas
  · cases hd : StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) with
    | none => simp [Frame.dupn, Frame.charge, Gas.charge, gas, hd]
    | some n =>
      cases hs : s.stack.dupAt (n - 1) with
      | error e => cases e <;> simp [Frame.dupn, Frame.charge, Gas.charge, gas, hd, hs, Frame.failStack]
      | ok stack =>
        constructor
        · intro h
          have eq : { s with stack, gas := s.gas - 3, pc := s.pc + 2 } = t := by
            simpa [Frame.dupn, Frame.charge, Gas.charge, gas, hd, hs] using h
          exact ⟨gas, n, stack, rfl, hs, eq.symm⟩
        · rintro ⟨_, n', stack', hn, ht, eq⟩
          have nn : n' = n := Option.some.inj hn.symm
          subst n'
          have ss : stack' = stack := Except.ok.inj (ht.symm.trans hs)
          subst stack'
          subst t
          simp [Frame.dupn, Frame.charge, Gas.charge, gas, hd, hs]
  · simp [Frame.dupn, Frame.charge, Gas.charge, gas]

/-- Successful SWAPN has the fields produced by the actual stack operation. -/
theorem swapn_ok_iff (s t : Frame.State) : Frame.swapn s = .continue t ↔
    3 ≤ s.gas ∧ ∃ n stack,
      StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = some n ∧
      s.stack.exchangeAt 0 n = .ok stack ∧
      t = { s with stack, gas := s.gas - 3, pc := s.pc + 2 } := by
  by_cases gas : 3 ≤ s.gas
  · cases hd : StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) with
    | none => simp [Frame.swapn, Frame.charge, Gas.charge, gas, hd]
    | some n =>
      cases hs : s.stack.exchangeAt 0 n with
      | error e => cases e <;> simp [Frame.swapn, Frame.charge, Gas.charge, gas, hd, hs, Frame.failStack]
      | ok stack =>
        constructor
        · intro h
          have eq : { s with stack, gas := s.gas - 3, pc := s.pc + 2 } = t := by
            simpa [Frame.swapn, Frame.charge, Gas.charge, gas, hd, hs] using h
          exact ⟨gas, n, stack, rfl, hs, eq.symm⟩
        · rintro ⟨_, n', stack', hn, ht, eq⟩
          have nn : n' = n := Option.some.inj hn.symm
          subst n'
          have ss : stack' = stack := Except.ok.inj (ht.symm.trans hs)
          subst stack'
          subst t
          simp [Frame.swapn, Frame.charge, Gas.charge, gas, hd, hs]
  · simp [Frame.swapn, Frame.charge, Gas.charge, gas]

/-- Successful EXCHANGE has the fields produced by the actual stack operation. -/
theorem exchange_ok_iff (s t : Frame.State) : Frame.exchange s = .continue t ↔
    3 ≤ s.gas ∧ ∃ n m stack,
      StackImmediate.decodePair (StackImmediate.byte s.code s.pc) = some (n, m) ∧
      s.stack.exchangeAt n m = .ok stack ∧
      t = { s with stack, gas := s.gas - 3, pc := s.pc + 2 } := by
  by_cases gas : 3 ≤ s.gas
  · cases hd : StackImmediate.decodePair (StackImmediate.byte s.code s.pc) with
    | none => simp [Frame.exchange, Frame.charge, Gas.charge, gas, hd]
    | some pair =>
      cases pair with
      | mk n m =>
        cases hs : s.stack.exchangeAt n m with
        | error e => cases e <;> simp [Frame.exchange, Frame.charge, Gas.charge, gas, hd, hs, Frame.failStack]
        | ok stack =>
          constructor
          · intro h
            have eq : { s with stack, gas := s.gas - 3, pc := s.pc + 2 } = t := by
              simpa [Frame.exchange, Frame.charge, Gas.charge, gas, hd, hs] using h
            exact ⟨gas, n, m, stack, rfl, hs, eq.symm⟩
          · rintro ⟨_, n', m', stack', hn, ht, eq⟩
            have pair : (n', m') = (n, m) := Option.some.inj hn.symm
            cases pair
            have ss : stack' = stack := Except.ok.inj (ht.symm.trans hs)
            subst stack'
            subst t
            simp [Frame.exchange, Frame.charge, Gas.charge, gas, hd, hs]
  · simp [Frame.exchange, Frame.charge, Gas.charge, gas]

/-- DUPN reports a stack error after a valid immediate. -/
theorem dupn_stack_error (s : Frame.State) (n : Nat) (e : StackError)
    (gas : 3 ≤ s.gas)
    (immediate : StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = some n)
    (stack : s.stack.dupAt (n - 1) = .error e) :
    Frame.dupn s = Frame.failStack s e := by
  simp [Frame.dupn, Frame.charge, Gas.charge, gas, immediate, stack]

/-- SWAPN reports a stack error after a valid immediate. -/
theorem swapn_stack_error (s : Frame.State) (n : Nat) (e : StackError)
    (gas : 3 ≤ s.gas)
    (immediate : StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = some n)
    (stack : s.stack.exchangeAt 0 n = .error e) :
    Frame.swapn s = Frame.failStack s e := by
  simp [Frame.swapn, Frame.charge, Gas.charge, gas, immediate, stack]

/-- EXCHANGE reports a stack error after a valid immediate. -/
theorem exchange_stack_error (s : Frame.State) (n m : Nat) (e : StackError)
    (gas : 3 ≤ s.gas)
    (immediate : StackImmediate.decodePair (StackImmediate.byte s.code s.pc) = some (n, m))
    (stack : s.stack.exchangeAt n m = .error e) :
    Frame.exchange s = Frame.failStack s e := by
  simp [Frame.exchange, Frame.charge, Gas.charge, gas, immediate, stack]

/-- Every DUPN exception has the source's first failing condition. -/
theorem dupn_exception_iff (s input : Frame.State) (reason : Frame.Exception) :
    Frame.dupn s = .exception input reason ↔
      (s.gas < 3 ∧ input = s ∧ reason = .outOfGas) ∨
      (3 ≤ s.gas ∧ StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = none ∧
        input = s ∧ reason = .invalidParameter) ∨
      (3 ≤ s.gas ∧ ∃ n e,
        StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = some n ∧
        s.stack.dupAt (n - 1) = .error e ∧ Frame.failStack s e = .exception input reason) := by
  by_cases gas : 3 ≤ s.gas
  · cases hd : StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) with
    | none => simp [Frame.dupn, Frame.charge, Gas.charge, gas, Nat.not_lt.mpr gas, hd, eq_comm]
    | some n =>
      cases hs : s.stack.dupAt (n - 1) with
      | error e => cases e <;> simp [Frame.dupn, Frame.charge, Gas.charge, gas, Nat.not_lt.mpr gas, hd, hs, Frame.failStack, eq_comm]
      | ok stack => simp [Frame.dupn, Frame.charge, Gas.charge, gas, Nat.not_lt.mpr gas, hd, hs, Frame.failStack, eq_comm]
  · simp [Frame.dupn, Frame.charge, Gas.charge, gas, Nat.lt_of_not_ge gas, eq_comm]

/-- Every SWAPN exception has the source's first failing condition. -/
theorem swapn_exception_iff (s input : Frame.State) (reason : Frame.Exception) :
    Frame.swapn s = .exception input reason ↔
      (s.gas < 3 ∧ input = s ∧ reason = .outOfGas) ∨
      (3 ≤ s.gas ∧ StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = none ∧
        input = s ∧ reason = .invalidParameter) ∨
      (3 ≤ s.gas ∧ ∃ n e,
        StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = some n ∧
        s.stack.exchangeAt 0 n = .error e ∧ Frame.failStack s e = .exception input reason) := by
  by_cases gas : 3 ≤ s.gas
  · cases hd : StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) with
    | none => simp [Frame.swapn, Frame.charge, Gas.charge, gas, Nat.not_lt.mpr gas, hd, eq_comm]
    | some n =>
      cases hs : s.stack.exchangeAt 0 n with
      | error e => cases e <;> simp [Frame.swapn, Frame.charge, Gas.charge, gas, Nat.not_lt.mpr gas, hd, hs, Frame.failStack, eq_comm]
      | ok stack => simp [Frame.swapn, Frame.charge, Gas.charge, gas, Nat.not_lt.mpr gas, hd, hs, Frame.failStack, eq_comm]
  · simp [Frame.swapn, Frame.charge, Gas.charge, gas, Nat.lt_of_not_ge gas, eq_comm]

/-- Every EXCHANGE exception has the source's first failing condition. -/
theorem exchange_exception_iff (s input : Frame.State) (reason : Frame.Exception) :
    Frame.exchange s = .exception input reason ↔
      (s.gas < 3 ∧ input = s ∧ reason = .outOfGas) ∨
      (3 ≤ s.gas ∧ StackImmediate.decodePair (StackImmediate.byte s.code s.pc) = none ∧
        input = s ∧ reason = .invalidParameter) ∨
      (3 ≤ s.gas ∧ ∃ n m e,
        StackImmediate.decodePair (StackImmediate.byte s.code s.pc) = some (n, m) ∧
        s.stack.exchangeAt n m = .error e ∧ Frame.failStack s e = .exception input reason) := by
  by_cases gas : 3 ≤ s.gas
  · cases hd : StackImmediate.decodePair (StackImmediate.byte s.code s.pc) with
    | none => simp [Frame.exchange, Frame.charge, Gas.charge, gas, Nat.not_lt.mpr gas, hd, eq_comm]
    | some pair =>
      cases pair with
      | mk n m =>
        cases hs : s.stack.exchangeAt n m with
        | error e => cases e <;> simp [Frame.exchange, Frame.charge, Gas.charge, gas, Nat.not_lt.mpr gas, hd, hs, Frame.failStack, eq_comm, and_assoc]
        | ok stack => simp [Frame.exchange, Frame.charge, Gas.charge, gas, Nat.not_lt.mpr gas, hd, hs, Frame.failStack, eq_comm, and_assoc]
  · simp [Frame.exchange, Frame.charge, Gas.charge, gas, Nat.lt_of_not_ge gas, eq_comm]

end EthLib.EVM.Proofs.Frame.StackImmediate
