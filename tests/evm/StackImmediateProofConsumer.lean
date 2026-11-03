import EthLib.EVM.Proofs.Frame.StackImmediate
import EthLib.EVM.Proofs.Frame.StackImmediateActual
import EthLib.EVM.Proofs.Runner.StackImmediate

open EthLib.EVM
open EthLib.EVM.Proofs.Frame.StackImmediate

-- These applications cover both directions of the direct-helper success contracts.
example (s t : Frame.State) (h : Frame.dupn s = .continue t) :
    3 ≤ s.gas ∧ ∃ n stack,
      StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = some n ∧
      s.stack.dupAt (n - 1) = .ok stack ∧
      t = { s with stack, gas := s.gas - 3, pc := s.pc + 2 } := (dupn_ok_iff s t).mp h
example (s t : Frame.State) (gas : 3 ≤ s.gas) (n : Nat) (stack : Stack)
    (imm : StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = some n)
    (hs : s.stack.dupAt (n - 1) = .ok stack)
    (ht : t = { s with stack, gas := s.gas - 3, pc := s.pc + 2 }) :
    Frame.dupn s = .continue t := (dupn_ok_iff s t).mpr ⟨gas, n, stack, imm, hs, ht⟩
example (s t : Frame.State) (h : Frame.swapn s = .continue t) :
    3 ≤ s.gas ∧ ∃ n stack,
      StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = some n ∧
      s.stack.exchangeAt 0 n = .ok stack ∧
      t = { s with stack, gas := s.gas - 3, pc := s.pc + 2 } := (swapn_ok_iff s t).mp h
example (s t : Frame.State) (gas : 3 ≤ s.gas) (n : Nat) (stack : Stack)
    (imm : StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = some n)
    (hs : s.stack.exchangeAt 0 n = .ok stack)
    (ht : t = { s with stack, gas := s.gas - 3, pc := s.pc + 2 }) :
    Frame.swapn s = .continue t := (swapn_ok_iff s t).mpr ⟨gas, n, stack, imm, hs, ht⟩
example (s t : Frame.State) (h : Frame.exchange s = .continue t) :
    3 ≤ s.gas ∧ ∃ n m stack,
      StackImmediate.decodePair (StackImmediate.byte s.code s.pc) = some (n, m) ∧
      s.stack.exchangeAt n m = .ok stack ∧
      t = { s with stack, gas := s.gas - 3, pc := s.pc + 2 } := (exchange_ok_iff s t).mp h
example (s t : Frame.State) (gas : 3 ≤ s.gas) (n m : Nat) (stack : Stack)
    (imm : StackImmediate.decodePair (StackImmediate.byte s.code s.pc) = some (n, m))
    (hs : s.stack.exchangeAt n m = .ok stack)
    (ht : t = { s with stack, gas := s.gas - 3, pc := s.pc + 2 }) :
    Frame.exchange s = .continue t := (exchange_ok_iff s t).mpr ⟨gas, n, m, stack, imm, hs, ht⟩

-- Exceptional results retain the input frame and identify the first failed check.
example (s input : Frame.State) (e : Frame.Exception) (h : Frame.dupn s = .exception input e) :
    input = s := by
  rcases (dupn_exception_iff s input e).mp h with h | h | h
  · exact h.2.1
  · exact h.2.2.1
  · obtain ⟨_, n, err, _, _, h⟩ := h
    cases err <;> simp only [Frame.failStack, Frame.Outcome.exception.injEq] at h <;> exact h.1.symm
example (s input : Frame.State) (e : Frame.Exception) (h : Frame.swapn s = .exception input e) :
    input = s := by
  rcases (swapn_exception_iff s input e).mp h with h | h | h
  · exact h.2.1
  · exact h.2.2.1
  · obtain ⟨_, n, err, _, _, h⟩ := h
    cases err <;> simp only [Frame.failStack, Frame.Outcome.exception.injEq] at h <;> exact h.1.symm
example (s input : Frame.State) (e : Frame.Exception) (h : Frame.exchange s = .exception input e) :
    input = s := by
  rcases (exchange_exception_iff s input e).mp h with h | h | h
  · exact h.2.1
  · exact h.2.2.1
  · obtain ⟨_, n, m, err, _, _, h⟩ := h
    cases err <;> simp only [Frame.failStack, Frame.Outcome.exception.injEq] at h <;> exact h.1.symm

example (a b c z : Word) (xs : List Word) (room : xs.length ≤ 1006)
    (g : Nat) (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem)
    (context : CallData.Context) (ret : ByteArray) (tracker : TransactionState.State) (warmAddresses : List World.Address) (warmSlots : List (World.Address × Word)) (static : Bool) (stateGas : Frame.StateGas) (logs : List Frame.LogEntry) :
    ∃ t, Runner.run 4 ⟨Runner.StackImmediate.program, 0,
      ⟨a :: b :: c :: List.replicate 14 z ++ xs, by simp; omega⟩,
      9 + g, mem, valid, context, ret, tracker, warmAddresses, warmSlots, static, stateGas, logs⟩ = .stopped t ∧
      t.pc = 7 ∧ t.gas = g ∧ t.code = Runner.StackImmediate.program ∧ t.memory = mem ∧
      t.context = context ∧ t.returnData = ret ∧
      t.stack.val = z :: a :: c :: b :: List.replicate 14 z ++ xs :=
  Runner.StackImmediate.run a b c z xs room g mem valid context ret tracker warmAddresses warmSlots static stateGas logs

-- Actual opcode successes expose the fields derived from execution.
example (s t : Frame.State) (at_ : Frame.At s (some .dupn))
    (h : Frame.step s = .continue t) : t.pc = s.pc + 2 ∧ t.gas = s.gas - 3 := by
  obtain ⟨_, _, _, _, _, fields⟩ := Frame.dupn_actual s t at_ h
  exact ⟨fields.2.2.1, fields.2.2.2.1⟩
example (s t : Frame.State) (at_ : Frame.At s (some .swapn))
    (h : Frame.step s = .continue t) : t.pc = s.pc + 2 ∧ t.gas = s.gas - 3 := by
  obtain ⟨_, _, _, _, fields⟩ := Frame.swapn_actual s t at_ h
  exact ⟨fields.2.2.1, fields.2.2.2.1⟩
example (s t : Frame.State) (at_ : Frame.At s (some .exchange))
    (h : Frame.step s = .continue t) : t.pc = s.pc + 2 ∧ t.gas = s.gas - 3 := by
  obtain ⟨_, _, _, _, _, _, fields⟩ := Frame.exchange_actual s t at_ h
  exact ⟨fields.2.2.1, fields.2.2.2.1⟩

-- Memory is unchanged for every outcome, including exceptional halts.
example (s : Frame.State) (out : Frame.Outcome) (at_ : Frame.At s (some .dupn))
    (h : Frame.step s = out) : out.frame.memory = s.memory :=
  Frame.immediate_outcome_memory s .dupn out at_ (Or.inl rfl) h

-- The exception converses can construct outcomes without an opcode premise.
example (s : Frame.State) (gas : s.gas < 3) :
    Frame.dupn s = .exception s .outOfGas :=
  (dupn_exception_iff s s .outOfGas).mpr (Or.inl ⟨gas, rfl, rfl⟩)
example (s : Frame.State) (gas : 3 ≤ s.gas)
    (bad : StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = none) :
    Frame.swapn s = .exception s .invalidParameter :=
  (swapn_exception_iff s s .invalidParameter).mpr (Or.inr (Or.inl ⟨gas, bad, rfl, rfl⟩))
example (s : Frame.State) (gas : 3 ≤ s.gas) (n m : Nat)
    (imm : StackImmediate.decodePair (StackImmediate.byte s.code s.pc) = some (n, m))
    (short : s.stack.height ≤ m) : Frame.exchange s = .exception s .stackUnderflow := by
  apply (exchange_exception_iff s s .stackUnderflow).mpr
  refine Or.inr (Or.inr ⟨gas, n, m, .underflow, imm, ?_, rfl⟩)
  exact (Proofs.StackIndexed.exchange_underflow_iff s.stack n m).mpr (Or.inr short)

-- Forward error contracts apply to arbitrary frames, without an opcode premise.
example (s : Frame.State) (gas : 3 ≤ s.gas)
    (bad : StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = none) :
    Frame.dupn s = .exception s .invalidParameter := dupn_invalid s gas bad
example (s : Frame.State) (n : Nat) (gas : 3 ≤ s.gas)
    (imm : StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = some n)
    (short : s.stack.height ≤ n - 1) : Frame.dupn s = .exception s .stackUnderflow :=
  dupn_stack_error s n .underflow gas imm
    ((Proofs.StackIndexed.dup_underflow_iff s.stack (n - 1)).mpr short)
example (s : Frame.State) (n : Nat) (gas : 3 ≤ s.gas)
    (imm : StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = some n)
    (depth : n - 1 < s.stack.height) (full : s.stack.height = 1024) :
    Frame.dupn s = .exception s .stackOverflow :=
  dupn_stack_error s n .overflow gas imm
    ((Proofs.StackIndexed.dup_overflow_iff s.stack (n - 1)).mpr ⟨depth, full⟩)
example (s : Frame.State) (gas : s.gas < 3) :
    Frame.swapn s = .exception s .outOfGas := swapn_gas s gas
example (s : Frame.State) (n : Nat) (gas : 3 ≤ s.gas)
    (imm : StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = some n)
    (short : s.stack.height ≤ n) : Frame.swapn s = .exception s .stackUnderflow :=
  swapn_stack_error s n .underflow gas imm
    ((Proofs.StackIndexed.exchange_underflow_iff s.stack 0 n).mpr (Or.inr short))
example (s : Frame.State) (gas : s.gas < 3) :
    Frame.exchange s = .exception s .outOfGas := exchange_gas s gas
example (s : Frame.State) (gas : 3 ≤ s.gas)
    (bad : StackImmediate.decodePair (StackImmediate.byte s.code s.pc) = none) :
    Frame.exchange s = .exception s .invalidParameter := exchange_invalid s gas bad

-- The exception converses recover the failed conditions, including stack depth.
example (s input : Frame.State) (h : Frame.dupn s = .exception input .stackUnderflow) :
    input = s ∧ 3 ≤ s.gas ∧ ∃ n,
      StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = some n ∧
      s.stack.height ≤ n - 1 := by
  rcases (dupn_exception_iff s input .stackUnderflow).mp h with h | h | h
  · simp at h
  · simp at h
  · obtain ⟨gas, n, err, imm, stack, failure⟩ := h
    cases err with
    | overflow => simp [Frame.failStack] at failure
    | underflow =>
      simp only [Frame.failStack, Frame.Outcome.exception.injEq] at failure
      exact ⟨failure.1.symm, gas, n, imm,
        (Proofs.StackIndexed.dup_underflow_iff s.stack (n - 1)).mp stack⟩
example (s input : Frame.State) (h : Frame.dupn s = .exception input .stackOverflow) :
    input = s ∧ 3 ≤ s.gas ∧ ∃ n,
      StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = some n ∧
      n - 1 < s.stack.height ∧ s.stack.height = 1024 := by
  rcases (dupn_exception_iff s input .stackOverflow).mp h with h | h | h
  · simp at h
  · simp at h
  · obtain ⟨gas, n, err, imm, stack, failure⟩ := h
    cases err with
    | underflow => simp [Frame.failStack] at failure
    | overflow =>
      simp only [Frame.failStack, Frame.Outcome.exception.injEq] at failure
      exact ⟨failure.1.symm, gas, n, imm,
        (Proofs.StackIndexed.dup_overflow_iff s.stack (n - 1)).mp stack⟩
example (s input : Frame.State) (h : Frame.swapn s = .exception input .stackUnderflow) :
    input = s ∧ 3 ≤ s.gas ∧ ∃ n,
      StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = some n ∧
      s.stack.height ≤ n := by
  rcases (swapn_exception_iff s input .stackUnderflow).mp h with h | h | h
  · simp at h
  · simp at h
  · obtain ⟨gas, n, err, imm, stack, failure⟩ := h
    cases err with
    | overflow => simp [Frame.failStack] at failure
    | underflow =>
      simp only [Frame.failStack, Frame.Outcome.exception.injEq] at failure
      have short := (Proofs.StackIndexed.exchange_underflow_iff s.stack 0 n).mp stack
      have bound : s.stack.height ≤ n := by rcases short with h | h <;> omega
      exact ⟨failure.1.symm, gas, n, imm, bound⟩
example (s input : Frame.State) (h : Frame.exchange s = .exception input .stackUnderflow) :
    input = s ∧ 3 ≤ s.gas ∧ ∃ n m,
      StackImmediate.decodePair (StackImmediate.byte s.code s.pc) = some (n, m) ∧
      (s.stack.height ≤ n ∨ s.stack.height ≤ m) := by
  rcases (exchange_exception_iff s input .stackUnderflow).mp h with h | h | h
  · simp at h
  · simp at h
  · obtain ⟨gas, n, m, err, imm, stack, failure⟩ := h
    cases err with
    | overflow => simp [Frame.failStack] at failure
    | underflow =>
      simp only [Frame.failStack, Frame.Outcome.exception.injEq] at failure
      exact ⟨failure.1.symm, gas, n, m, imm,
        (Proofs.StackIndexed.exchange_underflow_iff s.stack n m).mp stack⟩

example (s input : Frame.State) (h : Frame.dupn s = .exception input .outOfGas) :
    input = s ∧ s.gas < 3 := by
  rcases (dupn_exception_iff s input .outOfGas).mp h with h | h | h
  · exact ⟨h.2.1, h.1⟩
  · simp at h
  · obtain ⟨_, n, err, _, _, failure⟩ := h
    cases err <;> simp [Frame.failStack] at failure

example (s input : Frame.State) (h : Frame.dupn s = .exception input .invalidParameter) :
    input = s ∧ 3 ≤ s.gas ∧ StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = none := by
  rcases (dupn_exception_iff s input .invalidParameter).mp h with h | h | h
  · simp at h
  · exact ⟨h.2.2.1, h.1, h.2.1⟩
  · obtain ⟨_, n, err, _, _, failure⟩ := h
    cases err <;> simp [Frame.failStack] at failure

example (s input : Frame.State) (h : Frame.swapn s = .exception input .outOfGas) :
    input = s ∧ s.gas < 3 := by
  rcases (swapn_exception_iff s input .outOfGas).mp h with h | h | h
  · exact ⟨h.2.1, h.1⟩
  · simp at h
  · obtain ⟨_, n, err, _, _, failure⟩ := h
    cases err <;> simp [Frame.failStack] at failure

example (s input : Frame.State) (h : Frame.swapn s = .exception input .invalidParameter) :
    input = s ∧ 3 ≤ s.gas ∧ StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = none := by
  rcases (swapn_exception_iff s input .invalidParameter).mp h with h | h | h
  · simp at h
  · exact ⟨h.2.2.1, h.1, h.2.1⟩
  · obtain ⟨_, n, err, _, _, failure⟩ := h
    cases err <;> simp [Frame.failStack] at failure

example (s input : Frame.State) (h : Frame.exchange s = .exception input .outOfGas) :
    input = s ∧ s.gas < 3 := by
  rcases (exchange_exception_iff s input .outOfGas).mp h with h | h | h
  · exact ⟨h.2.1, h.1⟩
  · simp at h
  · obtain ⟨_, n, m, err, _, _, failure⟩ := h
    cases err <;> simp [Frame.failStack] at failure

example (s input : Frame.State) (h : Frame.exchange s = .exception input .invalidParameter) :
    input = s ∧ 3 ≤ s.gas ∧ StackImmediate.decodePair (StackImmediate.byte s.code s.pc) = none := by
  rcases (exchange_exception_iff s input .invalidParameter).mp h with h | h | h
  · simp at h
  · exact ⟨h.2.2.1, h.1, h.2.1⟩
  · obtain ⟨_, n, m, err, _, _, failure⟩ := h
    cases err <;> simp [Frame.failStack] at failure
