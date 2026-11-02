module

public import EthLib.EVM.Proofs.Frame

/-! Actual successful frame fields for immediate stack instructions. -/

@[expose] public section
namespace EthLib.EVM.Frame

/-- A successful DUPN determines the immediate and every output field. -/
theorem dupn_actual (s t : State) (at_ : At s (some .dupn))
    (run : step s = .continue t) :
    3 ≤ s.gas ∧ ∃ n, ∃ depth : n - 1 < s.stack.height,
      StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = some n ∧
      s.stack.height < 1024 ∧
      Advances s t (s.pc + 2) (s.gas - 3) (s.stack.toList[n - 1]'depth :: s.stack.toList) := by
  obtain ⟨bounds, decoded⟩ := at_
  simp only [step, dite_eq_left bounds, decoded] at run
  obtain ⟨gas, n, stack, imm, hs, eq⟩ := (Proofs.Frame.StackImmediate.dupn_ok_iff s t).mp run
  obtain ⟨depth, room, contents⟩ := (Proofs.StackIndexed.dup_ok_iff _ _ _).mp hs
  subst t
  refine ⟨gas, n, depth, imm, room, ?_⟩
  simpa [Advances, Stack.toList] using contents

/-- A successful SWAPN determines the immediate and every output field. -/
theorem swapn_actual (s t : State) (at_ : At s (some .swapn))
    (run : step s = .continue t) :
    3 ≤ s.gas ∧ ∃ n, ∃ depth : n < s.stack.height,
      StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = some n ∧
      Advances s t (s.pc + 2) (s.gas - 3)
        ((s.stack.toList.set 0 (s.stack.toList[n]'depth)).set n
          (s.stack.toList[0]'(by change 0 < s.stack.height; omega))) := by
  obtain ⟨bounds, decoded⟩ := at_
  simp only [step, dite_eq_left bounds, decoded] at run
  obtain ⟨gas, n, stack, imm, hs, eq⟩ := (Proofs.Frame.StackImmediate.swapn_ok_iff s t).mp run
  obtain ⟨_, depth, contents⟩ := (Proofs.StackIndexed.exchange_ok_iff _ _ _ _).mp hs
  subst t
  refine ⟨gas, n, depth, imm, ?_⟩
  simpa [Advances, Stack.toList] using contents

/-- A successful EXCHANGE determines both indices and every output field. -/
theorem exchange_actual (s t : State) (at_ : At s (some .exchange))
    (run : step s = .continue t) :
    3 ≤ s.gas ∧ ∃ n m, ∃ hn : n < s.stack.height, ∃ hm : m < s.stack.height,
      StackImmediate.decodePair (StackImmediate.byte s.code s.pc) = some (n, m) ∧
      Advances s t (s.pc + 2) (s.gas - 3)
        ((s.stack.toList.set n (s.stack.toList[m]'hm)).set m (s.stack.toList[n]'hn)) := by
  obtain ⟨bounds, decoded⟩ := at_
  simp only [step, dite_eq_left bounds, decoded] at run
  obtain ⟨gas, n, m, stack, imm, hs, eq⟩ := (Proofs.Frame.StackImmediate.exchange_ok_iff s t).mp run
  obtain ⟨hn, hm, contents⟩ := (Proofs.StackIndexed.exchange_ok_iff _ _ _ _).mp hs
  subst t
  refine ⟨gas, n, m, hn, hm, imm, ?_⟩
  simpa [Advances, Stack.toList] using contents

/-- Every outcome of these instructions preserves memory. -/
theorem immediate_outcome_memory (s : State) (op : Opcode) (out : Outcome)
    (at_ : At s (some op)) (family : op = .dupn ∨ op = .swapn ∨ op = .exchange)
    (run : step s = out) : out.frame.memory = s.memory := by
  apply outcome_memory_unchanged_of_pure _ ((step_iff_rule s out).mp run)
  rcases family with rfl | rfl | rfl <;>
    obtain ⟨bounds, decoded⟩ := at_ <;>
    simp [PureMemoryStep, At, decoded]

end EthLib.EVM.Frame
