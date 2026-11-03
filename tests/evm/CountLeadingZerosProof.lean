import EthLib.EVM.Proofs.Runner.CountLeadingZeros

open EthLib.EVM

example (x : Word) (h : x.toNat ≠ 0) (k : Nat) (hk : k < 256) :
    (Word.countLeadingZeros x).toNat = k ↔
      2 ^ (255 - k) ≤ x.toNat ∧ x.toNat < 2 ^ (256 - k) :=
  Word.countLeadingZeros_interval_iff x h k hk

example (s t : Frame.State) (run : Frame.clz s = .continue t) :
    ∃ x xs, s.stack.val = x :: xs ∧ 5 ≤ s.gas ∧
      Frame.Advances s t (s.pc + 1) (s.gas - 5) (Word.countLeadingZeros x :: xs) :=
  Frame.clz_helper_actual s t run

example (x y : Word) (xs : List Word) (room : xs.length ≤ 1022)
    (g : Nat) (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem)
    (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State) (warmAddresses : List World.Address) (warmSlots : List (World.Address × Word)) :
    ∃ t, Runner.run 4 ⟨Runner.CountLeadingZeros.program, 0,
        ⟨x :: y :: xs, by simp; omega⟩, 10 + g, mem, valid, context, returnData, tracker, warmAddresses, warmSlots⟩ = .stopped t ∧
      t.stack.val = 2 :: Word.countLeadingZeros (Word.add x y) :: xs := by
  obtain ⟨t, run, _, _, _, _, _, _, stack⟩ :=
    Runner.CountLeadingZeros.run x y xs room g mem valid context returnData tracker warmAddresses warmSlots
  exact ⟨t, run, stack⟩

example (s : Frame.State) (out : Frame.Outcome) (at_ : Frame.At s (some .clz)) :
    Frame.step s = out ↔ Frame.ClzRule s out :=
  Frame.clz_step_iff s out at_

-- These direct-helper contracts quantify over all frame fields, including code and PC.
example (s : Frame.State) (empty : s.stack.val = []) :
    Frame.clz s = .exception s .stackUnderflow :=
  Frame.clz_helper_empty s empty

example (s : Frame.State) (x : Word) (xs : List Word)
    (items : s.stack.val = x :: xs) (gas : s.gas < 5) :
    Frame.clz s = .exception s .outOfGas :=
  Frame.clz_helper_gas s x xs items gas

example (s t : Frame.State) (x : Word) (xs : List Word)
    (items : s.stack.val = x :: xs) (gas : 5 ≤ s.gas)
    (fields : Frame.Advances s t (s.pc + 1) (s.gas - 5)
      (Word.countLeadingZeros x :: xs)) :
    Frame.clz s = .continue t :=
  Frame.clz_helper_success s t x xs items gas fields
