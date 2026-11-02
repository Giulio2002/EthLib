import EthLib.EVM.Proofs.Frame.Memory

open EthLib.EVM

-- These contracts impose no condition on the frame's code or program counter.
example (s t : Frame.State) (x y z : Word) (xs : List Word)
    (items : s.stack.val = x :: y :: z :: xs)
    (run : Frame.returnDataCopy s = .continue t) :
    Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas ∧
    y.toNat + z.toNat ≤ s.returnData.size ∧ t.returnData = s.returnData := by
  have h := Frame.returnDataCopy_helper_actual s t x y z xs items run
  exact ⟨h.1, h.2.1, h.2.2.2.2.2.2.2.2⟩

example (s t : Frame.State) (x y z : Word) (xs : List Word)
    (items : s.stack.val = x :: y :: z :: xs)
    (run : Frame.returnDataCopy s = .continue t) :
    ∃ h : y.toNat + z.toNat ≤ s.returnData.size,
      (∀ i, (hi : i < z.toNat) → Memory.readByte t.memory.store (x.toNat + i) =
        s.returnData[y.toNat + i]'(by omega)) ∧
      (∀ a, ¬ (x.toNat ≤ a ∧ a < x.toNat + z.toNat) →
        Memory.readByte t.memory.store a = Memory.readByte s.memory.store a) := by
  obtain ⟨bound, _, _, _, _, _, _, _, _, bytes, outside⟩ :=
    Frame.returnDataCopy_helper_actual_output s t x y z xs items run
  exact ⟨bound, bytes, outside⟩

example (s : Frame.State) (x y z : Word) (xs : List Word)
    (items : s.stack.val = x :: y :: z :: xs)
    (gas : Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas)
    (bad : s.returnData.size < y.toNat + z.toNat) :
    Frame.returnDataCopy s = .exception s .outOfBoundsRead :=
  Frame.returnDataCopy_helper_bounds s x y z xs items gas bad

example (s input : Frame.State)
    (run : Frame.returnDataCopy s = .exception input .outOfBoundsRead) :
    input = s ∧ ∃ x y z xs, s.stack.val = x :: y :: z :: xs ∧
      Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas ∧
      s.returnData.size < y.toNat + z.toNat :=
  Frame.returnDataCopy_helper_bounds_actual run

example (s : Frame.State) (out : Frame.Outcome) :
    Frame.returnDataCopy s = out ↔ Frame.ReturnDataCopyRule s out :=
  Frame.returnDataCopy_helper_iff_rule s out
