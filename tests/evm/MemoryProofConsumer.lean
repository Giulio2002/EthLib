import EthLib.EVM.Proofs

open EthLib.EVM

-- A caller can recover the load head and its numeric value from an observed step.
example (s t : Frame.State) (x : Word) (xs : List Word)
    (at_ : Frame.At s (some .mload)) (items : s.stack.val = x :: xs)
    (run : Frame.step s = .continue t) :
    ∃ w, t.stack.val = w :: xs ∧ w.toNat =
      EthLib.Precompiles.Modexp.bytesToNat (Memory.readRange s.memory.store x.toNat 32) := by
  obtain ⟨_, _, _, _, stack, _, _, numeric⟩ := Frame.mload_success_output s t x xs at_ items run
  exact ⟨_, stack, numeric⟩

-- A caller can recover each written word byte and each outside byte.
example (s t : Frame.State) (x y : Word) (xs : List Word)
    (at_ : Frame.At s (some .mstore)) (items : s.stack.val = x :: y :: xs)
    (run : Frame.step s = .continue t) (i : Nat) (hi : i < 32) :
    Memory.readByte t.memory.store (x.toNat + i) =
      UInt8.ofNat ((y.toNat / 256 ^ (31 - i)) % 256) := by
  exact (Frame.mstore_success_output s t x y xs at_ items run).2.2.2.2.2.2.2 i hi

example (s t : Frame.State) (x y : Word) (xs : List Word)
    (at_ : Frame.At s (some .mstore8)) (items : s.stack.val = x :: y :: xs)
    (run : Frame.step s = .continue t) :
    (Memory.readByte t.memory.store x.toNat).toNat = y.toNat % 256 := by
  exact (Frame.mstore8_success_output s t x y xs at_ items run).2.2.2.2.2.2.1

-- Former unconditional memory preservation now requires a pure-instruction premise.
example (s t : Frame.State) (pure : Frame.PureMemoryStep s)
    (run : Frame.step s = .continue t) : t.code = s.code ∧ t.memory = s.memory :=
  ⟨Frame.continue_code_unchanged run, Frame.continue_memory_unchanged_of_pure pure run⟩

-- A pure bounded trace has the corresponding runner guarantee.
example (fuel : Nat) (s : Frame.State) (pure : Runner.PureMemoryRun fuel s) :
    (Runner.run fuel s).frame.code = s.code ∧ (Runner.run fuel s).frame.memory = s.memory :=
  ⟨Runner.run_code_unchanged fuel s, Runner.run_memory_unchanged_of_pure fuel s pure⟩

-- The converse also recovers gas sufficiency without post-state premises.
example (s t : Frame.State) (x : Word) (xs : List Word)
    (at_ : Frame.At s (some .mload)) (items : s.stack.val = x :: xs)
    (run : Frame.step s = .continue t) :
    3 + Gas.rangeCost s.memory.words x.toNat 32 ≤ s.gas :=
  (Frame.mload_success_fields s t x xs at_ items run).1

example (s t : Frame.State) (x y : Word) (xs : List Word)
    (at_ : Frame.At s (some .mstore)) (items : s.stack.val = x :: y :: xs)
    (run : Frame.step s = .continue t) :
    3 + Gas.rangeCost s.memory.words x.toNat 32 ≤ s.gas :=
  (Frame.mstore_success_fields s t x y xs at_ items run).1

example (s t : Frame.State) (x y : Word) (xs : List Word)
    (at_ : Frame.At s (some .mstore8)) (items : s.stack.val = x :: y :: xs)
    (run : Frame.step s = .continue t) :
    3 + Gas.rangeCost s.memory.words x.toNat 1 ≤ s.gas :=
  (Frame.mstore8_success_fields s t x y xs at_ items run).1

-- An observed copy exposes the original source bytes, including overlapping ranges.
example (s t : Frame.State) (x y z : Word) (xs : List Word)
    (at_ : Frame.At s (some .mcopy)) (items : s.stack.val = x :: y :: z :: xs)
    (run : Frame.step s = .continue t) (i : Nat) (hi : i < z.toNat) :
    Memory.readByte t.memory.store (x.toNat + i) =
      Memory.readByte s.memory.store (y.toNat + i) :=
  (Frame.mcopy_success_output s t x y z xs at_ items run).2.2.2.2.2.1 i hi

-- The public helper accepts data unrelated to the frame and any program counter.
example (s t : Frame.State) (data : ByteArray) (x y z : Word) (xs : List Word)
    (items : s.stack.val = x :: y :: z :: xs)
    (run : Frame.inputCopy s data = .continue t) (i : Nat) (hi : i < z.toNat) :
    t.pc = s.pc + 1 ∧ t.code = s.code ∧ t.context = s.context ∧
      Memory.readByte t.memory.store (x.toNat + i) =
        PushImmediate.byteAt data (y.toNat + i) := by
  have output := Frame.inputCopy_helper_success_output s t data x y z xs items run
  exact ⟨output.2.2.1, output.1, output.2.1, output.2.2.2.2.2.2.1 i hi⟩

-- A caller can derive zero padding without relating the data to the frame.
example (s t : Frame.State) (data : ByteArray) (x y z : Word) (xs : List Word)
    (items : s.stack.val = x :: y :: z :: xs)
    (run : Frame.inputCopy s data = .continue t) (i : Nat) (hi : i < z.toNat)
    (outside : data.size ≤ y.toNat + i) :
    Memory.readByte t.memory.store (x.toNat + i) = 0 := by
  rw [(Frame.inputCopy_helper_success_output s t data x y z xs items run).2.2.2.2.2.2.1 i hi]
  exact Proofs.PushImmediate.byteAt_out_of_range data (y.toNat + i) outside
