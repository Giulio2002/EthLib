import EthLib.EVM.Proofs.Runner.ExtCodeCopy

open EthLib.EVM

namespace ExtCodeCopyConsumer

theorem first_forward (s : Frame.State) (empty : s.stack.val = []) :
    Frame.extCodeCopy s = .exception s .stackUnderflow :=
  (Frame.extCodeCopy_iff_local s _).mpr (.extCodeCopyEmpty s empty)

theorem second_forward (s : Frame.State) (first : Stack) (x : Word)
    (items : s.stack.val = x :: first.val) (empty : first.val = []) :
    Frame.extCodeCopy s = .exception { s with stack := first } .stackUnderflow :=
  (Frame.extCodeCopy_iff_local s _).mpr (.extCodeCopySecond s first x items empty)

theorem third_forward (s : Frame.State) (first second : Stack) (x destination : Word)
    (items : s.stack.val = x :: first.val) (items' : first.val = destination :: second.val) (empty : second.val = []) :
    Frame.extCodeCopy s = .exception { s with stack := second } .stackUnderflow :=
  (Frame.extCodeCopy_iff_local s _).mpr (.extCodeCopyThird s first second x destination items items' empty)

theorem fourth_forward (s : Frame.State) (first second third : Stack) (x destination source : Word)
    (items : s.stack.val = x :: first.val) (items' : first.val = destination :: second.val)
    (items'' : second.val = source :: third.val) (empty : third.val = []) :
    Frame.extCodeCopy s = .exception { s with stack := third } .stackUnderflow :=
  (Frame.extCodeCopy_iff_local s _).mpr (.extCodeCopyFourth s first second third x destination source items items' items'' empty)

theorem gas_forward (s : Frame.State) (first second third rest : Stack) (x destination source length : Word)
    (items : s.stack.val = x :: first.val) (items' : first.val = destination :: second.val)
    (items'' : second.val = source :: third.val) (items''' : third.val = length :: rest.val)
    (gas : s.gas < Frame.ExtCodeCopyCost s (Frame.BalanceAddress x) destination length) :
    Frame.extCodeCopy s = .exception { s with stack := rest, warmAddresses := Frame.BalanceWarm s (Frame.BalanceAddress x) } .outOfGas :=
  (Frame.extCodeCopy_iff_local s _).mpr (.extCodeCopyGas s first second third rest x destination source length items items' items'' items''' gas)

theorem gas_converse (s t : Frame.State) (run : Frame.extCodeCopy s = .exception t .outOfGas) :
    ∃ (first second third rest : Stack) (x destination source length : Word),
      s.stack.val = x :: first.val ∧ first.val = destination :: second.val ∧
      second.val = source :: third.val ∧ third.val = length :: rest.val ∧
      s.gas < Frame.ExtCodeCopyCost s (Frame.BalanceAddress x) destination length ∧
      t = { s with stack := rest, warmAddresses := Frame.BalanceWarm s (Frame.BalanceAddress x) } := by
  have h := (Frame.extCodeCopy_iff_local s _).mp run
  cases h with
  | extCodeCopyGas first second third rest x destination source length p q r v gas =>
    exact ⟨first, second, third, rest, x, destination, source, length, p, q, r, v, gas, rfl⟩

theorem underflow_converse (s t : Frame.State) (run : Frame.extCodeCopy s = .exception t .stackUnderflow) :
    (s.stack.val = [] ∧ t = s) ∨
    (∃ (first : Stack) (x : Word), s.stack.val = x :: first.val ∧ first.val = [] ∧ t = { s with stack := first }) ∨
    (∃ (first second : Stack) (x destination : Word), s.stack.val = x :: first.val ∧ first.val = destination :: second.val ∧ second.val = [] ∧ t = { s with stack := second }) ∨
    (∃ (first second third : Stack) (x destination source : Word), s.stack.val = x :: first.val ∧ first.val = destination :: second.val ∧ second.val = source :: third.val ∧ third.val = [] ∧ t = { s with stack := third }) := by
  have h := (Frame.extCodeCopy_iff_local s _).mp run
  cases h with
  | extCodeCopyEmpty empty => exact Or.inl ⟨empty, rfl⟩
  | extCodeCopySecond first x p empty => exact Or.inr (Or.inl ⟨first, x, p, empty, rfl⟩)
  | extCodeCopyThird first second x destination p q empty => exact Or.inr (Or.inr (Or.inl ⟨first, second, x, destination, p, q, empty, rfl⟩))
  | extCodeCopyFourth first second third x destination source p q r empty => exact Or.inr (Or.inr (Or.inr ⟨first, second, third, x, destination, source, p, q, r, empty, rfl⟩))

theorem missing_converse (s t : Frame.State) (run : Frame.extCodeCopy s = .exception t .missingCode) :
    ∃ (first second third rest : Stack) (x destination source length : Word),
      s.stack.val = x :: first.val ∧ first.val = destination :: second.val ∧
      second.val = source :: third.val ∧ third.val = length :: rest.val ∧
      Frame.ExtCodeCopyCost s (Frame.BalanceAddress x) destination length ≤ s.gas ∧
      Frame.ExtCodeBytes s (Frame.BalanceAddress x) = none ∧
      Frame.AdvancesMemory { s with warmAddresses := Frame.BalanceWarm s (Frame.BalanceAddress x), tracker := Frame.BalanceRead s (Frame.BalanceAddress x) }
        t (Memory.Allocation.expand s.memory destination.toNat length.toNat) s.pc
        (s.gas - Frame.ExtCodeCopyCost s (Frame.BalanceAddress x) destination length) rest.val := by
  have h := (Frame.extCodeCopy_iff_local s _).mp run
  cases h with
  | extCodeCopyMissing _ first second third rest x destination source length p q r v gas missing fields =>
    exact ⟨first, second, third, rest, x, destination, source, length, p, q, r, v, gas, missing, fields⟩

theorem missing_forward (s t : Frame.State) (first second third rest : Stack) (x destination source length : Word)
    (p : s.stack.val = x :: first.val) (q : first.val = destination :: second.val)
    (r : second.val = source :: third.val) (v : third.val = length :: rest.val)
    (gas : Frame.ExtCodeCopyCost s (Frame.BalanceAddress x) destination length ≤ s.gas)
    (missing : Frame.ExtCodeBytes s (Frame.BalanceAddress x) = none)
    (fields : Frame.AdvancesMemory { s with warmAddresses := Frame.BalanceWarm s (Frame.BalanceAddress x), tracker := Frame.BalanceRead s (Frame.BalanceAddress x) }
      t (Memory.Allocation.expand s.memory destination.toNat length.toNat) s.pc
      (s.gas - Frame.ExtCodeCopyCost s (Frame.BalanceAddress x) destination length) rest.val) :
    Frame.extCodeCopy s = .exception t .missingCode :=
  (Frame.extCodeCopy_iff_local s _).mpr (.extCodeCopyMissing s t first second third rest x destination source length p q r v gas missing fields)

theorem success_forward (s t : Frame.State) (first second third rest : Stack) (x destination source length : Word) (code : ByteArray)
    (p : s.stack.val = x :: first.val) (q : first.val = destination :: second.val)
    (r : second.val = source :: third.val) (v : third.val = length :: rest.val)
    (gas : Frame.ExtCodeCopyCost s (Frame.BalanceAddress x) destination length ≤ s.gas)
    (present : Frame.ExtCodeBytes s (Frame.BalanceAddress x) = some code)
    (fields : Frame.AdvancesMemory { s with warmAddresses := Frame.BalanceWarm s (Frame.BalanceAddress x), tracker := Frame.BalanceRead s (Frame.BalanceAddress x) }
      t (Memory.Allocation.write (Memory.Allocation.expand s.memory destination.toNat length.toNat) destination.toNat
        (CallData.readRange code source.toNat length.toNat)) (s.pc + 1)
      (s.gas - Frame.ExtCodeCopyCost s (Frame.BalanceAddress x) destination length) rest.val) :
    Frame.extCodeCopy s = .continue t :=
  (Frame.extCodeCopy_iff_local s _).mpr (.extCodeCopy s t first second third rest x destination source length code p q r v gas present fields (Frame.extCodeCopy_observation s destination source length code t fields.2.1))

theorem success_bytes (s t : Frame.State) (run : Frame.extCodeCopy s = .continue t) :
    ∃ (first second third rest : Stack) (x destination source length : Word) (code : ByteArray),
      s.stack.val = x :: first.val ∧ first.val = destination :: second.val ∧
      second.val = source :: third.val ∧ third.val = length :: rest.val ∧
      Frame.ExtCodeCopyCost s (Frame.BalanceAddress x) destination length ≤ s.gas ∧
      Frame.ExtCodeBytes s (Frame.BalanceAddress x) = some code ∧
      Memory.readRange t.memory.store destination.toNat length.toNat = CallData.readRange code source.toNat length.toNat :=
  Frame.extCodeCopy_success_bytes s t run

theorem success_converse (s t : Frame.State) (run : Frame.extCodeCopy s = .continue t) :
    ∃ (first second third rest : Stack) (x destination source length : Word) (code : ByteArray),
      s.stack.val = x :: first.val ∧ first.val = destination :: second.val ∧
      second.val = source :: third.val ∧ third.val = length :: rest.val ∧
      Frame.ExtCodeCopyCost s (Frame.BalanceAddress x) destination length ≤ s.gas ∧
      Frame.ExtCodeBytes s (Frame.BalanceAddress x) = some code ∧
      Frame.AdvancesMemory { s with warmAddresses := Frame.BalanceWarm s (Frame.BalanceAddress x), tracker := Frame.BalanceRead s (Frame.BalanceAddress x) }
        t (Memory.Allocation.write (Memory.Allocation.expand s.memory destination.toNat length.toNat) destination.toNat
          (CallData.readRange code source.toNat length.toNat)) (s.pc + 1)
        (s.gas - Frame.ExtCodeCopyCost s (Frame.BalanceAddress x) destination length) rest.val ∧
      Frame.ExtCodeCopyObservation s t destination source length code := by
  have h := (Frame.extCodeCopy_iff_local s _).mp run
  cases h with
  | extCodeCopy _ first second third rest x destination source length code p q r v gas present fields observation =>
    exact ⟨first, second, third, rest, x, destination, source, length, code, p, q, r, v, gas, present, fields, observation⟩

theorem success_each_byte (s t : Frame.State) (run : Frame.extCodeCopy s = .continue t) :
    ∃ (first second third rest : Stack) (x destination source length : Word) (code : ByteArray),
      s.stack.val = x :: first.val ∧ first.val = destination :: second.val ∧
      second.val = source :: third.val ∧ third.val = length :: rest.val ∧
      Frame.ExtCodeBytes s (Frame.BalanceAddress x) = some code ∧
      Frame.ExtCodeCopyObservation s t destination source length code := by
  have h := (Frame.extCodeCopy_iff_local s _).mp run
  cases h with
  | extCodeCopy _ first second third rest x destination source length code p q r v _gas present _fields observation =>
    exact ⟨first, second, third, rest, x, destination, source, length, code, p, q, r, v, present, observation⟩

theorem dispatch_converse (s t : Frame.State) (at_ : Frame.At s (some .extcodecopy))
    (run : Frame.step s = .continue t) :
    ∃ (first second third rest : Stack) (x destination source length : Word) (code : ByteArray),
      s.stack.val = x :: first.val ∧ first.val = destination :: second.val ∧
      second.val = source :: third.val ∧ third.val = length :: rest.val ∧
      Frame.ExtCodeBytes s (Frame.BalanceAddress x) = some code ∧
      Frame.ExtCodeCopyObservation s t destination source length code := by
  have h := (Frame.extCodeCopy_step_iff_local s _ at_).mp run
  cases h with
  | extCodeCopy _ first second third rest x destination source length code p q r v _gas present _fields observation =>
    exact ⟨first, second, third, rest, x, destination, source, length, code, p, q, r, v, present, observation⟩

theorem mixed_run (xs : List Word) (room : xs.length ≤ 1018) (x destination source length : Word) (g : Nat)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem)
    (context : CallData.Context) (returnData : ByteArray) (tracker : TransactionState.State)
    (warm : List World.Address) (slots : List (World.Address × Word)) (static : Bool) (meter : Frame.StateGas)
    (cold : Frame.BalanceAddress x ∉ warm) (code : ByteArray)
    (present : Frame.ExtCodeBytes
      ⟨Runner.ExtCodeCopyProgram.program, 0, ⟨x :: x :: destination :: source :: length :: destination :: xs, by simp; omega⟩,
        0, mem, valid, context, returnData, tracker, warm, slots, static, meter⟩ (Frame.BalanceAddress x) = some code) :
    let copied := Memory.Allocation.write (Memory.Allocation.expand mem destination.toNat length.toNat)
      destination.toNat (CallData.readRange code source.toNat length.toNat)
    let copyCost := 200 + 3 * ((length.toNat + 31) / 32) + Gas.rangeCost mem.words destination.toNat length.toNat
    let loadCost := 3 + Gas.rangeCost copied.words destination.toNat 32
    let s : Frame.State := ⟨Runner.ExtCodeCopyProgram.program, 0, ⟨x :: x :: destination :: source :: length :: destination :: xs, by simp; omega⟩,
      3000 + 2 + copyCost + loadCost + g, mem, valid, context, returnData, tracker, warm, slots, static, meter⟩
    ∃ t, Runner.run 5 s = .stopped t ∧ t.pc = 5 ∧ t.gas = g ∧
      t.stack.val = (Memory.Allocation.loadWord copied destination.toNat).1 :: xs ∧
      t.tracker = { tracker with accountReads := Frame.BalanceAddress x :: Frame.BalanceAddress x :: tracker.accountReads } ∧
      t.warmAddresses = Frame.BalanceAddress x :: warm :=
  Runner.ExtCodeCopyProgram.run xs room x destination source length g mem valid context returnData tracker warm slots static meter cold code present

end ExtCodeCopyConsumer
