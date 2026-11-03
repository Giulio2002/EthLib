import EthLib.EVM.Proofs.Runner.Log
import EthLib.EVM.Proofs.Runner.LogPreservation

open EthLib.EVM

namespace LogConsumer

theorem first_forward (s : Frame.State) (count : Fin 5) (empty : s.stack.val = []) :
    Frame.logN s count = .exception s .stackUnderflow :=
  (Frame.logN_iff_local s count _).mpr (.logEmpty s count empty)

theorem second_forward (s : Frame.State) (count : Fin 5) (first : Stack) (offset : Word)
    (items : s.stack.val = offset :: first.val) (empty : first.val = []) :
    Frame.logN s count = .exception { s with stack := first } .stackUnderflow :=
  (Frame.logN_iff_local s count _).mpr (.logSecond s count first offset items empty)

theorem topics_forward (s : Frame.State) (count : Fin 5) (first rest : Stack) (offset length : Word)
    (items : s.stack.val = offset :: first.val) (items' : first.val = length :: rest.val)
    (short : rest.val.length < count.val) :
    Frame.logN s count = .exception { s with stack := Stack.empty } .stackUnderflow :=
  (Frame.logN_iff_local s count _).mpr (.logTopicsUnderflow s count first rest offset length items items' short)

theorem underflow_converse (s t : Frame.State) (count : Fin 5)
    (run : Frame.logN s count = .exception t .stackUnderflow) :
    (s.stack.val = [] ∧ t = s) ∨
    (∃ (first : Stack) (offset : Word), s.stack.val = offset :: first.val ∧ first.val = [] ∧ t = { s with stack := first }) ∨
    (∃ (first rest : Stack) (offset length : Word), s.stack.val = offset :: first.val ∧
      first.val = length :: rest.val ∧ rest.val.length < count.val ∧ t = { s with stack := Stack.empty }) := by
  have local_ := (Frame.logN_iff_local s count _).mp run
  cases local_ with
  | logEmpty _ _ empty => exact Or.inl ⟨empty, rfl⟩
  | logSecond _ _ first offset p empty => exact Or.inr (Or.inl ⟨first, offset, p, empty, rfl⟩)
  | logTopicsUnderflow _ _ first rest offset length p q short =>
    exact Or.inr (Or.inr ⟨first, rest, offset, length, p, q, short, rfl⟩)

theorem gas_forward (s : Frame.State) (count : Fin 5) (first rest tail : Stack)
    (offset length : Word) (topics : List Word)
    (p : s.stack.val = offset :: first.val) (q : first.val = length :: rest.val)
    (split : rest.val = topics ++ tail.val) (size : topics.length = count.val)
    (gas : s.gas < 375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat) :
    Frame.logN s count = .exception { s with stack := tail } .outOfGas :=
  (Frame.logN_iff_local s count _).mpr (.logGas s count first rest tail offset length topics p q split size gas)

theorem static_forward (s t : Frame.State) (count : Fin 5) (first rest tail : Stack)
    (offset length : Word) (topics : List Word)
    (p : s.stack.val = offset :: first.val) (q : first.val = length :: rest.val)
    (split : rest.val = topics ++ tail.val) (size : topics.length = count.val) (static : s.isStatic = true)
    (gas : 375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat ≤ s.gas)
    (fields : Frame.AdvancesMemory s t (Memory.Allocation.expand s.memory offset.toNat length.toNat) s.pc
      (s.gas - (375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat)) tail.val) :
    Frame.logN s count = .exception t .writeInStaticContext :=
  (Frame.logN_iff_local s count _).mpr (.logStatic s t count first rest tail offset length topics p q split size static gas fields)

theorem success_forward (s t : Frame.State) (count : Fin 5) (first rest tail : Stack)
    (offset length : Word) (topics : List Word) (data : ByteArray)
    (p : s.stack.val = offset :: first.val) (q : first.val = length :: rest.val)
    (split : rest.val = topics ++ tail.val) (size : topics.length = count.val) (static : s.isStatic = false)
    (gas : 375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat ≤ s.gas)
    (eq : data = ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩)
    (bytes : Frame.LogDataObservation s offset length data)
    (fields : Frame.AdvancesMemory { s with logs := s.logs ++ [⟨s.context.environment.currentTarget, topics.map Frame.logTopic, data⟩] }
      t (Memory.Allocation.expand s.memory offset.toNat length.toNat) (s.pc + 1)
      (s.gas - (375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat)) tail.val) :
    Frame.logN s count = .continue t :=
  (Frame.logN_iff_local s count _).mpr (.logSuccess s t count first rest tail offset length topics data p q split size static gas eq bytes fields)

theorem rule_equivalence (s : Frame.State) (count : Fin 5) (out : Frame.Outcome)
    (at_ : Frame.At s (some (.log count))) : Frame.Rule s out ↔ Frame.LogLocal count s out :=
  Frame.log_rule_iff_local s count out at_

-- A successful helper exposes the popped words, gas, topic order and bytes.
theorem success_converse (s t : Frame.State) (count : Fin 5)
    (run : Frame.logN s count = .continue t) :
    ∃ (first rest tail : Stack) (offset length : Word) (topics : List Word) (data : ByteArray),
      s.stack.val = offset :: first.val ∧ first.val = length :: rest.val ∧
      rest.val = topics ++ tail.val ∧ topics.length = count.val ∧ s.isStatic = false ∧
      375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat ≤ s.gas ∧
      Frame.LogDataObservation s offset length data ∧
      Frame.AdvancesMemory { s with logs := s.logs ++ [⟨s.context.environment.currentTarget, topics.map Frame.logTopic, data⟩] }
        t (Memory.Allocation.expand s.memory offset.toNat length.toNat) (s.pc + 1)
        (s.gas - (375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat)) tail.val := by
  have local_ := (Frame.logN_iff_local s count _).mp run
  cases local_ with
  | logSuccess _ _ _ first rest tail offset length topics data p q split size static gas _ bytes fields =>
    exact ⟨first, rest, tail, offset, length, topics, data, p, q, split, size, static, gas, bytes, fields⟩

theorem gas_converse (s t : Frame.State) (count : Fin 5)
    (run : Frame.logN s count = .exception t .outOfGas) :
    ∃ (first rest tail : Stack) (offset length : Word) (topics : List Word),
      s.stack.val = offset :: first.val ∧ first.val = length :: rest.val ∧
      rest.val = topics ++ tail.val ∧ topics.length = count.val ∧
      s.gas < 375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat ∧
      t = { s with stack := tail } := by
  have local_ := (Frame.logN_iff_local s count _).mp run
  cases local_ with
  | logGas _ _ first rest tail offset length topics p q split size gas =>
    exact ⟨first, rest, tail, offset, length, topics, p, q, split, size, gas, rfl⟩

theorem static_converse (s t : Frame.State) (count : Fin 5)
    (run : Frame.logN s count = .exception t .writeInStaticContext) :
    ∃ (first rest tail : Stack) (offset length : Word) (topics : List Word),
      s.stack.val = offset :: first.val ∧ first.val = length :: rest.val ∧
      rest.val = topics ++ tail.val ∧ topics.length = count.val ∧ s.isStatic = true ∧
      375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat ≤ s.gas ∧
      Frame.AdvancesMemory s t (Memory.Allocation.expand s.memory offset.toNat length.toNat) s.pc
        (s.gas - (375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat)) tail.val := by
  have local_ := (Frame.logN_iff_local s count _).mp run
  cases local_ with
  | logStatic _ _ _ first rest tail offset length topics p q split size static gas fields =>
    exact ⟨first, rest, tail, offset, length, topics, p, q, split, size, static, gas, fields⟩

-- A caller can apply the constructed mixed program to any frame and prior logs.
theorem mixed_run (s : Frame.State) (topic : Word) (xs : List Word) (room : xs.length ≤ 1019) (g : Nat) :
    let initial : Frame.State := { s with code := Runner.LogProgram.program, pc := 0, gas := 1125 + g, isStatic := false, stack := ⟨0 :: 0 :: 0 :: 0 :: topic :: xs, by simp; omega⟩ }
    ∃ t, Runner.run 3 initial = .stopped t ∧ t.gas = g ∧ t.stack.val = xs ∧
      t.logs = s.logs ++ [⟨s.context.environment.currentTarget, [], ⟨#[]⟩⟩,
        ⟨s.context.environment.currentTarget, [Frame.logTopic topic], ⟨#[]⟩⟩] :=
  Runner.LogProgram.run s topic xs room g

theorem unchanged_trace (fuel : Nat) (s : Frame.State) (h : Runner.NoLogRun fuel s) :
    (Runner.run fuel s).frame.logs = s.logs :=
  Runner.run_logs_unchanged_of_noLog fuel s h

theorem prefix_trace (fuel : Nat) (s : Frame.State) :
    ∃ suffix, (Runner.run fuel s).frame.logs = s.logs ++ suffix :=
  Runner.run_logs_prefix fuel s

end LogConsumer
