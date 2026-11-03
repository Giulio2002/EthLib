module

public import EthLib.EVM.Proofs.Frame
public import EthLib.EVM.Proofs.Memory.Ranges
import Aesop

@[expose] public section
namespace EthLib.EVM.Frame

/-- Data bytes observe the original sparse memory at the popped range. -/
def LogDataObservation (s : State) (offset length : Word) (data : ByteArray) : Prop :=
  data.size = length.toNat ∧ ∀ i, (h : i < data.size) →
    data[i] = Memory.readByte s.memory.store (offset.toNat + i)

/-- The source range reader has the independent byte observations. -/
theorem logData_observation (s : State) (offset length : Word) :
    LogDataObservation s offset length ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩ := by
  constructor
  · simp [ByteArray.size, Memory.readRange_length]
  · intro i h
    have bound : i < length.toNat := by simpa [ByteArray.size, Memory.readRange_length] using h
    simpa [ByteArray.getElem_eq_getElem_data] using Memory.readRange_getElem s.memory.store offset.toNat length.toNat i bound

/-- Source-order LOG cases at arbitrary code and program counter. -/
inductive LogLocal : Fin 5 → State → Outcome → Prop where
  | logEmpty (s : State) (count : Fin 5) : s.stack.val = [] →
      LogLocal count s (.exception s .stackUnderflow)
  | logSecond (s : State) (count : Fin 5) (first : Stack) (offset : Word) :
      s.stack.val = offset :: first.val → first.val = [] →
      LogLocal count s (.exception { s with stack := first } .stackUnderflow)
  | logTopicsUnderflow (s : State) (count : Fin 5) (first rest : Stack) (offset length : Word) :
      s.stack.val = offset :: first.val → first.val = length :: rest.val →
      rest.val.length < count.val → LogLocal count s (.exception { s with stack := Stack.empty } .stackUnderflow)
  | logGas (s : State) (count : Fin 5) (first rest tail : Stack) (offset length : Word) (topics : List Word) :
      s.stack.val = offset :: first.val → first.val = length :: rest.val →
      rest.val = topics ++ tail.val → topics.length = count.val →
      s.gas < 375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat →
      LogLocal count s (.exception { s with stack := tail } .outOfGas)
  | logStatic (s t : State) (count : Fin 5) (first rest tail : Stack) (offset length : Word) (topics : List Word) :
      s.stack.val = offset :: first.val → first.val = length :: rest.val →
      rest.val = topics ++ tail.val → topics.length = count.val → s.isStatic = true →
      375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat ≤ s.gas →
      AdvancesMemory s t (Memory.Allocation.expand s.memory offset.toNat length.toNat) s.pc
        (s.gas - (375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat)) tail.val →
      LogLocal count s (.exception t .writeInStaticContext)
  | logSuccess (s t : State) (count : Fin 5) (first rest tail : Stack) (offset length : Word) (topics : List Word) (data : ByteArray) :
      s.stack.val = offset :: first.val → first.val = length :: rest.val →
      rest.val = topics ++ tail.val → topics.length = count.val → s.isStatic = false →
      375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat ≤ s.gas →
      data = ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩ →
      LogDataObservation s offset length data →
      AdvancesMemory { s with logs := s.logs ++ [⟨s.context.environment.currentTarget, topics.map logTopic, data⟩] }
        t (Memory.Allocation.expand s.memory offset.toNat length.toNat) (s.pc + 1)
        (s.gas - (375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat)) tail.val →
      LogLocal count s (.continue t)

/-- Every local case determines the executable helper result. -/
theorem logLocal_sound {count : Fin 5} {s : State} {out : Outcome}
    (h : LogLocal count s out) : logN s count = out := by
  cases h with
  | logEmpty _ _ empty =>
    have p := (Proofs.Stack.pop_underflow_iff _).mpr empty
    simp [logN, p, failStack]
  | logSecond _ _ first offset items empty =>
    have p := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
    have q := (Proofs.Stack.pop_underflow_iff _).mpr empty
    simp [logN, p, q, failStack]
  | logTopicsUnderflow _ _ first rest offset length items items' short =>
    have p := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
    have q := (Proofs.Stack.pop_ok_iff _ _ _).mpr items'
    have r := popLogTopics_underflow count.val rest short
    simp [logN, p, q, r]
  | logGas _ _ first rest tail offset length topics items items' split size gas =>
    have p := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
    have q := (Proofs.Stack.pop_ok_iff _ _ _).mpr items'
    have r := popLogTopics_ok topics rest tail split
    rw [size] at r
    simp [logN, p, q, r, charge, Gas.charge, Nat.not_le_of_gt gas]
  | logStatic _ t _ first rest tail offset length topics items items' split size static gas fields =>
    have p := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
    have q := (Proofs.Stack.pop_ok_iff _ _ _).mpr items'
    have r := popLogTopics_ok topics rest tail split
    rw [size] at r
    have eq := advancesMemory_eq s t _ (Memory.Allocation.expand_valid_for_frame _ _ _ s.memoryValid)
      s.pc (s.gas - (375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat)) tail fields
    subst t
    simp [logN, p, q, r, charge, Gas.charge, gas, static]
  | logSuccess _ t _ first rest tail offset length topics data items items' split size static gas dataEq _observation fields =>
    subst data
    have p := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
    have q := (Proofs.Stack.pop_ok_iff _ _ _).mpr items'
    have r := popLogTopics_ok topics rest tail split
    rw [size] at r
    have eq := advancesMemory_eq _ t _ (Memory.Allocation.expand_valid_for_frame _ _ _ s.memoryValid)
      (s.pc + 1) (s.gas - (375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat)) tail fields
    subst t
    simp [logN, p, q, r, charge, Gas.charge, gas, static]

/-- The cases cover every input state and topic count. -/
theorem logLocal_total (s : State) (count : Fin 5) : ∃ out, LogLocal count s out := by
  cases items : s.stack.val with
  | nil => exact ⟨_, .logEmpty s count items⟩
  | cons offset xs =>
    let first : Stack := ⟨xs, by have h := s.stack.property; rw [items] at h; simp at h; omega⟩
    have items' : s.stack.val = offset :: first.val := items
    cases secondItems : first.val with
    | nil => exact ⟨_, .logSecond s count first offset items' secondItems⟩
    | cons length ys =>
      let rest : Stack := ⟨ys, by have h := first.property; rw [secondItems] at h; simp at h; omega⟩
      have second' : first.val = length :: rest.val := secondItems
      by_cases short : rest.val.length < count.val
      · exact ⟨_, .logTopicsUnderflow s count first rest offset length items' second' short⟩
      · let topics := rest.val.take count.val
        let tail : Stack := ⟨rest.val.drop count.val, by
          have h := rest.property
          simp only [List.length_drop]
          omega⟩
        have split : rest.val = topics ++ tail.val := (List.take_append_drop count.val rest.val).symm
        have size : topics.length = count.val := by simp [topics, Nat.min_eq_left (Nat.le_of_not_gt short)]
        by_cases gas : 375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat ≤ s.gas
        · by_cases static : s.isStatic = true
          · let t := { s with stack := tail, gas := s.gas - (375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat), memory := Memory.Allocation.expand s.memory offset.toNat length.toNat, memoryValid := Memory.Allocation.expand_valid_for_frame _ _ _ s.memoryValid }
            exact ⟨_, .logStatic s t count first rest tail offset length topics items' second' split size static gas (by simp [AdvancesMemory, t])⟩
          · let entry : LogEntry := ⟨s.context.environment.currentTarget, topics.map logTopic, ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩⟩
            let t := { s with stack := tail, gas := s.gas - (375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat), memory := Memory.Allocation.expand s.memory offset.toNat length.toNat, memoryValid := Memory.Allocation.expand_valid_for_frame _ _ _ s.memoryValid, logs := s.logs ++ [entry], pc := s.pc + 1 }
            have notStatic : s.isStatic = false := by cases h : s.isStatic <;> simp_all
            exact ⟨_, .logSuccess s t count first rest tail offset length topics _ items' second' split size notStatic gas rfl (logData_observation s offset length) (by simp [AdvancesMemory, t, entry])⟩
        · exact ⟨_, .logGas s count first rest tail offset length topics items' second' split size (Nat.lt_of_not_ge gas)⟩

/-- The helper is equivalent to the independent source-order cases. -/
theorem logN_iff_local (s : State) (count : Fin 5) (out : Outcome) :
    logN s count = out ↔ LogLocal count s out := by
  constructor
  · intro run
    obtain ⟨result, cases⟩ := logLocal_total s count
    have sound := logLocal_sound cases
    rw [run] at sound
    subst result
    exact cases
  · exact logLocal_sound

/-- The actual dispatcher and local cases agree for each LOG opcode. -/
theorem log_step_iff_local (s : State) (count : Fin 5) (out : Outcome)
    (at_ : At s (some (.log count))) : step s = out ↔ LogLocal count s out := by
  obtain ⟨bounds, decoded⟩ := at_
  simpa only [step, dite_eq_left bounds, decoded] using logN_iff_local s count out

/-- The global independent rule and local cases agree for each LOG opcode. -/
theorem log_rule_iff_local (s : State) (count : Fin 5) (out : Outcome)
    (at_ : At s (some (.log count))) : Rule s out ↔ LogLocal count s out :=
  (step_iff_rule s out).symm.trans (log_step_iff_local s count out at_)

end EthLib.EVM.Frame
