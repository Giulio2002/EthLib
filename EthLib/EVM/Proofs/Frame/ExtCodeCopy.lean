module

public import EthLib.EVM.Proofs.Frame.ExtCodeSize
public import EthLib.EVM.Proofs.CallData
public import EthLib.EVM.Proofs.Memory.Ranges

/-! Source-order contracts for Amsterdam `environment.py`, `extcodecopy`. -/

@[expose] public section
namespace EthLib.EVM.Frame

/-- Byte observations and allocation after a copy, independently of sparse-store layout. -/
def ExtCodeCopyObservation (s t : State) (destination source length : Word)
    (code : ByteArray) : Prop :=
  t.memory.words = max s.memory.words
      (if length.toNat = 0 then 0 else (destination.toNat + length.toNat + 31) / 32) ∧
  (∀ i, i < length.toNat →
    Memory.readByte t.memory.store (destination.toNat + i) =
      if h : source.toNat + i < code.size then code[source.toNat + i] else 0) ∧
  (∀ q, q < destination.toNat ∨ destination.toNat + length.toNat ≤ q →
    Memory.readByte t.memory.store q = Memory.readByte s.memory.store q)

/-- Source-order cases at arbitrary code and program counter. -/
inductive ExtCodeCopyLocal : State → Outcome → Prop where
  | extCodeCopyEmpty (s) : s.stack.val = [] →
      ExtCodeCopyLocal s (.exception s .stackUnderflow)
  | extCodeCopySecond (s : State) (first : Stack) (x : Word) : s.stack.val = x :: first.val → first.val = [] → ExtCodeCopyLocal s (.exception { s with stack := first } .stackUnderflow)
  | extCodeCopyThird (s : State) (first second : Stack) (x destination : Word) : s.stack.val = x :: first.val → first.val = destination :: second.val → second.val = [] →
      ExtCodeCopyLocal s (.exception { s with stack := second } .stackUnderflow)
  | extCodeCopyFourth (s : State) (first second third : Stack) (x destination source : Word) : s.stack.val = x :: first.val → first.val = destination :: second.val → second.val = source :: third.val → third.val = [] →
      ExtCodeCopyLocal s (.exception { s with stack := third } .stackUnderflow)
  | extCodeCopyGas (s : State) (first second third rest : Stack) (x destination source length : Word) :
      s.stack.val = x :: first.val → first.val = destination :: second.val →
      second.val = source :: third.val → third.val = length :: rest.val →
      s.gas < ExtCodeCopyCost s (BalanceAddress x) destination length →
      ExtCodeCopyLocal s (.exception { s with stack := rest, warmAddresses := BalanceWarm s (BalanceAddress x) } .outOfGas)
  | extCodeCopyMissing (s t : State) (first second third rest : Stack) (x destination source length : Word) :
      s.stack.val = x :: first.val → first.val = destination :: second.val →
      second.val = source :: third.val → third.val = length :: rest.val →
      ExtCodeCopyCost s (BalanceAddress x) destination length ≤ s.gas → ExtCodeBytes s (BalanceAddress x) = none →
      AdvancesMemory { s with warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x) }
        t (Memory.Allocation.expand s.memory destination.toNat length.toNat) s.pc
        (s.gas - ExtCodeCopyCost s (BalanceAddress x) destination length) rest.val → ExtCodeCopyLocal s (.exception t .missingCode)
  | extCodeCopy (s t : State) (first second third rest : Stack) (x destination source length : Word) (code : ByteArray) :
      s.stack.val = x :: first.val → first.val = destination :: second.val →
      second.val = source :: third.val → third.val = length :: rest.val →
      ExtCodeCopyCost s (BalanceAddress x) destination length ≤ s.gas → ExtCodeBytes s (BalanceAddress x) = some code →
      AdvancesMemory { s with warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x) }
        t (Memory.Allocation.write (Memory.Allocation.expand s.memory destination.toNat length.toNat) destination.toNat
          (CallData.readRange code source.toNat length.toNat)) (s.pc + 1)
        (s.gas - ExtCodeCopyCost s (BalanceAddress x) destination length) rest.val →
      ExtCodeCopyObservation s t destination source length code → ExtCodeCopyLocal s (.continue t)

/-- The executable sparse write has the specified byte observations. -/
theorem extCodeCopy_observation (s : State) (destination source length : Word) (code : ByteArray)
    (t : State)
    (memory : t.memory = Memory.Allocation.write
      (Memory.Allocation.expand s.memory destination.toNat length.toNat) destination.toNat
      (CallData.readRange code source.toNat length.toNat)) :
    ExtCodeCopyObservation s t destination source length code := by
  unfold ExtCodeCopyObservation
  rw [memory]
  constructor
  · simp [Memory.Allocation.write, Memory.Allocation.expand, Memory.Allocation.requiredWords,
      Proofs.CallData.readRange_length]
  constructor
  · intro i hi
    simp only [Memory.Allocation.write, Memory.Allocation.expand]
    rw [Memory.writeRange_observe]
    have inside : destination.toNat ≤ destination.toNat + i ∧
        destination.toNat + i < destination.toNat + (CallData.readRange code source.toNat length.toNat).length := by
      rw [Proofs.CallData.readRange_length]
      omega
    rw [dite_eq_left inside]
    simp only [Nat.add_sub_cancel_left]
    by_cases h : source.toNat + i < code.size
    · rw [dite_eq_left h]
      exact Proofs.CallData.readRange_in_range code source.toNat length.toNat i hi h
    · rw [dite_eq_right h]
      exact Proofs.CallData.readRange_pad code source.toNat length.toNat i hi (Nat.le_of_not_gt h)
  · intro q outside
    simp only [Memory.Allocation.write, Memory.Allocation.expand]
    apply Memory.writeRange_outside
    rw [Proofs.CallData.readRange_length]
    omega

/-- Every source case implies the helper outcome. -/
theorem extCodeCopy_local_sound {s : State} {out : Outcome} (h : ExtCodeCopyLocal s out) : extCodeCopy s = out := by
  cases h with
  | extCodeCopyEmpty empty =>
    have p := (Proofs.Stack.pop_underflow_iff _).mpr empty
    simp [extCodeCopy, p, failStack]
  | extCodeCopySecond first x items empty =>
    have p := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
    have q := (Proofs.Stack.pop_underflow_iff _).mpr empty
    simp [extCodeCopy, p, q, failStack]
  | extCodeCopyThird first second x destination items items' empty =>
    have p := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
    have q := (Proofs.Stack.pop_ok_iff _ _ _).mpr items'
    have r := (Proofs.Stack.pop_underflow_iff _).mpr empty
    simp [extCodeCopy, p, q, r, failStack]
  | extCodeCopyFourth first second third x destination source items items' items'' empty =>
    have p := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
    have q := (Proofs.Stack.pop_ok_iff _ _ _).mpr items'
    have r := (Proofs.Stack.pop_ok_iff _ _ _).mpr items''
    have v := (Proofs.Stack.pop_underflow_iff _).mpr empty
    simp [extCodeCopy, p, q, r, v, failStack]
  | extCodeCopyGas first second third rest x destination source length items items' items'' items''' gas =>
    have p := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
    have q := (Proofs.Stack.pop_ok_iff _ _ _).mpr items'
    have r := (Proofs.Stack.pop_ok_iff _ _ _).mpr items''
    have v := (Proofs.Stack.pop_ok_iff _ _ _).mpr items'''
    by_cases warm : BalanceAddress x ∈ s.warmAddresses <;>
      simp_all [extCodeCopy, balanceAddress, BalanceAddress, BalanceWarm, BalanceCost,
        ExtCodeSizeCost, ExtCodeCopyCost, charge, Gas.charge, Nat.not_le_of_gt]
  | extCodeCopyMissing t first second third rest x destination source length items items' items'' items''' gas missing fields =>
    have p := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
    have q := (Proofs.Stack.pop_ok_iff _ _ _).mpr items'
    have r := (Proofs.Stack.pop_ok_iff _ _ _).mpr items''
    have v := (Proofs.Stack.pop_ok_iff _ _ _).mpr items'''
    have valid := Memory.Allocation.expand_valid_for_frame s.memory destination.toNat length.toNat s.memoryValid
    have eq := advancesMemory_eq { s with warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x) }
      t (Memory.Allocation.expand s.memory destination.toNat length.toNat) valid s.pc
      (s.gas - ExtCodeCopyCost s (BalanceAddress x) destination length) rest fields
    subst t
    have addr : balanceAddress x = BalanceAddress x := rfl
    have cost : (if s.warmAddresses.contains (BalanceAddress x) then 200 else 3100) + 3 * ((length.toNat + 31) / 32) + Gas.rangeCost s.memory.words destination.toNat length.toNat = ExtCodeCopyCost s (BalanceAddress x) destination length := by simp [ExtCodeCopyCost, ExtCodeSizeCost, BalanceCost]; split <;> simp_all
    have warms : (if s.warmAddresses.contains (BalanceAddress x) then s.warmAddresses else BalanceAddress x :: s.warmAddresses) = BalanceWarm s (BalanceAddress x) := by simp [BalanceWarm]
    have bytes := extCodeBytes_eq s (BalanceAddress x)
    simp only [extCodeCopy, p, q, r, v, addr, cost, warms,
      charge, Gas.charge, ite_eq_left gas, bytes, missing]
    rfl
  | extCodeCopy t first second third rest x destination source length code items items' items'' items''' gas present fields _observation =>
    have p := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
    have q := (Proofs.Stack.pop_ok_iff _ _ _).mpr items'
    have r := (Proofs.Stack.pop_ok_iff _ _ _).mpr items''
    have v := (Proofs.Stack.pop_ok_iff _ _ _).mpr items'''
    have valid := Memory.Allocation.write_valid_for_frame (Memory.Allocation.expand s.memory destination.toNat length.toNat)
      destination.toNat (CallData.readRange code source.toNat length.toNat)
      (Memory.Allocation.expand_valid_for_frame _ _ _ s.memoryValid)
    have eq := advancesMemory_eq { s with warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x) }
      t (Memory.Allocation.write (Memory.Allocation.expand s.memory destination.toNat length.toNat) destination.toNat
        (CallData.readRange code source.toNat length.toNat)) valid (s.pc + 1)
      (s.gas - ExtCodeCopyCost s (BalanceAddress x) destination length) rest fields
    subst t
    have addr : balanceAddress x = BalanceAddress x := rfl
    have cost : (if s.warmAddresses.contains (BalanceAddress x) then 200 else 3100) + 3 * ((length.toNat + 31) / 32) + Gas.rangeCost s.memory.words destination.toNat length.toNat = ExtCodeCopyCost s (BalanceAddress x) destination length := by simp [ExtCodeCopyCost, ExtCodeSizeCost, BalanceCost]; split <;> simp_all
    have warms : (if s.warmAddresses.contains (BalanceAddress x) then s.warmAddresses else BalanceAddress x :: s.warmAddresses) = BalanceWarm s (BalanceAddress x) := by simp [BalanceWarm]
    have bytes := extCodeBytes_eq s (BalanceAddress x)
    simp only [extCodeCopy, p, q, r, v, addr, cost, warms,
      charge, Gas.charge, ite_eq_left gas, bytes, present]
    rfl

/-- The cases cover every input frame, including missing code. -/
theorem extCodeCopy_local_total (s : State) : ∃ out, ExtCodeCopyLocal s out := by
  cases items : s.stack.val with
  | nil => exact ⟨_, .extCodeCopyEmpty s items⟩
  | cons x xs =>
    let first : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
    have items' : s.stack.val = x :: first.val := items
    cases secondItems : first.val with
    | nil => exact ⟨_, .extCodeCopySecond s first x items' secondItems⟩
    | cons destination ys =>
      let second : Stack := ⟨ys, by have b := first.property; rw [secondItems] at b; simp at b; omega⟩
      have second' : first.val = destination :: second.val := secondItems
      cases thirdItems : second.val with
      | nil => exact ⟨_, .extCodeCopyThird s first second x destination items' second' thirdItems⟩
      | cons source zs =>
        let third : Stack := ⟨zs, by have b := second.property; rw [thirdItems] at b; simp at b; omega⟩
        have third' : second.val = source :: third.val := thirdItems
        cases fourthItems : third.val with
        | nil => exact ⟨_, .extCodeCopyFourth s first second third x destination source items' second' third' fourthItems⟩
        | cons length ws =>
          let rest : Stack := ⟨ws, by have b := third.property; rw [fourthItems] at b; simp at b; omega⟩
          have fourth' : third.val = length :: rest.val := fourthItems
          by_cases gas : ExtCodeCopyCost s (BalanceAddress x) destination length ≤ s.gas
          · cases bytes : ExtCodeBytes s (BalanceAddress x) with
            | none =>
              let t := { s with stack := rest, tracker := BalanceRead s (BalanceAddress x), warmAddresses := BalanceWarm s (BalanceAddress x), gas := s.gas - ExtCodeCopyCost s (BalanceAddress x) destination length, memory := Memory.Allocation.expand s.memory destination.toNat length.toNat, memoryValid := Memory.Allocation.expand_valid_for_frame _ _ _ s.memoryValid }
              exact ⟨_, .extCodeCopyMissing s t first second third rest x destination source length items' second' third' fourth' gas bytes (by simp [AdvancesMemory, t])⟩
            | some code =>
              let expanded := Memory.Allocation.expand s.memory destination.toNat length.toNat
              let t := { s with stack := rest, tracker := BalanceRead s (BalanceAddress x), warmAddresses := BalanceWarm s (BalanceAddress x), pc := s.pc + 1, gas := s.gas - ExtCodeCopyCost s (BalanceAddress x) destination length, memory := Memory.Allocation.write expanded destination.toNat (CallData.readRange code source.toNat length.toNat), memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ (Memory.Allocation.expand_valid_for_frame _ _ _ s.memoryValid) }
              exact ⟨_, .extCodeCopy s t first second third rest x destination source length code items' second' third' fourth' gas bytes (by simp [AdvancesMemory, t, expanded]) (extCodeCopy_observation s destination source length code t rfl)⟩
          · exact ⟨_, .extCodeCopyGas s first second third rest x destination source length items' second' third' fourth' (Nat.lt_of_not_ge gas)⟩

/-- The executable helper is equivalent to the independent source-order cases. -/
theorem extCodeCopy_iff_local (s : State) (out : Outcome) : extCodeCopy s = out ↔ ExtCodeCopyLocal s out := by
  constructor
  · intro run
    obtain ⟨result, rule⟩ := extCodeCopy_local_total s
    have sound := extCodeCopy_local_sound rule
    rw [run] at sound
    subst result
    exact rule
  · exact extCodeCopy_local_sound

/-- Dispatch and the operand-bound helper cases agree at an EXTCODECOPY instruction. -/
theorem extCodeCopy_step_iff_local (s : State) (out : Outcome)
    (at_ : At s (some .extcodecopy)) : step s = out ↔ ExtCodeCopyLocal s out := by
  obtain ⟨bounds, decoded⟩ := at_
  simpa only [step, dite_eq_left bounds, decoded] using extCodeCopy_iff_local s out

/-- The unrestricted frame rule and the refined helper cases agree at this opcode. -/
theorem extCodeCopy_rule_iff_local (s : State) (out : Outcome)
    (at_ : At s (some .extcodecopy)) : Rule s out ↔ ExtCodeCopyLocal s out :=
  (step_iff_rule s out).symm.trans (extCodeCopy_step_iff_local s out at_)

/-- A successful copy writes exactly the padded source byte sequence. -/
theorem extCodeCopy_success_bytes (s t : State) (run : extCodeCopy s = .continue t) :
    ∃ (first second third rest : Stack) (x destination source length : Word) (code : ByteArray),
      s.stack.val = x :: first.val ∧ first.val = destination :: second.val ∧
      second.val = source :: third.val ∧ third.val = length :: rest.val ∧
      ExtCodeCopyCost s (BalanceAddress x) destination length ≤ s.gas ∧
      ExtCodeBytes s (BalanceAddress x) = some code ∧
      Memory.readRange t.memory.store destination.toNat length.toNat =
        CallData.readRange code source.toNat length.toNat := by
  have local_ := (extCodeCopy_iff_local s _).mp run
  cases local_ with
  | extCodeCopy _ first second third rest x destination source length code items secondItems thirdItems fourthItems gas bytes fields _observation =>
    refine ⟨first, second, third, rest, x, destination, source, length, code,
      items, secondItems, thirdItems, fourthItems, gas, bytes, ?_⟩
    rw [fields.2.1]
    simpa [Memory.Allocation.write, Memory.Allocation.expand, CallData.readRange] using
      (Memory.readRange_writeRange s.memory.store destination.toNat (CallData.readRange code source.toNat length.toNat))

end EthLib.EVM.Frame
