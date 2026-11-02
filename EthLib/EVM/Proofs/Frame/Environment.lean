module

public import EthLib.EVM.Proofs.Frame
public import EthLib.EVM.Proofs.Environment

/-! The observation rules select the message fields and preserve their values. -/

@[expose] public section
namespace EthLib.EVM.Frame

/-- The address observations use zero extension, with no reduction. -/
theorem environment_address_values (s : State) :
    observationWord (Observation.address.value s) = Environment.addressWord s.context.environment.currentTarget ∧
    observationWord (Observation.origin.value s) = Environment.addressWord s.context.environment.origin ∧
    observationWord (Observation.caller.value s) = Environment.addressWord s.context.environment.caller := by
  exact ⟨rfl, rfl, rfl⟩

/-- Value and gas price are already words and are preserved by observation. -/
theorem environment_word_values (s : State) :
    observationWord (Observation.callvalue.value s) = s.context.environment.value ∧
    observationWord (Observation.gasprice.value s) = s.context.environment.gasPrice := by
  simp [observationWord, Observation.value]

/-- Each block observation selects the supplied field. -/
theorem block_observation_values (s : State) :
    observationWord (Observation.coinbase.value s) = Environment.addressWord s.context.environment.coinbase ∧
    observationWord (Observation.timestamp.value s) = s.context.environment.timestamp ∧
    observationWord (Observation.number.value s) = s.context.environment.number ∧
    observationWord (Observation.prevrandao.value s) = s.context.environment.prevRandao ∧
    observationWord (Observation.gaslimit.value s) = s.context.environment.gasLimit ∧
    observationWord (Observation.chainid.value s) = BitVec.ofNat 256 s.context.environment.chainId.val ∧
    observationWord (Observation.basefee.value s) = s.context.environment.baseFee := by
  simp [observationWord, Observation.value, Environment.addressWord]

/-- The chain identifier is zero extended without reduction. -/
theorem chainId_word_toNat (id : Fin (2 ^ 64)) :
    (BitVec.ofNat 256 id.val).toNat = id.val := by
  simp only [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have bound := id.isLt
  have widths : 2 ^ 64 < 2 ^ 256 := by decide
  omega

/-- The word stored for PREVRANDAO has exactly the supplied big-endian bytes. -/
theorem prevRandao_codec (bytes : ByteArray) (s : State)
    (h : Word.ofBytesBE bytes = .ok s.context.environment.prevRandao) :
    s.context.environment.prevRandao.toBytesBE = bytes :=
  EthLib.EVM.Proofs.Word.toBytesBE_ofBytesBE bytes _ h

/-- Actual success yields the selected block word and preserves the context. -/
theorem block_observation_actual (s t : State) (o : Observation)
    (at_ : At s (some o.opcode)) (run : step s = .continue t) :
    t.stack.val = observationWord (o.value s) :: s.stack.val ∧
    t.context = s.context := by
  have fields := step_observation_actual s t o at_ run
  exact ⟨fields.2.2.2.2.2.2.1, fields.2.2.2.2.2.2.2.1⟩

/-- A successful helper invocation determines all output fields for any value function. -/
theorem observe_actual (s t : State) (value : Nat → Nat)
    (run : observe s value = .continue t) :
    2 ≤ s.gas ∧ s.stack.val.length < 1024 ∧
      Advances s t (s.pc + 1) (s.gas - 2)
        (observationWord (value (s.gas - 2)) :: s.stack.val) := by
  have gas : 2 ≤ s.gas := by
    by_cases h : 2 ≤ s.gas
    · exact h
    have bad := observe_gas s value (by omega)
    rw [run] at bad
    cases bad
  have room : s.stack.val.length < 1024 := by
    by_cases h : s.stack.val.length < 1024
    · exact h
    have full : s.stack.val.length = 1024 := by have := s.stack.property; omega
    have bad := observe_full s value gas full
    rw [run] at bad
    cases bad
  let stack : Stack := ⟨observationWord (value (s.gas - 2)) :: s.stack.val, by simp; omega⟩
  let target : State := { s with stack, pc := s.pc + 1, gas := s.gas - 2 }
  have fields : Advances s target (s.pc + 1) (s.gas - 2)
      (observationWord (value (s.gas - 2)) :: s.stack.val) := by simp [Advances, target, stack]
  have ok := observe_success s target value gas room fields
  rw [run] at ok
  have eq : t = target := Outcome.continue.inj ok
  exact ⟨gas, room, eq ▸ fields⟩

/-- An empty stack fails before the gas check for every helper invocation. -/
theorem blobHash_empty (s : State) (empty : s.stack.val = []) :
    blobHash s = .exception s .stackUnderflow := by
  have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr empty
  simp [blobHash, pop, failStack]

/-- A present index with insufficient gas fails before lookup. -/
theorem blobHash_gas (s : State) (x : Word) (xs : List Word)
    (items : s.stack.val = x :: xs) (gas : s.gas < 3) :
    blobHash s = .exception s .outOfGas := by
  let rest : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  simp [blobHash, pop, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful lookup replaces the index and preserves all other frame fields. -/
theorem blobHash_success (s t : State) (x : Word) (xs : List Word)
    (items : s.stack.val = x :: xs) (gas : 3 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 3)
      (Environment.blobHash s.context.environment x :: xs)) :
    blobHash s = .continue t := by
  let rest : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  let final : Stack := ⟨Environment.blobHash s.context.environment x :: xs,
    by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have push : rest.push (Environment.blobHash s.context.environment x) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 3) final fields
  simp only [blobHash, pop, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- Observed helper success determines its operand, gas, and every output field. -/
theorem blobHash_actual (s t : State) (run : blobHash s = .continue t) :
    ∃ x xs, s.stack.val = x :: xs ∧ 3 ≤ s.gas ∧
      Advances s t (s.pc + 1) (s.gas - 3)
        (Environment.blobHash s.context.environment x :: xs) := by
  cases items : s.stack.val with
  | nil =>
    have bad := blobHash_empty s items
    rw [run] at bad
    cases bad
  | cons x xs =>
    have gas : 3 ≤ s.gas := by
      by_cases h : 3 ≤ s.gas
      · exact h
      have bad := blobHash_gas s x xs items (by omega)
      rw [run] at bad
      cases bad
    let stack : Stack := ⟨Environment.blobHash s.context.environment x :: xs,
      by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
    let target : State := { s with stack, pc := s.pc + 1, gas := s.gas - 3 }
    have fields : Advances s target (s.pc + 1) (s.gas - 3)
        (Environment.blobHash s.context.environment x :: xs) := by simp [Advances, target, stack]
    have ok := blobHash_success s target x xs items gas fields
    rw [run] at ok
    have eq : t = target := Outcome.continue.inj ok
    exact ⟨x, xs, rfl, gas, eq ▸ fields⟩

/-- An actual BLOBHASH instruction inherits the helper's full converse. -/
theorem step_blobHash_actual (s t : State) (at_ : At s (some .blobhash))
    (run : step s = .continue t) :
    ∃ x xs, s.stack.val = x :: xs ∧ 3 ≤ s.gas ∧
      Advances s t (s.pc + 1) (s.gas - 3)
        (Environment.blobHash s.context.environment x :: xs) := by
  obtain ⟨bounds, decoded⟩ := at_
  have helper : blobHash s = .continue t := by
    simpa [step, bounds, decoded] using run
  exact blobHash_actual s t helper

/-- An empty stack fails before the gas check for every helper invocation. -/
theorem blockHash_empty (s : State) (history : Environment.BlockHistory) (empty : s.stack.val = []) :
    blockHash s history = .exception s .stackUnderflow := by
  have pop : s.stack.pop = .error .underflow := (Proofs.Stack.pop_underflow_iff _).mpr empty
  simp [blockHash, pop, failStack]

/-- A present index with insufficient gas fails before lookup. -/
theorem blockHash_gas (s : State) (history : Environment.BlockHistory) (x : Word) (xs : List Word)
    (items : s.stack.val = x :: xs) (gas : s.gas < 20) :
    blockHash s history = .exception s .outOfGas := by
  let rest : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  simp [blockHash, pop, charge, Gas.charge, Nat.not_le.mpr gas]

/-- A successful lookup replaces the index and preserves all other frame fields. -/
theorem blockHash_success (s t : State) (history : Environment.BlockHistory) (x : Word) (xs : List Word)
    (items : s.stack.val = x :: xs) (gas : 20 ≤ s.gas)
    (fields : Advances s t (s.pc + 1) (s.gas - 20)
      (Environment.blockHash history s.context.environment.number x :: xs)) :
    blockHash s history = .continue t := by
  let rest : Stack := ⟨xs, by have b := s.stack.property; rw [items] at b; simp at b; omega⟩
  let final : Stack := ⟨Environment.blockHash history s.context.environment.number x :: xs,
    by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
  have pop : s.stack.pop = .ok (x, rest) := (Proofs.Stack.pop_ok_iff _ _ _).mpr items
  have push : rest.push (Environment.blockHash history s.context.environment.number x) = .ok final :=
    (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨by change xs.length < 1024; have b := s.stack.property; rw [items] at b; simp at b; omega, rfl⟩
  have update := advances_eq s t (s.pc + 1) (s.gas - 20) final fields
  simp only [blockHash, pop, charge, Gas.charge, ite_eq_left gas, push]
  rw [update]

/-- Observed helper success determines its operand, gas, and every output field. -/
theorem blockHash_actual (s t : State) (history : Environment.BlockHistory) (run : blockHash s history = .continue t) :
    ∃ x xs, s.stack.val = x :: xs ∧ 20 ≤ s.gas ∧
      Advances s t (s.pc + 1) (s.gas - 20)
        (Environment.blockHash history s.context.environment.number x :: xs) := by
  cases items : s.stack.val with
  | nil =>
    have bad := blockHash_empty s history items
    rw [run] at bad
    cases bad
  | cons x xs =>
    have gas : 20 ≤ s.gas := by
      by_cases h : 20 ≤ s.gas
      · exact h
      have bad := blockHash_gas s history x xs items (by omega)
      rw [run] at bad
      cases bad
    let stack : Stack := ⟨Environment.blockHash history s.context.environment.number x :: xs,
      by have b := s.stack.property; rw [items] at b; simp at b ⊢; omega⟩
    let target : State := { s with stack, pc := s.pc + 1, gas := s.gas - 20 }
    have fields : Advances s target (s.pc + 1) (s.gas - 20)
        (Environment.blockHash history s.context.environment.number x :: xs) := by simp [Advances, target, stack]
    have ok := blockHash_success s target history x xs items gas fields
    rw [run] at ok
    have eq : t = target := Outcome.continue.inj ok
    exact ⟨x, xs, rfl, gas, eq ▸ fields⟩

/-- Actual opcode success determines the full frame without assumed output fields. -/
theorem step_blockHash_actual (s t : State) (at_ : At s (some .blockhash))
    (run : step s = .continue t) :
    ∃ x xs, s.stack.val = x :: xs ∧ 20 ≤ s.gas ∧
      Advances s t (s.pc + 1) (s.gas - 20)
        (Environment.blockHash s.context.environment.blockHashes s.context.environment.number x :: xs) := by
  obtain ⟨bounds, decoded⟩ := at_
  have helper : blockHash s s.context.environment.blockHashes = .continue t := by
    simpa [step, bounds, decoded] using run
  exact blockHash_actual s t s.context.environment.blockHashes helper

/-- Actual successful execution exposes the source bytes of an available hash. -/
theorem step_blockHash_codec (s t : State) (at_ : At s (some .blockhash))
    (run : step s = .continue t) (x : Word) (xs : List Word)
    (items : s.stack.val = x :: xs) (bytes : ByteArray)
    (window : x.toNat < s.context.environment.number.toNat ∧
      s.context.environment.number.toNat ≤ x.toNat + 256)
    (available : s.context.environment.number.toNat - x.toNat ≤ s.context.environment.blockHashes.length)
    (codec : Word.ofBytesBE bytes = .ok
      (s.context.environment.blockHashes[s.context.environment.blockHashes.length -
        (s.context.environment.number.toNat - x.toNat)]' (by omega))) :
    ∃ w, t.stack.val = w :: xs ∧ w.toBytesBE = bytes := by
  obtain ⟨y, ys, input, gas, fields⟩ := step_blockHash_actual s t at_ run
  rw [items] at input
  cases input
  refine ⟨_, fields.2.2.2.2.1, ?_⟩
  exact Environment.blockHash_codec _ _ _ bytes window available codec

end EthLib.EVM.Frame
