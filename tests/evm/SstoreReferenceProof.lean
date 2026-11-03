import EthLib.EVM.Proofs.Runner.Sstore
import Aesop

open EthLib.EVM
namespace SstoreReferenceConsumer

theorem all_outcomes (s : Frame.State) (out : Frame.Outcome) :
    Frame.sstore s = out ↔ Frame.SstoreLocal s out := Frame.sstore_iff_local s out

theorem success (s ready charged paid result : Frame.State) (first rest : Stack) (key value : Word)
    (cost stateCost : Nat) (static : s.isStatic = false) (items : s.stack.val = key :: first.val)
    (items' : first.val = value :: rest.val) (gas : 2301 ≤ s.gas)
    (fields : Frame.SstoreReady s ready rest key value cost stateCost) (enough : cost ≤ ready.gas)
    (execution : Frame.SstoreExecutionFields ready charged cost)
    (charge : Frame.SstoreChargeFields charged paid stateCost) (present : Frame.SstoreAccount paid ≠ none)
    (written : Frame.SstoreWriteFields paid result key value true) :
    Frame.sstore s = .continue result :=
  (Frame.sstore_iff_local s _).mpr (.sstoreSuccess s ready charged paid result first rest key value cost stateCost
    static items items' gas fields enough execution charge present written)

theorem success_converse (s result : Frame.State) (run : Frame.sstore s = .continue result) :
    ∃ (ready charged paid : Frame.State) (first rest : Stack) (key value : Word) (cost stateCost : Nat),
      s.isStatic = false ∧ s.stack.val = key :: first.val ∧ first.val = value :: rest.val ∧
      2301 ≤ s.gas ∧ Frame.SstoreReady s ready rest key value cost stateCost ∧ cost ≤ ready.gas ∧
      Frame.SstoreExecutionFields ready charged cost ∧ Frame.SstoreChargeFields charged paid stateCost ∧
      Frame.SstoreAccount paid ≠ none ∧ Frame.SstoreWriteFields paid result key value true := by
  have rule := (Frame.sstore_iff_local s _).mp run
  cases rule
  all_goals aesop


theorem second_underflow (s : Frame.State) (rest : Stack) (key : Word)
    (static : s.isStatic = false) (items : s.stack.val = key :: rest.val) (empty : rest.val = []) :
    Frame.sstore s = .exception { s with stack := rest } .stackUnderflow :=
  (Frame.sstore_iff_local s _).mpr (.sstoreSecondUnderflow s rest key static items empty)

theorem exception_converse (s input : Frame.State) (reason : Frame.Exception)
    (run : Frame.sstore s = .exception input reason) : Frame.SstoreLocal s (.exception input reason) :=
  (Frame.sstore_iff_local s _).mp run


-- Each exceptional result exposes its exact independent failed premises.
theorem static_converse (s input : Frame.State)
    (run : Frame.sstore s = .exception input .writeInStaticContext) :
    s.isStatic = true ∧ input = s := by
  have rule := (Frame.sstore_iff_local s _).mp run
  cases rule
  all_goals aesop

theorem underflow_converse (s input : Frame.State)
    (run : Frame.sstore s = .exception input .stackUnderflow) :
    (s.isStatic = false ∧ s.stack.val = [] ∧ input = s) ∨
    (∃ (rest : Stack) (key : Word), s.isStatic = false ∧ s.stack.val = key :: rest.val ∧
      rest.val = [] ∧ input = { s with stack := rest }) := by
  have rule := (Frame.sstore_iff_local s _).mp run
  cases rule
  all_goals aesop

theorem out_of_gas_converse (s input : Frame.State)
    (run : Frame.sstore s = .exception input .outOfGas) :
    (∃ (first rest : Stack) (key value : Word), s.isStatic = false ∧
      s.stack.val = key :: first.val ∧ first.val = value :: rest.val ∧ s.gas < 2301 ∧
      input = { s with stack := rest }) ∨
    (∃ (ready : Frame.State) (first rest : Stack) (key value : Word) (cost stateCost : Nat),
      s.isStatic = false ∧ s.stack.val = key :: first.val ∧ first.val = value :: rest.val ∧
      2301 ≤ s.gas ∧ Frame.SstoreReady s ready rest key value cost stateCost ∧ ready.gas < cost ∧ input = ready) ∨
    (∃ (ready charged : Frame.State) (first rest : Stack) (key value : Word) (cost stateCost : Nat),
      s.isStatic = false ∧ s.stack.val = key :: first.val ∧ first.val = value :: rest.val ∧
      2301 ≤ s.gas ∧ Frame.SstoreReady s ready rest key value cost stateCost ∧ cost ≤ ready.gas ∧
      Frame.SstoreExecutionFields ready charged cost ∧ charged.stateGas.reservoir + charged.gas < stateCost ∧ input = charged) := by
  have rule := (Frame.sstore_iff_local s _).mp run
  cases rule
  all_goals aesop

theorem missing_converse (s input : Frame.State)
    (run : Frame.sstore s = .exception input .missingStorageAccount) :
    ∃ (ready charged paid : Frame.State) (first rest : Stack) (key value : Word) (cost stateCost : Nat),
      s.isStatic = false ∧ s.stack.val = key :: first.val ∧ first.val = value :: rest.val ∧
      2301 ≤ s.gas ∧ Frame.SstoreReady s ready rest key value cost stateCost ∧ cost ≤ ready.gas ∧
      Frame.SstoreExecutionFields ready charged cost ∧ Frame.SstoreChargeFields charged paid stateCost ∧
      Frame.SstoreAccount paid = none ∧ Frame.SstoreWriteFields paid input key value false := by
  have rule := (Frame.sstore_iff_local s _).mp run
  cases rule
  all_goals aesop

theorem execution_gas (s ready : Frame.State) (first rest : Stack) (key value : Word) (cost stateCost : Nat)
    (static : s.isStatic = false) (items : s.stack.val = key :: first.val) (items' : first.val = value :: rest.val)
    (gas : 2301 ≤ s.gas) (fields : Frame.SstoreReady s ready rest key value cost stateCost) (low : ready.gas < cost) :
    Frame.sstore s = .exception ready .outOfGas :=
  (Frame.sstore_iff_local s _).mpr (.sstoreExecutionGas s ready first rest key value cost stateCost static items items' gas fields low)

theorem state_gas (s ready charged : Frame.State) (first rest : Stack) (key value : Word) (cost stateCost : Nat)
    (static : s.isStatic = false) (items : s.stack.val = key :: first.val) (items' : first.val = value :: rest.val)
    (gas : 2301 ≤ s.gas) (fields : Frame.SstoreReady s ready rest key value cost stateCost) (enough : cost ≤ ready.gas)
    (execution : Frame.SstoreExecutionFields ready charged cost) (low : charged.stateGas.reservoir + charged.gas < stateCost) :
    Frame.sstore s = .exception charged .outOfGas :=
  (Frame.sstore_iff_local s _).mpr (.sstoreStateGas s ready charged first rest key value cost stateCost static items items' gas fields enough execution low)

theorem missing (s ready charged paid result : Frame.State) (first rest : Stack) (key value : Word) (cost stateCost : Nat)
    (static : s.isStatic = false) (items : s.stack.val = key :: first.val) (items' : first.val = value :: rest.val)
    (gas : 2301 ≤ s.gas) (fields : Frame.SstoreReady s ready rest key value cost stateCost) (enough : cost ≤ ready.gas)
    (execution : Frame.SstoreExecutionFields ready charged cost) (charge : Frame.SstoreChargeFields charged paid stateCost)
    (absent : Frame.SstoreAccount paid = none) (written : Frame.SstoreWriteFields paid result key value false) :
    Frame.sstore s = .exception result .missingStorageAccount :=
  (Frame.sstore_iff_local s _).mpr (.sstoreMissing s ready charged paid result first rest key value cost stateCost static items items' gas fields enough execution charge absent written)

theorem mixed (s t u : Frame.State) (rest : Stack) (key : Word)
    (code : s.code = Runner.SstoreProgram.program) (pc : s.pc = 0)
    (store : Frame.SstoreLocal s (.continue t)) (items : t.stack.val = key :: rest.val)
    (gas : Frame.SloadCost t key ≤ t.gas)
    (load : Frame.Advances { t with warmSlots := Frame.SloadWarm t key, tracker := Frame.SloadRead t key }
      u (t.pc + 1) (t.gas - Frame.SloadCost t key) (Frame.SloadValue t key :: rest.val)) :
    Runner.run 3 s = .stopped { u with pc := 3 } ∧
      u.tracker = Frame.SloadRead t key ∧ u.warmSlots = Frame.SloadWarm t key :=
  Runner.SstoreProgram.run_mixed s t u rest key code pc store items gas load


-- Construct both runner transitions from the independent SSTORE conditions.
theorem mixed_constructed (s ready charged paid : Frame.State) (first rest tail : Stack)
    (key value nextKey : Word) (cost stateCost : Nat)
    (code : s.code = Runner.SstoreProgram.program) (pc : s.pc = 0)
    (static : s.isStatic = false) (items : s.stack.val = key :: first.val)
    (items' : first.val = value :: rest.val) (next : rest.val = nextKey :: tail.val)
    (gas : 2301 ≤ s.gas) (fields : Frame.SstoreReady s ready rest key value cost stateCost)
    (enough : cost ≤ ready.gas) (execution : Frame.SstoreExecutionFields ready charged cost)
    (charge : Frame.SstoreChargeFields charged paid stateCost) (present : Frame.SstoreAccount paid ≠ none)
    (readGas : Frame.SloadCost paid nextKey ≤ paid.gas) :
    ∃ (t u : Frame.State), Runner.run 3 s = .stopped { u with pc := 3 } ∧
      t = Frame.sstoreWriteWitness paid key value true ∧
      u.tracker = Frame.SloadRead t nextKey ∧ u.warmSlots = Frame.SloadWarm t nextKey ∧
      u.stack.val = Frame.SloadValue t nextKey :: tail.val := by
  let t := Frame.sstoreWriteWitness paid key value true
  have write := Frame.sstore_write_witness_success paid key value present
  have written : Frame.SstoreWriteFields paid t key value true := by
    simpa [t, Frame.sstoreWriteWitness] using Frame.sstore_write_success_fields paid key value t.tracker write
  have store : Frame.SstoreLocal s (.continue t) :=
    .sstoreSuccess s ready charged paid t first rest key value cost stateCost static items items' gas fields enough execution charge present written
  have restStack : t.stack = rest := by
    rcases fields with ⟨read, _, _, _, _, _, readFields, _, creditFields, _⟩
    have a : read.stack = rest := readFields.2.2.1
    have b : ready.stack = read.stack := creditFields.1.2.2.1
    have c : charged.stack = ready.stack := execution.1.2.2.1
    have d : paid.stack = charged.stack := charge.1.2.2.1
    have e : t.stack = paid.stack := written.2.2.1
    exact e.trans (d.trans (c.trans (b.trans a)))
  have nextItems : t.stack.val = nextKey :: tail.val := by simpa [restStack] using next
  have bound : (Frame.SloadValue t nextKey :: tail.val).length ≤ 1024 := by
    have h := rest.property
    rw [next] at h
    simpa using h
  let stack : Stack := ⟨Frame.SloadValue t nextKey :: tail.val, bound⟩
  let u : Frame.State := { t with stack, tracker := Frame.SloadRead t nextKey, warmSlots := Frame.SloadWarm t nextKey, pc := t.pc + 1, gas := t.gas - Frame.SloadCost t nextKey }
  have load : Frame.Advances { t with warmSlots := Frame.SloadWarm t nextKey, tracker := Frame.SloadRead t nextKey }
      u (t.pc + 1) (t.gas - Frame.SloadCost t nextKey) (Frame.SloadValue t nextKey :: tail.val) := by
    simp [Frame.Advances, u, stack]
  have tgas : Frame.SloadCost t nextKey ≤ t.gas := by simpa [t, Frame.sstoreWriteWitness, Frame.SloadCost] using readGas
  have run := Runner.SstoreProgram.run_mixed s t u tail nextKey code pc store nextItems tgas load
  exact ⟨t, u, run.1, rfl, run.2.1, run.2.2, rfl⟩

#print axioms all_outcomes
#print axioms success
#print axioms success_converse
#print axioms second_underflow
#print axioms exception_converse
#print axioms static_converse
#print axioms underflow_converse
#print axioms out_of_gas_converse
#print axioms missing_converse
#print axioms execution_gas
#print axioms state_gas
#print axioms missing
#print axioms mixed
#print axioms mixed_constructed
end SstoreReferenceConsumer
