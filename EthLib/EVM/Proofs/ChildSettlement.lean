module

public import EthLib.EVM.ChildSettlement
public import EthLib.EVM.Proofs.TransactionStateReference

@[expose] public section
namespace EthLib.EVM.ChildSettlement

/-- A tooling result cannot settle a child. -/
theorem settle_unsupported (parent child : Frame.State) (op : Opcode) :
    settle parent (.unsupported child op) = .error .toolingOutcome := by
  rfl

/-- Exhaustion is a fuel boundary, not an EVM exception. -/
theorem settle_exhausted (parent child : Frame.State) :
    settle parent (.exhausted child) = .error .toolingOutcome := by
  rfl

/-- The tracker checkpoint has the independent transaction-state save relation. -/
theorem checkpoint_tracker (child : Frame.State) :
    TransactionState.Reference.Save
      (TransactionState.Reference.observe child.tracker)
      (TransactionState.Reference.observe (checkpoint child).tracker) := by
  exact TransactionState.Reference.snapshot_refines child.tracker

/-- A successful stopped child commits its top transaction checkpoint. -/
theorem stopped_commits (parent child out : Frame.State)
    (h : settle parent (.stopped child) = .ok out) :
    ∃ t, TransactionState.commit child.tracker = .ok t ∧ out.tracker = t := by
  by_cases hc : child.stateGas.committedSpill = 0
  · cases ht : TransactionState.commit child.tracker with
    | error e => simp [settle, settleChild, hc, ht] at h
    | ok t =>
      refine ⟨t, rfl, ?_⟩
      simp [settle, settleChild, hc, ht] at h
      cases h
      rfl
  · simp [settle, settleChild, hc] at h

/-- A reverted child restores the transaction checkpoint and keeps diagnostic reads. -/
theorem reverted_rolls_back (parent child out : Frame.State) (gas : Nat) (output : ByteArray)
    (h : settle parent (.reverted child gas output) = .ok out) :
    TransactionState.Reference.Rollback
      (TransactionState.Reference.observe child.tracker)
      (TransactionState.Reference.observe out.tracker) := by
  by_cases hc : child.stateGas.committedSpill = 0
  · cases ht : TransactionState.rollback child.tracker with
    | error e => simp [settle, settleChild, hc, ht] at h
    | ok t =>
      have href := TransactionState.Reference.rollback_refines child.tracker t ht
      simp [settle, settleChild, hc, ht] at h
      cases h
      exact href
  · simp [settle, settleChild, hc] at h

/-- The parent retains its execution context while a successful child is merged. -/
theorem stopped_fields (parent child out : Frame.State)
    (h : settle parent (.stopped child) = .ok out) :
    out.code = parent.code ∧ out.pc = parent.pc ∧ out.stack = parent.stack ∧
    out.memory = parent.memory ∧ out.context = parent.context ∧
    out.returnData = ByteArray.empty ∧ out.isStatic = parent.isStatic ∧
    out.logs = parent.logs ++ child.logs ∧
    out.warmAddresses = child.warmAddresses ++ parent.warmAddresses ∧
    out.warmSlots = child.warmSlots ++ parent.warmSlots ∧
    out.stateGas.baseline = parent.stateGas.baseline ∧
    out.stateGas.committedSpill = parent.stateGas.committedSpill ∧
    out.stateGas.refundCounter = parent.stateGas.refundCounter + child.stateGas.refundCounter ∧
    out.gas = parent.gas + child.gas +
      min (parent.stateGas.reservoir + child.stateGas.reservoir)
        (parent.stateGas.spilled + child.stateGas.spilled) := by
  by_cases hc : child.stateGas.committedSpill = 0
  · cases ht : TransactionState.commit child.tracker with
    | error e => simp [settle, settleChild, hc, ht] at h
    | ok t =>
      simp [settle, settleChild, hc, ht] at h
      cases h
      simp
  · simp [settle, settleChild, hc] at h

/-- A revert leaves parent warmth and logs unchanged while returning child gas and bytes. -/
theorem reverted_fields (parent child out : Frame.State) (gas : Nat) (output : ByteArray)
    (h : settle parent (.reverted child gas output) = .ok out) :
    out.code = parent.code ∧ out.pc = parent.pc ∧ out.stack = parent.stack ∧
    out.memory = parent.memory ∧ out.context = parent.context ∧
    out.returnData = output ∧ out.isStatic = parent.isStatic ∧
    out.logs = parent.logs ∧ out.warmAddresses = parent.warmAddresses ∧
    out.warmSlots = parent.warmSlots ∧ out.gas = parent.gas + (gas + child.stateGas.spilled) ∧
    out.stateGas.reservoir = parent.stateGas.reservoir + child.stateGas.baseline ∧
    out.stateGas.baseline = parent.stateGas.baseline ∧
    out.stateGas.spilled = parent.stateGas.spilled ∧
    out.stateGas.refundCounter = parent.stateGas.refundCounter ∧
    out.stateGas.committedSpill = parent.stateGas.committedSpill := by
  by_cases hc : child.stateGas.committedSpill = 0
  · cases ht : TransactionState.rollback child.tracker with
    | error e => simp [settle, settleChild, hc, ht] at h
    | ok t =>
      simp [settle, settleChild, hc, ht] at h
      cases h
      simp
  · simp [settle, settleChild, hc] at h

/-- Snapshot failure takes precedence only after the child spill check. -/
theorem stopped_missing_snapshot_iff (parent child : Frame.State) :
    settle parent (.stopped child) = .error .missingSnapshot ↔
      child.stateGas.committedSpill = 0 ∧ child.tracker.snapshots = [] := by
  by_cases hc : child.stateGas.committedSpill = 0 <;>
    cases hs : child.tracker.snapshots <;>
    simp [settle, settleChild, TransactionState.commit, hs, hc]

/-- The same checkpoint condition applies to reverted children. -/
theorem reverted_missing_snapshot_iff (parent child : Frame.State) (gas : Nat) (output : ByteArray) :
    settle parent (.reverted child gas output) = .error .missingSnapshot ↔
      child.stateGas.committedSpill = 0 ∧ child.tracker.snapshots = [] := by
  by_cases hc : child.stateGas.committedSpill = 0 <;>
    cases hs : child.tracker.snapshots <;>
    simp [settle, settleChild, TransactionState.rollback, hs, hc]

/-- An exceptional child burns its execution gas and returns no output or effects. -/
theorem exceptional_fields (parent child out : Frame.State) (reason : Frame.Exception)
    (hreason : reason ≠ .missingCode ∧ reason ≠ .missingStorageAccount)
    (h : settle parent (.exception child reason) = .ok out) :
    out.code = parent.code ∧ out.pc = parent.pc ∧ out.stack = parent.stack ∧
    out.memory = parent.memory ∧ out.context = parent.context ∧
    out.returnData = ByteArray.empty ∧ out.isStatic = parent.isStatic ∧
    out.logs = parent.logs ∧ out.warmAddresses = parent.warmAddresses ∧
    out.warmSlots = parent.warmSlots ∧ out.gas = parent.gas ∧
    out.stateGas.reservoir = parent.stateGas.reservoir + child.stateGas.baseline ∧
    out.stateGas.baseline = parent.stateGas.baseline ∧
    out.stateGas.spilled = parent.stateGas.spilled ∧
    out.stateGas.refundCounter = parent.stateGas.refundCounter ∧
    out.stateGas.committedSpill = parent.stateGas.committedSpill := by
  have hchild : settleChild parent child false 0 ByteArray.empty = .ok out := by
    cases reason <;> simp_all [settle]
  by_cases hc : child.stateGas.committedSpill = 0
  · cases ht : TransactionState.rollback child.tracker with
    | error e => simp [settleChild, hc, ht] at hchild
    | ok t =>
      simp [settleChild, hc, ht] at hchild
      cases hchild
      simp
  · simp [settleChild, hc] at hchild

/-- Frame equality follows from equality of its observable fields. -/
theorem frame_eq_of_fields (a b : Frame.State)
    (hcode : a.code = b.code) (hpc : a.pc = b.pc) (hstack : a.stack = b.stack)
    (hgas : a.gas = b.gas) (hmem : a.memory = b.memory) (hctx : a.context = b.context)
    (hdata : a.returnData = b.returnData) (htx : a.tracker = b.tracker)
    (ha : a.warmAddresses = b.warmAddresses) (hs : a.warmSlots = b.warmSlots)
    (hstatic : a.isStatic = b.isStatic) (hmeter : a.stateGas = b.stateGas)
    (hlogs : a.logs = b.logs) : a = b := by
  cases a
  cases b
  simp_all

/-- Fieldwise checkpoint observations, including the independent tracker save. -/
def CheckpointFields (before after : Frame.State) : Prop :=
  after.code = before.code ∧ after.pc = before.pc ∧ after.stack = before.stack ∧
  after.gas = before.gas ∧ after.memory = before.memory ∧ after.context = before.context ∧
  after.returnData = before.returnData ∧ after.warmAddresses = before.warmAddresses ∧
  after.warmSlots = before.warmSlots ∧ after.isStatic = before.isStatic ∧
  after.stateGas = before.stateGas ∧ after.logs = before.logs ∧
  after.tracker.parent = before.tracker.parent ∧ after.tracker.writes = before.tracker.writes ∧
  after.tracker.accountReads = before.tracker.accountReads ∧
  after.tracker.storageReads = before.tracker.storageReads ∧
  after.tracker.createdAccounts = before.tracker.createdAccounts ∧
  after.tracker.snapshots = before.tracker.writes :: before.tracker.snapshots ∧
  TransactionState.Reference.Save (TransactionState.Reference.observe before.tracker)
    (TransactionState.Reference.observe after.tracker)

/-- The checkpoint is exactly the frame satisfying the independent field observations. -/
theorem checkpoint_iff (before after : Frame.State) :
    checkpoint before = after ↔ CheckpointFields before after := by
  constructor
  · intro h
    subst after
    simp [CheckpointFields, checkpoint, TransactionState.snapshot,
      TransactionState.Reference.Save, TransactionState.Reference.Retained,
      TransactionState.Reference.observe]
  · intro h
    rcases h with ⟨hc, hp, hs, hg, hm, hx, hd, ha, hw, hi, hmeter, hl, ht⟩
    apply frame_eq_of_fields <;> simp [checkpoint] <;> try (first | exact hc.symm | exact hp.symm | exact hs.symm | exact hg.symm | exact hm.symm | exact hx.symm | exact hd.symm | exact ha.symm | exact hw.symm | exact hi.symm | exact hmeter.symm | exact hl.symm)
    cases before
    cases after
    cases ‹TransactionState.State›
    cases ‹TransactionState.State›
    simp_all [TransactionState.snapshot]

/-- Exactly these runner results are incomplete tooling outcomes. -/
def ToolingResult : Runner.Result → Prop
  | .unsupported _ _ | .exhausted _ => True
  | .exception _ .missingCode | .exception _ .missingStorageAccount => True
  | _ => False

/-- Settling a protocol terminal child never manufactures a tooling outcome. -/
theorem settleChild_not_tooling (p c : Frame.State) (success : Bool)
    (gas : Nat) (bytes : ByteArray) :
    settleChild p c success gas bytes ≠ .error .toolingOutcome := by
  by_cases hc : c.stateGas.committedSpill = 0 <;> cases success <;>
    cases hs : c.tracker.snapshots <;>
    simp [settleChild, hc, TransactionState.commit, TransactionState.rollback, hs]

/-- The tooling error identifies precisely unsupported, exhausted, or incomplete-world results. -/
theorem settle_tooling_iff (p : Frame.State) (r : Runner.Result) :
    settle p r = .error .toolingOutcome ↔ ToolingResult r := by
  cases r with
  | stopped c => simp [settle, ToolingResult, settleChild_not_tooling]
  | returned c bytes => simp [settle, ToolingResult, settleChild_not_tooling]
  | reverted c gas bytes => simp [settle, ToolingResult, settleChild_not_tooling]
  | exception c reason => cases reason <;> simp [settle, ToolingResult, settleChild_not_tooling]
  | unsupported c op => simp [settle, ToolingResult]
  | exhausted c => simp [settle, ToolingResult]

/-- Independent observations of a terminal child incorporation. -/
def Effect (parent child out : Frame.State) (success : Bool) (gas : Nat) (output : ByteArray) : Prop :=
  ∃ saved rest,
    child.stateGas.committedSpill = 0 ∧ child.tracker.snapshots = saved :: rest ∧
    out.code = parent.code ∧ out.pc = parent.pc ∧ out.stack = parent.stack ∧
    out.memory = parent.memory ∧ out.context = parent.context ∧ out.returnData = output ∧
    out.isStatic = parent.isStatic ∧
    out.tracker.parent = child.tracker.parent ∧
    out.tracker.writes = (if success then child.tracker.writes else saved) ∧
    out.tracker.accountReads = child.tracker.accountReads ∧
    out.tracker.storageReads = child.tracker.storageReads ∧
    out.tracker.createdAccounts = child.tracker.createdAccounts ∧ out.tracker.snapshots = rest ∧
    out.logs = (if success then parent.logs ++ child.logs else parent.logs) ∧
    out.warmAddresses = (if success then child.warmAddresses ++ parent.warmAddresses else parent.warmAddresses) ∧
    out.warmSlots = (if success then child.warmSlots ++ parent.warmSlots else parent.warmSlots) ∧
    let reservoir := parent.stateGas.reservoir + (if success then child.stateGas.reservoir else child.stateGas.baseline)
    let spill := parent.stateGas.spilled + (if success then child.stateGas.spilled else 0)
    let repayment := if success then min reservoir spill else 0
    out.gas = parent.gas + gas + repayment ∧
    out.stateGas.reservoir = reservoir - repayment ∧
    out.stateGas.baseline = parent.stateGas.baseline ∧
    out.stateGas.refundCounter = parent.stateGas.refundCounter +
      (if success then child.stateGas.refundCounter else 0) ∧
    out.stateGas.spilled = spill - repayment ∧
    out.stateGas.committedSpill = parent.stateGas.committedSpill

/-- Terminal incorporation satisfies the independent observations. -/
theorem settleChild_effect (parent child out : Frame.State) (success : Bool)
    (gas : Nat) (output : ByteArray)
    (h : settleChild parent child success gas output = .ok out) :
    Effect parent child out success gas output := by
  by_cases hc : child.stateGas.committedSpill = 0
  · cases hs : child.tracker.snapshots with
    | nil => cases success <;> simp [settleChild, hc, TransactionState.commit, TransactionState.rollback, hs] at h
    | cons saved rest =>
      cases success <;>
        simp [settleChild, hc, TransactionState.commit, TransactionState.rollback, hs] at h <;>
        cases h <;>
        simp [Effect, hc, hs]
  · simp [settleChild, hc] at h

/-- The independent observations determine the actual terminal result. -/
theorem effect_settleChild (parent child out : Frame.State) (success : Bool)
    (gas : Nat) (output : ByteArray)
    (h : Effect parent child out success gas output) :
    settleChild parent child success gas output = .ok out := by
  rcases h with ⟨saved, rest, hc, hs, h⟩
  cases success <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.sub_zero] at h
  all_goals
    simp [settleChild, hc, TransactionState.commit, TransactionState.rollback, hs]
    symm
    apply frame_eq_of_fields <;> simp_all
    all_goals
      cases out <;> cases ‹TransactionState.State› <;> cases ‹Frame.StateGas› <;> simp_all


/-- Exact all-input equivalence with the fieldwise specification. -/
theorem settleChild_iff (parent child out : Frame.State) (success : Bool)
    (gas : Nat) (output : ByteArray) :
    settleChild parent child success gas output = .ok out ↔
      Effect parent child out success gas output :=
  ⟨settleChild_effect parent child out success gas output,
   effect_settleChild parent child out success gas output⟩

/-- STOP commits the child effects and produces empty output. -/
theorem stopped_iff (parent child out : Frame.State) :
    settle parent (.stopped child) = .ok out ↔
      Effect parent child out true child.gas ByteArray.empty :=
  settleChild_iff parent child out true child.gas ByteArray.empty

/-- RETURN commits the child effects and returns its output. -/
theorem returned_iff (parent child out : Frame.State) (output : ByteArray) :
    settle parent (.returned child output) = .ok out ↔
      Effect parent child out true child.gas output :=
  settleChild_iff parent child out true child.gas output

/-- REVERT restores spill before returning execution gas and output. -/
theorem reverted_iff (parent child out : Frame.State) (gas : Nat) (output : ByteArray) :
    settle parent (.reverted child gas output) = .ok out ↔
      Effect parent child out false (gas + child.stateGas.spilled) output :=
  settleChild_iff parent child out false (gas + child.stateGas.spilled) output

/-- Exceptional termination burns execution gas and produces no output. -/
theorem exceptional_iff (parent child out : Frame.State) (reason : Frame.Exception)
    (hreason : reason ≠ .missingCode ∧ reason ≠ .missingStorageAccount) :
    settle parent (.exception child reason) = .ok out ↔
      Effect parent child out false 0 ByteArray.empty := by
  cases reason <;> simp_all [settle, settleChild_iff]

/-- Incomplete world diagnostics are not settled as protocol exceptions. -/
theorem missing_code_tooling (parent child : Frame.State) :
    settle parent (.exception child .missingCode) = .error .toolingOutcome := rfl

/-- A missing storage account is a state-validity diagnostic. -/
theorem missing_account_tooling (parent child : Frame.State) :
    settle parent (.exception child .missingStorageAccount) = .error .toolingOutcome := rfl

/-- A nonzero committed child spill is rejected before a checkpoint is inspected. -/
theorem settleChild_committed_spill_iff (parent child : Frame.State) (success : Bool)
    (gas : Nat) (output : ByteArray) :
    settleChild parent child success gas output = .error .committedChildSpill ↔
      child.stateGas.committedSpill ≠ 0 := by
  by_cases hc : child.stateGas.committedSpill = 0
  · cases success <;> cases hs : child.tracker.snapshots <;>
      simp [settleChild, hc, TransactionState.commit, TransactionState.rollback, hs]
  · simp [settleChild, hc]

/-- A missing checkpoint is reported for either protocol fate. -/
theorem settleChild_missing_snapshot_iff (parent child : Frame.State) (success : Bool)
    (gas : Nat) (output : ByteArray) :
    settleChild parent child success gas output = .error .missingSnapshot ↔
      child.stateGas.committedSpill = 0 ∧ child.tracker.snapshots = [] := by
  by_cases hc : child.stateGas.committedSpill = 0 <;> cases success <;>
    cases hs : child.tracker.snapshots <;>
    simp [settleChild, hc, TransactionState.commit, TransactionState.rollback, hs]

/-- The duplicate-tolerant tracker observation follows the existing commit specification. -/
theorem returned_tracker_refines (parent child out : Frame.State) (output : ByteArray)
    (h : settle parent (.returned child output) = .ok out) :
    TransactionState.Reference.Commit
      (TransactionState.Reference.observe child.tracker)
      (TransactionState.Reference.observe out.tracker) := by
  by_cases hc : child.stateGas.committedSpill = 0
  · cases ht : TransactionState.commit child.tracker with
    | error e => simp [settle, settleChild, hc, ht] at h
    | ok t =>
      have href := TransactionState.Reference.commit_refines child.tracker t ht
      simp [settle, settleChild, hc, ht] at h
      cases h
      exact href
  · simp [settle, settleChild, hc] at h

/-- On success, a warm address belongs to the result exactly when either frame had it. -/
theorem returned_warm_membership (parent child out : Frame.State) (output : ByteArray)
    (address : World.Address) (h : settle parent (.returned child output) = .ok out) :
    address ∈ out.warmAddresses ↔ address ∈ child.warmAddresses ∨ address ∈ parent.warmAddresses := by
  have effect := (returned_iff parent child out output).mp h
  rcases effect with ⟨saved, rest, hc, hs, h⟩
  simp only [↓reduceIte] at h
  rw [h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, List.mem_append]

end EthLib.EVM.ChildSettlement
