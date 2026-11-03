import EthLib.EVM.Proofs.ChildSettlement

open EthLib.EVM
open EthLib.EVM.ChildSettlement

-- Extract actual tracker, output and log conditions from a settled RETURN.
theorem returned_consumer (p c out : Frame.State) (bytes : ByteArray)
    (h : settle p (.returned c bytes) = .ok out) :
    out.returnData = bytes ∧ out.logs = p.logs ++ c.logs ∧
    out.tracker.writes = c.tracker.writes ∧
    out.tracker.accountReads = c.tracker.accountReads ∧
    out.tracker.storageReads = c.tracker.storageReads := by
  have effect := (returned_iff p c out bytes).mp h
  rcases effect with ⟨saved, rest, hc, hs, h⟩
  simp only [↓reduceIte] at h
  exact ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.1⟩

-- Apply the opposite direction for each protocol outcome.
theorem return_converse (p c out : Frame.State) (bytes : ByteArray)
    (h : Effect p c out true c.gas bytes) : settle p (.returned c bytes) = .ok out :=
  (returned_iff p c out bytes).mpr h

theorem stop_converse (p c out : Frame.State)
    (h : Effect p c out true c.gas ByteArray.empty) : settle p (.stopped c) = .ok out :=
  (stopped_iff p c out).mpr h

theorem revert_converse (p c out : Frame.State) (gas : Nat) (bytes : ByteArray)
    (h : Effect p c out false (gas + c.stateGas.spilled) bytes) :
    settle p (.reverted c gas bytes) = .ok out :=
  (reverted_iff p c out gas bytes).mpr h

theorem exception_converse (p c out : Frame.State) (reason : Frame.Exception)
    (hreason : reason ≠ .missingCode ∧ reason ≠ .missingStorageAccount)
    (h : Effect p c out false 0 ByteArray.empty) :
    settle p (.exception c reason) = .ok out :=
  (exceptional_iff p c out reason hreason).mpr h

-- Feed a real bounded runner result into settlement, retaining its output.
theorem run_return_consumer (fuel : Nat) (p initial child out : Frame.State) (bytes : ByteArray)
    (hrun : Runner.run fuel initial = .returned child bytes)
    (h : settle p (Runner.run fuel initial) = .ok out) :
    out.returnData = bytes ∧ out.logs = p.logs ++ child.logs ∧
    out.tracker.writes = child.tracker.writes := by
  rw [hrun] at h
  obtain ⟨hdata, hlogs, hwrites, _, _⟩ := returned_consumer p child out bytes h
  exact ⟨hdata, hlogs, hwrites⟩

-- A child with a real saved checkpoint and an uncommitted meter can settle.
theorem constructed_return (p c : Frame.State) (bytes : ByteArray)
    (saved : TransactionState.Snapshot) (rest : List TransactionState.Snapshot)
    (hs : c.tracker.snapshots = saved :: rest) (hc : c.stateGas.committedSpill = 0) :
    ∃ out, settle p (.returned c bytes) = .ok out ∧
      out.returnData = bytes ∧ out.logs = p.logs ++ c.logs ∧
      out.tracker.writes = c.tracker.writes := by
  have hex : ∃ out, settle p (.returned c bytes) = .ok out := by
    simp [settle, settleChild, hc, TransactionState.commit, hs]
  obtain ⟨out, h⟩ := hex
  obtain ⟨hdata, hlogs, hwrites, _, _⟩ := returned_consumer p c out bytes h
  exact ⟨out, h, hdata, hlogs, hwrites⟩

-- A failed child restores the saved writes while retaining the child's reads.
theorem constructed_revert (p c : Frame.State) (gas : Nat) (bytes : ByteArray)
    (saved : TransactionState.Snapshot) (rest : List TransactionState.Snapshot)
    (hs : c.tracker.snapshots = saved :: rest) (hc : c.stateGas.committedSpill = 0) :
    ∃ out, settle p (.reverted c gas bytes) = .ok out ∧
      out.tracker.writes = saved ∧ out.tracker.accountReads = c.tracker.accountReads ∧
      out.returnData = bytes ∧ out.gas = p.gas + (gas + c.stateGas.spilled) := by
  have hex : ∃ out, settle p (.reverted c gas bytes) = .ok out := by
    simp [settle, settleChild, hc, TransactionState.rollback, hs]
  obtain ⟨out, h⟩ := hex
  have effect := (reverted_iff p c out gas bytes).mp h
  obtain ⟨saved', rest', _, hs', heffect⟩ := effect
  have hid : saved' = saved := by rw [hs] at hs'; exact (List.cons.inj hs').1.symm
  subst saved'
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.sub_zero] at heffect
  have hf := reverted_fields p c out gas bytes h
  exact ⟨out, h, heffect.2.2.2.2.2.2.2.2.1,
    heffect.2.2.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.1,
    hf.2.2.2.2.2.2.2.2.2.2.1⟩

-- STOP retains the parent's code and appends the child's logs.
theorem stop_forward (p c out : Frame.State)
    (h : settle p (.stopped c) = .ok out) : out.code = p.code ∧ out.logs = p.logs ++ c.logs := by
  have fields := stopped_fields p c out h
  exact ⟨fields.1, fields.2.2.2.2.2.2.2.1⟩

-- REVERT and exceptional halts preserve the parent's log list and warmth.
theorem revert_forward (p c out : Frame.State) (gas : Nat) (bytes : ByteArray)
    (h : settle p (.reverted c gas bytes) = .ok out) :
    out.logs = p.logs ∧ out.warmAddresses = p.warmAddresses ∧ out.returnData = bytes := by
  have fields := reverted_fields p c out gas bytes h
  exact ⟨fields.2.2.2.2.2.2.2.1, fields.2.2.2.2.2.2.2.2.1, fields.2.2.2.2.2.1⟩

theorem exception_forward (p c out : Frame.State) (reason : Frame.Exception)
    (hreason : reason ≠ .missingCode ∧ reason ≠ .missingStorageAccount)
    (h : settle p (.exception c reason) = .ok out) :
    out.gas = p.gas ∧ out.returnData = ByteArray.empty ∧ out.logs = p.logs := by
  have fields := exceptional_fields p c out reason hreason h
  exact ⟨fields.2.2.2.2.2.2.2.2.2.2.1, fields.2.2.2.2.2.1, fields.2.2.2.2.2.2.2.1⟩

-- Both directions expose the caller-side error priorities.
theorem spill_error_consumer (p c : Frame.State) (gas : Nat) (bytes : ByteArray) :
    settleChild p c true gas bytes = .error .committedChildSpill ↔
      c.stateGas.committedSpill ≠ 0 := settleChild_committed_spill_iff p c true gas bytes

theorem checkpoint_error_consumer (p c : Frame.State) (gas : Nat) (bytes : ByteArray) :
    settleChild p c false gas bytes = .error .missingSnapshot ↔
      c.stateGas.committedSpill = 0 ∧ c.tracker.snapshots = [] :=
  settleChild_missing_snapshot_iff p c false gas bytes

theorem return_warm_consumer (p c out : Frame.State) (bytes : ByteArray) (a : World.Address)
    (h : settle p (.returned c bytes) = .ok out) :
    a ∈ out.warmAddresses ↔ a ∈ c.warmAddresses ∨ a ∈ p.warmAddresses :=
  returned_warm_membership p c out bytes a h

-- A returned child contributes its gas, then the merged reservoir repays spill.
theorem return_gas_consumer (p c out : Frame.State) (bytes : ByteArray)
    (h : settle p (.returned c bytes) = .ok out) :
    out.gas = p.gas + c.gas +
      min (p.stateGas.reservoir + c.stateGas.reservoir)
        (p.stateGas.spilled + c.stateGas.spilled) ∧
    out.stateGas.refundCounter = p.stateGas.refundCounter + c.stateGas.refundCounter := by
  have effect := (returned_iff p c out bytes).mp h
  rcases effect with ⟨_, _, _, _, fields⟩
  simp only [↓reduceIte] at fields
  exact ⟨fields.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fields.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

-- Checkpointing saves the actual prior writes and preserves the complete tracker view.
theorem checkpoint_forward_consumer (before after : Frame.State)
    (h : checkpoint before = after) :
    after.tracker.snapshots = before.tracker.writes :: before.tracker.snapshots ∧
    after.tracker.writes = before.tracker.writes ∧
    after.tracker.parent = before.tracker.parent ∧
    after.tracker.accountReads = before.tracker.accountReads ∧
    after.tracker.storageReads = before.tracker.storageReads ∧
    after.tracker.createdAccounts = before.tracker.createdAccounts ∧
    TransactionState.Reference.Save (TransactionState.Reference.observe before.tracker)
      (TransactionState.Reference.observe after.tracker) := by
  have f := (checkpoint_iff before after).mp h
  exact ⟨f.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    f.2.2.2.2.2.2.2.2.2.2.2.2.2.1, f.2.2.2.2.2.2.2.2.2.2.2.2.1,
    f.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, f.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    f.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    f.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

-- The field observations and tracker save determine the checkpoint frame.
theorem checkpoint_converse_consumer (before after : Frame.State)
    (h : CheckpointFields before after) :
    checkpoint before = after ∧
    after.tracker.snapshots = before.tracker.writes :: before.tracker.snapshots ∧
    after.tracker.writes = before.tracker.writes := by
  have result := (checkpoint_iff before after).mpr h
  have fields := checkpoint_forward_consumer before after result
  exact ⟨result, fields.1, fields.2.1⟩

-- A tooling result is one of the four diagnostic forms, for every runner result.
theorem tooling_forward_consumer (p : Frame.State) (r : Runner.Result)
    (h : settle p r = .error .toolingOutcome) :
    (∃ c op, r = .unsupported c op) ∨ (∃ c, r = .exhausted c) ∨
    (∃ c, r = .exception c .missingCode) ∨
    (∃ c, r = .exception c .missingStorageAccount) := by
  have ht := (settle_tooling_iff p r).mp h
  cases r with
  | stopped c => simp [ToolingResult] at ht
  | returned c bytes => simp [ToolingResult] at ht
  | reverted c gas bytes => simp [ToolingResult] at ht
  | exception c reason => cases reason <;> simp_all [ToolingResult]
  | unsupported c op => exact Or.inl ⟨c, op, rfl⟩
  | exhausted c => exact Or.inr (Or.inl ⟨c, rfl⟩)

theorem unsupported_converse_consumer (p c : Frame.State) (op : Opcode) :
    settle p (.unsupported c op) = .error .toolingOutcome :=
  (settle_tooling_iff p (.unsupported c op)).mpr (by trivial)

theorem exhausted_converse_consumer (p c : Frame.State) :
    settle p (.exhausted c) = .error .toolingOutcome :=
  (settle_tooling_iff p (.exhausted c)).mpr (by trivial)

theorem missing_code_converse_consumer (p c : Frame.State) :
    settle p (.exception c .missingCode) = .error .toolingOutcome :=
  (settle_tooling_iff p (.exception c .missingCode)).mpr (by trivial)

theorem missing_account_converse_consumer (p c : Frame.State) :
    settle p (.exception c .missingStorageAccount) = .error .toolingOutcome :=
  (settle_tooling_iff p (.exception c .missingStorageAccount)).mpr (by trivial)

-- Both fates recover the exact first failing check, and both directions are used.
theorem priority_conditions_consumer (p c : Frame.State) (fate : Bool)
    (gas : Nat) (bytes : ByteArray) :
    (settleChild p c fate gas bytes = .error .committedChildSpill →
      c.stateGas.committedSpill ≠ 0) ∧
    (c.stateGas.committedSpill ≠ 0 →
      settleChild p c fate gas bytes = .error .committedChildSpill) ∧
    (settleChild p c fate gas bytes = .error .missingSnapshot →
      c.stateGas.committedSpill = 0 ∧ c.tracker.snapshots = []) ∧
    (c.stateGas.committedSpill = 0 → c.tracker.snapshots = [] →
      settleChild p c fate gas bytes = .error .missingSnapshot) := by
  exact ⟨(settleChild_committed_spill_iff p c fate gas bytes).mp,
    (settleChild_committed_spill_iff p c fate gas bytes).mpr,
    (settleChild_missing_snapshot_iff p c fate gas bytes).mp,
    fun hzero hempty => (settleChild_missing_snapshot_iff p c fate gas bytes).mpr ⟨hzero, hempty⟩⟩

-- Checkpointing also preserves every non-tracker frame field.
theorem checkpoint_frame_consumer (before after : Frame.State)
    (h : checkpoint before = after) :
    after.code = before.code ∧ after.pc = before.pc ∧ after.stack = before.stack ∧
    after.gas = before.gas ∧ after.memory = before.memory ∧ after.context = before.context ∧
    after.returnData = before.returnData ∧ after.warmAddresses = before.warmAddresses ∧
    after.warmSlots = before.warmSlots ∧ after.isStatic = before.isStatic ∧
    after.stateGas = before.stateGas ∧ after.logs = before.logs := by
  have f := (checkpoint_iff before after).mp h
  exact ⟨f.1, f.2.1, f.2.2.1, f.2.2.2.1, f.2.2.2.2.1, f.2.2.2.2.2.1,
    f.2.2.2.2.2.2.1, f.2.2.2.2.2.2.2.1, f.2.2.2.2.2.2.2.2.1,
    f.2.2.2.2.2.2.2.2.2.1, f.2.2.2.2.2.2.2.2.2.2.1,
    f.2.2.2.2.2.2.2.2.2.2.2.1⟩

-- Explicitly instantiate both success and failure for each priority clause.
theorem both_fates_priority_consumer (p c : Frame.State) (gas : Nat) (bytes : ByteArray)
    (hspill : c.stateGas.committedSpill ≠ 0) (hempty : c.tracker.snapshots = []) :
    settleChild p c true gas bytes = .error .committedChildSpill ∧
    settleChild p c false gas bytes = .error .committedChildSpill ∧ c.tracker.snapshots = [] := by
  have ht := priority_conditions_consumer p c true gas bytes
  have hf := priority_conditions_consumer p c false gas bytes
  exact ⟨ht.2.1 hspill, hf.2.1 hspill, hempty⟩

theorem both_fates_missing_consumer (p c : Frame.State) (gas : Nat) (bytes : ByteArray)
    (hzero : c.stateGas.committedSpill = 0) (hempty : c.tracker.snapshots = []) :
    settleChild p c true gas bytes = .error .missingSnapshot ∧
    settleChild p c false gas bytes = .error .missingSnapshot := by
  have ht := priority_conditions_consumer p c true gas bytes
  have hf := priority_conditions_consumer p c false gas bytes
  exact ⟨ht.2.2.2 hzero hempty, hf.2.2.2 hzero hempty⟩

-- An observed generic success exposes both checks and every resulting field.
theorem generic_observed_success (p c out : Frame.State) (fate : Bool) (gas : Nat) (bytes : ByteArray)
    (h : settleChild p c fate gas bytes = .ok out) :
    c.stateGas.committedSpill = 0 ∧ ∃ saved rest,
      c.tracker.snapshots = saved :: rest ∧
      out.code = p.code ∧ out.pc = p.pc ∧ out.stack = p.stack ∧
      out.memory = p.memory ∧ out.context = p.context ∧ out.returnData = bytes ∧
      out.isStatic = p.isStatic ∧ out.tracker.parent = c.tracker.parent ∧
      out.tracker.writes = (if fate then c.tracker.writes else saved) ∧
      out.tracker.accountReads = c.tracker.accountReads ∧
      out.tracker.storageReads = c.tracker.storageReads ∧
      out.tracker.createdAccounts = c.tracker.createdAccounts ∧ out.tracker.snapshots = rest ∧
      out.logs = (if fate then p.logs ++ c.logs else p.logs) ∧
      out.warmAddresses = (if fate then c.warmAddresses ++ p.warmAddresses else p.warmAddresses) ∧
      out.warmSlots = (if fate then c.warmSlots ++ p.warmSlots else p.warmSlots) ∧
      let reservoir := p.stateGas.reservoir + (if fate then c.stateGas.reservoir else c.stateGas.baseline)
      let spill := p.stateGas.spilled + (if fate then c.stateGas.spilled else 0)
      let repayment := if fate then min reservoir spill else 0
      out.gas = p.gas + gas + repayment ∧
      out.stateGas.reservoir = reservoir - repayment ∧ out.stateGas.baseline = p.stateGas.baseline ∧
      out.stateGas.refundCounter = p.stateGas.refundCounter + (if fate then c.stateGas.refundCounter else 0) ∧
      out.stateGas.spilled = spill - repayment ∧ out.stateGas.committedSpill = p.stateGas.committedSpill := by
  have fields := (settleChild_iff p c out fate gas bytes).mp h
  obtain ⟨saved, rest, hc, hs, fields⟩ := fields
  exact ⟨hc, saved, rest, hs, fields⟩

-- The generic direct helper's two independently stated directions are applied for arbitrary inputs.
theorem generic_effect_forward_consumer (p c out : Frame.State) (fate : Bool) (gas : Nat) (bytes : ByteArray)
    (h : settleChild p c fate gas bytes = .ok out) :
    c.stateGas.committedSpill = 0 ∧ ∃ saved rest, c.tracker.snapshots = saved :: rest ∧
      out.tracker.writes = (if fate then c.tracker.writes else saved) := by
  obtain ⟨saved, rest, hc, hs, fields⟩ := settleChild_effect p c out fate gas bytes h
  exact ⟨hc, saved, rest, hs, fields.2.2.2.2.2.2.2.2.1⟩

theorem generic_effect_reverse_consumer (p c out : Frame.State) (fate : Bool) (gas : Nat) (bytes : ByteArray)
    (fields : Effect p c out fate gas bytes) :
    settleChild p c fate gas bytes = .ok out ∧
      c.stateGas.committedSpill = 0 ∧ ∃ saved rest, c.tracker.snapshots = saved :: rest := by
  have actual := effect_settleChild p c out fate gas bytes fields
  have again := (settleChild_iff p c out fate gas bytes).mpr fields
  obtain ⟨saved, rest, hc, hs, _⟩ := (settleChild_iff p c out fate gas bytes).mp again
  exact ⟨actual, hc, saved, rest, hs⟩

-- Observed wrapper success recovers the first checks without assuming them.
theorem wrapper_observed_checks (p c out : Frame.State) (bytes : ByteArray)
    (h : settle p (.returned c bytes) = .ok out) :
    c.stateGas.committedSpill = 0 ∧ ∃ saved rest, c.tracker.snapshots = saved :: rest ∧
      out.returnData = bytes ∧ out.tracker.writes = c.tracker.writes := by
  obtain ⟨saved, rest, hc, hs, fields⟩ := (returned_iff p c out bytes).mp h
  simp only [↓reduceIte] at fields
  exact ⟨hc, saved, rest, hs, fields.2.2.2.2.2.1, fields.2.2.2.2.2.2.2.2.1⟩

-- Apply the tracker refinements to actual settled protocol outcomes.
theorem stopped_commit_application (p c out : Frame.State)
    (h : settle p (.stopped c) = .ok out) :
    ∃ t saved rest, TransactionState.commit c.tracker = .ok t ∧ out.tracker = t ∧
      c.tracker.snapshots = saved :: rest := by
  obtain ⟨t, ht, hout⟩ := stopped_commits p c out h
  obtain ⟨saved, rest, hs, _⟩ := (TransactionState.commit_ok_iff c.tracker t).mp ht
  exact ⟨t, saved, rest, ht, hout, hs⟩

theorem reverted_reference_application (p c out : Frame.State) (gas : Nat) (bytes : ByteArray)
    (h : settle p (.reverted c gas bytes) = .ok out) :
    ∃ saved rest, (TransactionState.Reference.observe c.tracker).stack = saved :: rest ∧
      (TransactionState.Reference.observe out.tracker).writes = saved := by
  obtain ⟨saved, rest, hs, _, hw, _⟩ := reverted_rolls_back p c out gas bytes h
  exact ⟨saved, rest, hs, hw⟩

theorem returned_reference_application (p c out : Frame.State) (bytes : ByteArray)
    (h : settle p (.returned c bytes) = .ok out) :
    (TransactionState.Reference.observe out.tracker).writes =
      (TransactionState.Reference.observe c.tracker).writes := by
  obtain ⟨_, _, _, _, hw, _⟩ := returned_tracker_refines p c out bytes h
  exact hw

-- An actual RETURN wrapper success recovers the complete fieldwise outcome.
theorem wrapper_observed_all (p c out : Frame.State) (bytes : ByteArray)
    (h : settle p (.returned c bytes) = .ok out) :
    c.stateGas.committedSpill = 0 ∧ ∃ saved rest,
      c.tracker.snapshots = saved :: rest ∧
      out.code = p.code ∧ out.pc = p.pc ∧ out.stack = p.stack ∧
      out.memory = p.memory ∧ out.context = p.context ∧ out.returnData = bytes ∧
      out.isStatic = p.isStatic ∧ out.tracker.parent = c.tracker.parent ∧
      out.tracker.writes = (if true then c.tracker.writes else saved) ∧
      out.tracker.accountReads = c.tracker.accountReads ∧
      out.tracker.storageReads = c.tracker.storageReads ∧
      out.tracker.createdAccounts = c.tracker.createdAccounts ∧ out.tracker.snapshots = rest ∧
      out.logs = (if true then p.logs ++ c.logs else p.logs) ∧
      out.warmAddresses = (if true then c.warmAddresses ++ p.warmAddresses else p.warmAddresses) ∧
      out.warmSlots = (if true then c.warmSlots ++ p.warmSlots else p.warmSlots) ∧
      let reservoir := p.stateGas.reservoir + (if true then c.stateGas.reservoir else c.stateGas.baseline)
      let spill := p.stateGas.spilled + (if true then c.stateGas.spilled else 0)
      let repayment := if true then min reservoir spill else 0
      out.gas = p.gas + c.gas + repayment ∧
      out.stateGas.reservoir = reservoir - repayment ∧ out.stateGas.baseline = p.stateGas.baseline ∧
      out.stateGas.refundCounter = p.stateGas.refundCounter + (if true then c.stateGas.refundCounter else 0) ∧
      out.stateGas.spilled = spill - repayment ∧ out.stateGas.committedSpill = p.stateGas.committedSpill := by
  change settleChild p c true c.gas bytes = .ok out at h
  exact generic_observed_success p c out true c.gas bytes h
