import EthLib.EVM.Proofs.Runner.Transient

open EthLib.EVM

namespace TransientConsumer

theorem load_success_forward (s t : Frame.State) (rest : Stack) (key : Word)
    (items : s.stack.val = key :: rest.val) (gas : 100 ≤ s.gas)
    (fields : Frame.Advances s t (s.pc + 1) (s.gas - 100) (Frame.TransientValue s key :: rest.val)) :
    Frame.tload s = .continue t := (Frame.tload_success_iff s t).mpr ⟨rest, key, items, gas, fields⟩

theorem load_success_converse (s t : Frame.State) (run : Frame.tload s = .continue t) :
    ∃ (rest : Stack) (key : Word), s.stack.val = key :: rest.val ∧ 100 ≤ s.gas ∧
      Frame.Advances s t (s.pc + 1) (s.gas - 100) (Frame.TransientValue s key :: rest.val) :=
  (Frame.tload_success_iff s t).mp run

theorem load_errors_converse (s t : Frame.State) (reason : Frame.Exception)
    (run : Frame.tload s = .exception t reason) :
    (s.stack.val = [] ∧ t = s ∧ reason = .stackUnderflow) ∨
      ∃ (rest : Stack) (key : Word), s.stack.val = key :: rest.val ∧ s.gas < 100 ∧
        t = { s with stack := rest } ∧ reason = .outOfGas :=
  (Frame.tload_exception_iff s t reason).mp run

theorem load_errors_forward (s t : Frame.State) (reason : Frame.Exception)
    (cases_ : (s.stack.val = [] ∧ t = s ∧ reason = .stackUnderflow) ∨
      ∃ (rest : Stack) (key : Word), s.stack.val = key :: rest.val ∧ s.gas < 100 ∧
        t = { s with stack := rest } ∧ reason = .outOfGas) :
    Frame.tload s = .exception t reason := (Frame.tload_exception_iff s t reason).mpr cases_

theorem store_static_converse (s t : Frame.State) (run : Frame.tstore s = .exception t .writeInStaticContext) :
    s.isStatic = true ∧ t = s := by
  have local_ := (Frame.tstore_iff_local s _).mp run
  cases local_; simp_all

theorem store_gas_converse (s t : Frame.State) (run : Frame.tstore s = .exception t .outOfGas) :
    ∃ (first rest : Stack) (key value : Word), s.isStatic = false ∧
      s.stack.val = key :: first.val ∧ first.val = value :: rest.val ∧ s.gas < 100 ∧
      t = { s with stack := rest } := by
  have local_ := (Frame.tstore_iff_local s _).mp run
  cases local_ with
  | gas first rest key value dynamic items second gas => exact ⟨first, rest, key, value, dynamic, items, second, gas, rfl⟩

theorem store_underflow_converse (s t : Frame.State) (run : Frame.tstore s = .exception t .stackUnderflow) :
    s.isStatic = false ∧ ((s.stack.val = [] ∧ t = s) ∨
      ∃ (first : Stack) (key : Word), s.stack.val = key :: first.val ∧ first.val = [] ∧ t = { s with stack := first }) := by
  have local_ := (Frame.tstore_iff_local s _).mp run
  cases local_ with
  | empty dynamic empty => exact ⟨dynamic, Or.inl ⟨empty, rfl⟩⟩
  | second first key dynamic items empty => exact ⟨dynamic, Or.inr ⟨first, key, items, empty, rfl⟩⟩

theorem store_success_converse (s t : Frame.State) (run : Frame.tstore s = .continue t) :
    ∃ (first rest : Stack) (key value : Word), s.isStatic = false ∧
      s.stack.val = key :: first.val ∧ first.val = value :: rest.val ∧ 100 ≤ s.gas ∧
      Frame.TransientWriteEffect s.tracker t.tracker s.context.environment.currentTarget key value :=
  Frame.tstore_success_observation s t run

theorem store_success_fields (s t : Frame.State) (run : Frame.tstore s = .continue t) :
    ∃ (first rest : Stack) (key value : Word), s.isStatic = false ∧
      s.stack.val = key :: first.val ∧ first.val = value :: rest.val ∧ 100 ≤ s.gas ∧
      t.pc = s.pc + 1 ∧ t.gas = s.gas - 100 ∧ t.stack.val = rest.val ∧
      t.code = s.code ∧ t.memory = s.memory ∧ t.context = s.context ∧ t.returnData = s.returnData ∧
      t.warmAddresses = s.warmAddresses ∧ t.warmSlots = s.warmSlots ∧
      t.isStatic = s.isStatic ∧ t.stateGas = s.stateGas ∧
      (∀ p, (TransactionState.Reference.observe t.tracker).writes.transient p =
        if p = (s.context.environment.currentTarget, key) then (if value = 0 then none else some value)
        else (TransactionState.Reference.observe s.tracker).writes.transient p) := by
  have local_ := (Frame.tstore_iff_local s _).mp run
  cases local_ with
  | success _ first rest key value tracker dynamic items second gas writes fields =>
    have trackerEq : t.tracker = tracker := fields.2.2.2.2.2.2.2.1
    have map := (TransactionTracker.setTransientStorage_spec s.tracker s.context.environment.currentTarget key value).2.1
    have unique := Frame.transient_write_fields_unique s.tracker tracker s.context.environment.currentTarget key value writes
    rw [trackerEq, unique]
    exact ⟨first, rest, key, value, dynamic, items, second, gas, fields.2.2.1,
      fields.2.2.2.1, fields.2.2.2.2.1, fields.1, fields.2.1, fields.2.2.2.2.2.1,
      fields.2.2.2.2.2.2.1, fields.2.2.2.2.2.2.2.2.1,
      fields.2.2.2.2.2.2.2.2.2.1, fields.2.2.2.2.2.2.2.2.2.2.1,
      fields.2.2.2.2.2.2.2.2.2.2.2, map⟩

theorem store_retained_observations (s t : Frame.State) (run : Frame.tstore s = .continue t) :
    let before := TransactionState.Reference.observe s.tracker
    let after := TransactionState.Reference.observe t.tracker
    before.parentAccounts = after.parentAccounts ∧ before.parentStorage = after.parentStorage ∧
    before.parentCode = after.parentCode ∧ before.accountReads = after.accountReads ∧
    before.storageReads = after.storageReads ∧ before.created = after.created ∧
    before.stack = after.stack ∧ after.writes.accounts = before.writes.accounts ∧
    after.writes.storage = before.writes.storage ∧ after.writes.code = before.writes.code ∧
    after.writes.clears = before.writes.clears := by
  obtain ⟨_, _, _, _, _, _, _, _, effect⟩ := Frame.tstore_success_observation s t run
  rcases effect with ⟨context, _, accounts, storage, code, clears⟩
  exact ⟨context.1, context.2.1, context.2.2.1, context.2.2.2.1, context.2.2.2.2.1,
    context.2.2.2.2.2.1, context.2.2.2.2.2.2, accounts, storage, code, clears⟩

theorem store_error_forward (s : Frame.State) (first rest : Stack) (key value : Word)
    (dynamic : s.isStatic = false) (items : s.stack.val = key :: first.val)
    (second : first.val = value :: rest.val) (gas : s.gas < 100) :
    Frame.tstore s = .exception { s with stack := rest } .outOfGas :=
  (Frame.tstore_iff_local s _).mpr (.gas s first rest key value dynamic items second gas)

theorem store_static_forward (s : Frame.State) (static : s.isStatic = true) :
    Frame.tstore s = .exception s .writeInStaticContext :=
  (Frame.tstore_iff_local s _).mpr (.static s static)

theorem store_first_forward (s : Frame.State) (dynamic : s.isStatic = false) (empty : s.stack.val = []) :
    Frame.tstore s = .exception s .stackUnderflow :=
  (Frame.tstore_iff_local s _).mpr (.empty s dynamic empty)

theorem store_second_forward (s : Frame.State) (first : Stack) (key : Word)
    (dynamic : s.isStatic = false) (items : s.stack.val = key :: first.val) (empty : first.val = []) :
    Frame.tstore s = .exception { s with stack := first } .stackUnderflow :=
  (Frame.tstore_iff_local s _).mpr (.second s first key dynamic items empty)

theorem store_success_forward (s t : Frame.State) (first rest : Stack) (key value : Word)
    (tracker : TransactionState.State) (dynamic : s.isStatic = false)
    (items : s.stack.val = key :: first.val) (second : first.val = value :: rest.val)
    (gas : 100 ≤ s.gas) (write : Frame.TransientWriteFields s.tracker tracker s.context.environment.currentTarget key value)
    (fields : Frame.Advances { s with tracker } t (s.pc + 1) (s.gas - 100) rest.val) :
    Frame.tstore s = .continue t :=
  (Frame.tstore_iff_local s _).mpr (.success s t first rest key value tracker dynamic items second gas write fields)

theorem snapshot_application (s : TransactionState.State) (a : World.Address) (key value : Word) :
    TransactionState.rollback (TransactionTracker.setTransientStorage (TransactionState.snapshot s) a key value) = .ok s :=
  Frame.transient_snapshot_rollback s a key value

theorem program_application (xs : List Word) (room : xs.length ≤ 1019) (key value : Word) (g : Nat)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem) (ctx : CallData.Context)
    (ret : ByteArray) (tx : TransactionState.State) (warm : List World.Address)
    (slots : List (World.Address × Word)) (meter : Frame.StateGas) :
    let s : Frame.State := ⟨Runner.TransientProgram.program, 0,
      ⟨key :: value :: key :: key :: 0 :: xs, by simp; omega⟩, 302 + g, mem, valid, ctx, ret, tx, warm, slots, false, meter⟩
    ∃ t, Runner.run 5 s = .stopped t ∧ t.pc = 5 ∧ t.gas = g ∧ t.stack.val = xs ∧
      t.tracker = TransactionTracker.setTransientStorage
        (TransactionTracker.setTransientStorage tx ctx.environment.currentTarget key value) ctx.environment.currentTarget key 0 :=
  Runner.TransientProgram.run xs room key value g mem valid ctx ret tx warm slots meter

theorem program_deleted_application (xs : List Word) (room : xs.length ≤ 1019) (key value : Word) (g : Nat)
    (mem : Memory.Allocation.State) (valid : Memory.Allocation.Valid mem) (ctx : CallData.Context)
    (ret : ByteArray) (tx : TransactionState.State) (warm : List World.Address)
    (slots : List (World.Address × Word)) (meter : Frame.StateGas) :
    let s : Frame.State := ⟨Runner.TransientProgram.program, 0,
      ⟨key :: value :: key :: key :: 0 :: xs, by simp; omega⟩, 302 + g, mem, valid, ctx, ret, tx, warm, slots, false, meter⟩
    ∃ t, Runner.run 5 s = .stopped t ∧
      (TransactionState.Reference.observe t.tracker).writes.transient (ctx.environment.currentTarget, key) = none :=
  Runner.TransientProgram.run_deleted xs room key value g mem valid ctx ret tx warm slots meter

end TransientConsumer
