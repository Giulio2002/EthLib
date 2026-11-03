module

public import EthLib.EVM.NestedRunner
public import EthLib.EVM.Proofs.TransactionTransfer
public import EthLib.EVM.Proofs.Gas.StateMeter
public import EthLib.EVM.Proofs.ChildSettlement
public import EthLib.EVM.Proofs.Frame.Finish
public import EthLib.EVM.Proofs.Stack

/-!
# Nested runner trace

The trace describes executable machine transitions and fuel accounting.
The entry and continuation relations describe their fields independently.
They do not prove source conformance for unavailable CALL features.
-/

@[expose] public section
namespace EthLib.EVM.NestedRunner

/-- Each machine transition consumes one unit of tooling fuel. -/
inductive Trace : Nat → Machine → Result → Prop where
  | exhausted (m) : Trace 0 m (.exhausted m)
  | done {fuel m result} : step m = .done result → Trace (fuel + 1) m result.result
  | next {fuel m next result} : step m = .next next → Trace fuel next result →
      Trace (fuel + 1) m result

/-- Every bounded nested run has a corresponding finite machine trace. -/
theorem run_trace (fuel : Nat) (m : Machine) : Trace fuel m (run fuel m) := by
  induction fuel generalizing m with
  | zero => exact .exhausted m
  | succ fuel ih =>
    cases h : step m with
    | done result => simpa [run, h] using (Trace.done (fuel := fuel) h)
    | next next => simpa [run, h] using (Trace.next h (ih next))

/-- A finite machine trace determines the bounded run. -/
theorem run_of_trace {fuel : Nat} {m : Machine} {result : Result}
    (h : Trace fuel m result) : run fuel m = result := by
  induction h with
  | exhausted m => rfl
  | done h => simp [run, h]
  | next h _ ih => simpa [run, h] using ih

/-- Machine traces and bounded runs describe the same fuel-indexed execution. -/
theorem run_iff_trace (fuel : Nat) (m : Machine) (result : Result) :
    run fuel m = result ↔ Trace fuel m result := by
  constructor
  · intro h; rw [← h]; exact run_trace fuel m
  · exact run_of_trace

/-- Additional fuel resumes precisely the machine retained at exhaustion. -/
theorem run_add (fuel extra : Nat) (m : Machine) :
    run (fuel + extra) m = match run fuel m with
      | .exhausted next => run extra next
      | result => result := by
  induction fuel generalizing m with
  | zero => simp [run]
  | succ fuel ih =>
    cases h : step m with
    | done result => cases result <;> simp [run, h, Final.result, Nat.succ_add]
    | next next => simpa [run, h, Nat.succ_add] using ih next

/-- Child creation uses the caller-supplied grant and checkpoint. -/
theorem child_frame_fields (p : CallPreparation.Prepared) :
    (childFrame p).gas = p.childGas ∧
    (childFrame p).stateGas.reservoir = p.stateGrant ∧
    (childFrame p).stateGas.baseline = p.stateGrant ∧
    (childFrame p).stateGas.spilled = 0 ∧
    (childFrame p).stateGas.committedSpill = 0 ∧
    (childFrame p).stateGas.refundCounter = 0 ∧
    (childFrame p).tracker = TransactionState.snapshot p.parent.tracker ∧
    (childFrame p).context.environment.currentTarget = p.address ∧
    (childFrame p).context.environment.caller = p.parent.context.environment.currentTarget ∧
    (childFrame p).isStatic = p.parent.isStatic := by
  simp [childFrame]

/-- A nonzero entry transfer refines the independent tracker observations. -/
theorem enterChild_transfer_refines (p : CallPreparation.Prepared) (child : Frame.State)
    (hvalue : p.request.value ≠ 0) (h : enterChild p = .ok child) :
    TransactionTransfer.SuccessSpec
      (TransactionState.Reference.observe (TransactionState.snapshot p.parent.tracker))
      (TransactionState.Reference.observe child.tracker)
      p.parent.context.environment.currentTarget p.address p.request.value := by
  have hz : (p.request.value == 0) = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    apply hvalue
    exact of_decide_eq_true he
  unfold enterChild at h
  simp only [hz, Bool.false_eq_true, ↓reduceIte] at h
  cases hm : TransactionTransfer.moveEther (childFrame p).tracker
      p.parent.context.environment.currentTarget p.address p.request.value with
  | error e => cases e; simp [hm] at h
  | ok t =>
    have hs := TransactionTransfer.moveEther_refines (childFrame p).tracker
      p.parent.context.environment.currentTarget p.address p.request.value
    rw [hm] at hs
    simp only [hm, Except.ok.injEq] at h
    subst child
    simpa [childFrame] using hs

/-- The transfer failure branch exposes the independent account-read effects. -/
theorem enterChild_insufficient_refines (p : CallPreparation.Prepared) (child : Frame.State)
    (hvalue : p.request.value ≠ 0)
    (h : enterChild p = .error (.insufficientBalance, child)) :
    TransactionTransfer.InsufficientSpec
      (TransactionState.Reference.observe (TransactionState.snapshot p.parent.tracker))
      (TransactionState.Reference.observe child.tracker)
      p.parent.context.environment.currentTarget p.request.value := by
  have hz : (p.request.value == 0) = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    apply hvalue
    exact of_decide_eq_true he
  unfold enterChild at h
  simp only [hz, Bool.false_eq_true, ↓reduceIte] at h
  cases hm : TransactionTransfer.moveEther (childFrame p).tracker
      p.parent.context.environment.currentTarget p.address p.request.value with
  | error e =>
    cases e with
    | mk reason tracker =>
      cases reason with
      | insufficientBalance =>
        have hs := TransactionTransfer.moveEther_refines (childFrame p).tracker
          p.parent.context.environment.currentTarget p.address p.request.value
        rw [hm] at hs
        simp only [hm, Except.error.injEq, Prod.mk.injEq, true_and] at h
        subst child
        simpa [childFrame] using hs
      | recipientOverflow => simp [hm] at h
  | ok t => simp [hm] at h

/-- A charged failed call credits the independent state-gas relation. -/
theorem refundNewAccount_meter (parent : Frame.State) :
    Gas.StateMeter.CreditEffect (Frame.stateMeter parent)
      (Frame.stateMeter (refundNewAccount parent true)) 183600 := by
  apply (Gas.StateMeter.creditState_iff _ _ _).mp
  simp [refundNewAccount, Frame.stateMeter, Frame.withStateMeter]

/-- A failed new-account credit has exactly these frame and meter effects. -/
theorem refundNewAccount_iff (parent out : Frame.State) :
    refundNewAccount parent true = out ↔
    out.code = parent.code ∧ out.pc = parent.pc ∧ out.stack = parent.stack ∧
    out.memory = parent.memory ∧ out.context = parent.context ∧ out.returnData = parent.returnData ∧
    out.tracker = parent.tracker ∧ out.warmAddresses = parent.warmAddresses ∧
    out.warmSlots = parent.warmSlots ∧ out.isStatic = parent.isStatic ∧ out.logs = parent.logs ∧
    Gas.StateMeter.CreditEffect (Frame.stateMeter parent) (Frame.stateMeter out) 183600 := by
  rw [← Gas.StateMeter.creditState_iff]
  cases parent with
  | mk c p st g mem valid ctx data tracker wa ws static meter logs =>
    cases out with
    | mk c2 p2 st2 g2 mem2 valid2 ctx2 data2 tracker2 wa2 ws2 static2 meter2 logs2 =>
      cases meter
      cases meter2
      simp only [refundNewAccount, Frame.stateMeter, Frame.withStateMeter, Gas.StateMeter.creditState]
      constructor <;> intro h <;> simp_all
/-- Overflow preserves the independent post-debit read and checked bound. -/
theorem enterChild_overflow_refines (p : CallPreparation.Prepared) (child : Frame.State)
    (hvalue : p.request.value ≠ 0)
    (h : enterChild p = .error (.recipientOverflow, child)) :
    TransactionTransfer.OverflowSpec
      (TransactionState.Reference.observe (TransactionState.snapshot p.parent.tracker))
      (TransactionState.Reference.observe child.tracker)
      p.parent.context.environment.currentTarget p.address p.request.value := by
  have hz : (p.request.value == 0) = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    apply hvalue
    exact of_decide_eq_true he
  unfold enterChild at h
  simp only [hz, Bool.false_eq_true, ↓reduceIte] at h
  cases hm : TransactionTransfer.moveEther (childFrame p).tracker
      p.parent.context.environment.currentTarget p.address p.request.value with
  | error e =>
    cases e with
    | mk reason tracker =>
      cases reason with
      | insufficientBalance => simp [hm] at h
      | recipientOverflow =>
        have hs := TransactionTransfer.moveEther_refines (childFrame p).tracker
          p.parent.context.environment.currentTarget p.address p.request.value
        rw [hm] at hs
        simp only [hm, Except.error.injEq, Prod.mk.injEq, true_and] at h
        subst child
        simpa [childFrame] using hs
  | ok t => simp [hm] at h

/-- Independent zero-value entry fields and operand-bound child input bytes. -/
def ZeroEntry (p : CallPreparation.Prepared) (out : Frame.State) : Prop :=
  p.request.value = 0 ∧ out.code = p.code ∧ out.pc = 0 ∧ out.stack = Stack.empty ∧
  out.gas = p.childGas ∧ out.memory = Memory.Allocation.empty ∧ out.returnData = ByteArray.empty ∧
  out.context.environment = { p.parent.context.environment with currentTarget := p.address, caller := p.parent.context.environment.currentTarget, value := p.request.value } ∧
  Frame.FinishBytes p.parent p.request.inputOffset p.request.inputSize out.context.data ∧
  out.tracker.parent = p.parent.tracker.parent ∧ out.tracker.writes = p.parent.tracker.writes ∧
  out.tracker.accountReads = p.parent.tracker.accountReads ∧
  out.tracker.storageReads = p.parent.tracker.storageReads ∧
  out.tracker.createdAccounts = p.parent.tracker.createdAccounts ∧
  out.tracker.snapshots = p.parent.tracker.writes :: p.parent.tracker.snapshots ∧
  out.warmAddresses = p.parent.warmAddresses ∧ out.warmSlots = p.parent.warmSlots ∧
  out.isStatic = p.parent.isStatic ∧ out.stateGas = ⟨p.stateGrant, p.stateGrant, 0, 0, 0⟩ ∧ out.logs = []

theorem inputBytes_unique (s : Frame.State) (offset length : Word) (a b : ByteArray)
    (ha : Frame.FinishBytes s offset length a) (hb : Frame.FinishBytes s offset length b) : a = b := by
  apply ByteArray.ext
  apply Array.ext
  · simpa only [ByteArray.size] using ha.1.trans hb.1.symm
  · intro i h1 h2
    have h1' : i < a.size := by simpa only [ByteArray.size] using h1
    have h2' : i < b.size := by simpa only [ByteArray.size] using h2
    simpa only [ByteArray.getElem_eq_getElem_data] using (ha.2 i h1').trans (hb.2 i h2').symm

theorem zeroEntry_iff (p : CallPreparation.Prepared) (out : Frame.State)
    (hv : p.request.value = 0) : enterChild p = .ok out ↔ ZeroEntry p out := by
  have hzero : (p.request.value == 0) = true := by simp [hv]
  simp only [enterChild, hzero, ↓reduceIte, Except.ok.injEq]
  constructor
  · intro h
    subst out
    simp only [ZeroEntry, childFrame, hv, TransactionState.snapshot, true_and, and_self]
    exact ⟨Frame.finish_bytes _ _ _, trivial⟩
  · intro h
    rcases h with ⟨_, hc, hpc, hstack, hgas, hmem, hret, henv, hbytes,
      hparent, hwrites, hareads, hsreads, hcreated, hsnap, hwarm, hslots, hstatic, hmeter, hlogs⟩
    have hb := inputBytes_unique p.parent p.request.inputOffset p.request.inputSize out.context.data
      ⟨(Memory.readRange p.parent.memory.store p.request.inputOffset.toNat p.request.inputSize.toNat).toArray⟩
      hbytes (Frame.finish_bytes _ _ _)
    apply ChildSettlement.frame_eq_of_fields <;> simp_all [childFrame, TransactionState.snapshot]
    · cases hctx : out.context with
      | mk data env => simp only [hctx] at hb henv; simp_all
    · cases htx : out.tracker with
      | mk parent writes areads sreads created snaps =>
        simp only [htx] at hparent hwrites hareads hsreads hcreated hsnap
        simp_all
/-- With stack space, continuation fails exactly when checkpoint settlement fails. -/
theorem resume_invalid_checkpoint_iff (c : Continuation) (child : Frame.State) (success : Bool)
    (gas : Nat) (output : ByteArray) (rest : List Continuation)
    (hroom : c.parent.stack.val.length < 1024) :
    resume c child success gas output rest = .done (.tooling child .invalidContinuation) ↔
      child.stateGas.committedSpill ≠ 0 ∨ child.tracker.snapshots = [] := by
  by_cases hc : child.stateGas.committedSpill = 0
  · cases hs : child.tracker.snapshots with
    | nil =>
      cases success <;> simp [resume, ChildSettlement.settleChild, TransactionState.commit,
        TransactionState.rollback, hc, hs]
    | cons saved tail =>
      cases success <;> cases hb : c.newAccountCharged <;>
        simp [resume, ChildSettlement.settleChild, TransactionState.commit,
          TransactionState.rollback, hc, hs, hb, refundNewAccount, Frame.withStateMeter, Stack.push, hroom]
  · simp [resume, ChildSettlement.settleChild, hc]
/-- Fields constrained when a failed new-account charge is credited. -/
def CreditFields (before after : Frame.State) : Prop :=
  after.code = before.code ∧ after.pc = before.pc ∧ after.stack = before.stack ∧
  after.memory = before.memory ∧ after.context = before.context ∧ after.returnData = before.returnData ∧
  after.tracker = before.tracker ∧ after.warmAddresses = before.warmAddresses ∧
  after.warmSlots = before.warmSlots ∧ after.isStatic = before.isStatic ∧ after.logs = before.logs ∧
  Gas.StateMeter.CreditEffect (Frame.stateMeter before) (Frame.stateMeter after) 183600

def RefundSpec (success charged : Bool) (before after : Frame.State) : Prop :=
  ((success = true ∨ charged = false) ∧ after = before) ∨
    (success = false ∧ charged = true ∧ CreditFields before after)

theorem refund_spec_iff (success charged : Bool) (before after : Frame.State) :
    (if success then before else refundNewAccount before charged) = after ↔
      RefundSpec success charged before after := by
  cases success <;> cases charged
  · simp [RefundSpec, refundNewAccount, eq_comm]
  · simpa [RefundSpec, CreditFields] using refundNewAccount_iff before after
  · simp [RefundSpec, eq_comm]
  · simp [RefundSpec, eq_comm]
/-- Consecutive writes add the indexed bytes to the sparse history. -/
theorem writeRange_list (s : Memory.Store) (offset : Nat) (bytes : List UInt8) :
    Memory.writeRange s offset bytes = (List.zip (List.range' offset bytes.length) bytes) ++ s := by
  induction bytes generalizing offset with
  | nil => rfl
  | cons b bs ih => simp [Memory.writeRange, Memory.writeByte, List.range'_succ, ih]

def ResumeSuccess (c : Continuation) (child : Frame.State) (success : Bool)
    (gas : Nat) (output : ByteArray) (rest : List Continuation) (out : Machine) : Prop :=
  ∃ incorporated credited : Frame.State,
    ChildSettlement.Effect c.parent child incorporated success gas output ∧
    RefundSpec success c.newAccountCharged incorporated credited ∧
    credited.stack.val.length < 1024 ∧
    out.depth = c.depth ∧ out.callers = rest ∧
    out.frame.code = credited.code ∧ out.frame.pc = credited.pc + 1 ∧
    out.frame.stack.val = (if success then 1 else 0) :: credited.stack.val ∧
    out.frame.gas = credited.gas ∧
    out.frame.memory.store = List.zip
      (List.range' c.request.outputOffset.toNat (output.data.toList.take c.request.outputSize.toNat).length)
      (output.data.toList.take c.request.outputSize.toNat) ++ credited.memory.store ∧
    out.frame.memory.words = max credited.memory.words
      (Memory.Allocation.requiredWords c.request.outputOffset.toNat (output.data.toList.take c.request.outputSize.toNat).length) ∧
    out.frame.context = credited.context ∧ out.frame.returnData = credited.returnData ∧
    out.frame.tracker = credited.tracker ∧ out.frame.warmAddresses = credited.warmAddresses ∧
    out.frame.warmSlots = credited.warmSlots ∧ out.frame.isStatic = credited.isStatic ∧
    out.frame.stateGas = credited.stateGas ∧ out.frame.logs = credited.logs

theorem resume_success_iff (c : Continuation) (child : Frame.State) (success : Bool)
    (gas : Nat) (output : ByteArray) (rest : List Continuation) (out : Machine) :
    resume c child success gas output rest = .next out ↔ ResumeSuccess c child success gas output rest out := by
  constructor
  · intro h
    cases hs : ChildSettlement.settleChild c.parent child success gas output with
    | error e => simp [resume, hs] at h
    | ok incorporated =>
      let credited := if success then incorporated else refundNewAccount incorporated c.newAccountCharged
      cases hp : Stack.push credited.stack (if success then 1 else 0) with
      | error e =>
        simp only [resume, hs] at h
        change (match Stack.push credited.stack (if success then 1 else 0) with
          | .error _ => _ | .ok _ => _) = _ at h
        rw [hp] at h
        contradiction
      | ok stack =>
        simp only [resume, hs] at h
        change (match Stack.push credited.stack (if success then 1 else 0) with
          | .error _ => _ | .ok _ => _) = _ at h
        rw [hp] at h
        simp only [Transition.next.injEq] at h
        subst out
        have heff := (ChildSettlement.settleChild_iff _ _ _ _ _ _).mp hs
        have hcredit := (refund_spec_iff success c.newAccountCharged incorporated credited).mp rfl
        have hpush := (Proofs.Stack.push_ok_iff _ _ _).mp hp
        have hstack' : stack.val = (if success then (1 : Word) else 0) :: credited.stack.val := by
          simpa only [Stack.toList] using hpush.2
        refine ⟨incorporated, credited, heff, hcredit, hpush.1, ?_⟩
        simp [Memory.Allocation.write, Memory.Allocation.expand, writeRange_list, credited, hstack']
  · intro h
    rcases h with ⟨incorporated, credited, heff, hcredit, hroom, hdepth, hcallers,
      hcode, hpc, hstack, hgas, hstore, hwords, hcontext, hret, htracker, hwarm,
      hslots, hstatic, hstate, hlogs⟩
    have hs := (ChildSettlement.settleChild_iff _ _ _ _ _ _).mpr heff
    have hr := (refund_spec_iff success c.newAccountCharged incorporated credited).mpr hcredit
    have hp : Stack.push credited.stack (if success then 1 else 0) = .ok out.frame.stack :=
      (Proofs.Stack.push_ok_iff _ _ _).mpr ⟨hroom, hstack⟩
    simp only [resume, hs, hr, hp]
    apply congrArg Transition.next
    cases out with
    | mk frame depth callers =>
      simp only at *
      subst depth
      subst callers
      congr 1
      apply ChildSettlement.frame_eq_of_fields <;> simp_all [Memory.Allocation.write, Memory.Allocation.expand, writeRange_list]
      all_goals
        cases hfm : frame.memory with
        | mk fstore fwords =>
          cases hcm : credited.memory with
          | mk cstore cwords =>
            simp only [hfm, hcm] at hstore hwords
            simp_all
/-- Output bytes overwrite exactly the requested prefix of the parent memory. -/
theorem resume_success_bytes (c : Continuation) (child : Frame.State) (success : Bool)
    (gas : Nat) (output : ByteArray) (rest : List Continuation) (out : Machine)
    (h : resume c child success gas output rest = .next out) :
    ∃ incorporated credited : Frame.State,
      ChildSettlement.Effect c.parent child incorporated success gas output ∧
      RefundSpec success c.newAccountCharged incorporated credited ∧
      ∀ q, Memory.readByte out.frame.memory.store q =
        if hq : c.request.outputOffset.toNat ≤ q ∧
          q < c.request.outputOffset.toNat + (output.data.toList.take c.request.outputSize.toNat).length then
          (output.data.toList.take c.request.outputSize.toNat)[q - c.request.outputOffset.toNat]'(by omega)
        else Memory.readByte credited.memory.store q := by
  have effect := (resume_success_iff c child success gas output rest out).mp h
  obtain ⟨incorporated, credited, hsettle, hcredit, _, _, _, _, _, _, _, hstore, _⟩ := effect
  refine ⟨incorporated, credited, hsettle, hcredit, ?_⟩
  intro q
  rw [hstore, ← writeRange_list]
  exact Memory.writeRange_observe _ _ _ _
/-- Settlement failure exposes spill priority and checkpoint absence. -/
theorem settlement_failure_iff (parent child : Frame.State) (success : Bool) (gas : Nat) (output : ByteArray) :
    (∃ e, ChildSettlement.settleChild parent child success gas output = .error e) ↔
      child.stateGas.committedSpill ≠ 0 ∨ (child.stateGas.committedSpill = 0 ∧ child.tracker.snapshots = []) := by
  by_cases hc : child.stateGas.committedSpill = 0 <;> cases hs : child.tracker.snapshots <;>
    cases success <;> simp [ChildSettlement.settleChild, TransactionState.commit, TransactionState.rollback, hc, hs]

def ResumeFailure (c : Continuation) (child : Frame.State) (success : Bool)
    (gas : Nat) (output : ByteArray) (diagnostic : Frame.State) : Prop :=
  (diagnostic = child ∧ (child.stateGas.committedSpill ≠ 0 ∨
    (child.stateGas.committedSpill = 0 ∧ child.tracker.snapshots = []))) ∨
  ∃ incorporated credited : Frame.State,
    ChildSettlement.Effect c.parent child incorporated success gas output ∧
    RefundSpec success c.newAccountCharged incorporated credited ∧
    credited.stack.val.length = 1024 ∧ diagnostic = credited

theorem resume_failure_iff (c : Continuation) (child : Frame.State) (success : Bool)
    (gas : Nat) (output : ByteArray) (rest : List Continuation) (diagnostic : Frame.State) :
    resume c child success gas output rest = .done (.tooling diagnostic .invalidContinuation) ↔
      ResumeFailure c child success gas output diagnostic := by
  cases hs : ChildSettlement.settleChild c.parent child success gas output with
  | error e =>
    have hf := (settlement_failure_iff c.parent child success gas output).mp ⟨e, hs⟩
    constructor
    · intro h
      simp only [resume, hs, Final.tooling.injEq, Transition.done.injEq] at h
      exact Or.inl ⟨h.1.symm, hf⟩
    · intro h
      rcases h with ⟨rfl, _⟩ | ⟨inc, credit, heff, _, _, _⟩
      · simp [resume, hs]
      · have hgood := (ChildSettlement.settleChild_iff _ _ _ _ _ _).mpr heff
        rw [hs] at hgood
        contradiction
  | ok incorporated =>
    have heff := (ChildSettlement.settleChild_iff _ _ _ _ _ _).mp hs
    have hgood : ¬ (child.stateGas.committedSpill ≠ 0 ∨
        (child.stateGas.committedSpill = 0 ∧ child.tracker.snapshots = [])) := by
      intro hb
      have ⟨e, he⟩ := (settlement_failure_iff c.parent child success gas output).mpr hb
      rw [hs] at he
      contradiction
    let credited := if success then incorporated else refundNewAccount incorporated c.newAccountCharged
    have hcredit := (refund_spec_iff success c.newAccountCharged incorporated credited).mp rfl
    cases hp : Stack.push credited.stack (if success then 1 else 0) with
    | error e =>
      have he : e = .overflow := by
        cases e with
        | overflow => rfl
        | underflow => unfold Stack.push at hp; split at hp <;> cases hp
      subst e
      have hfull := (Proofs.Stack.push_overflow_iff _ _).mp hp
      constructor
      · intro h
        simp only [resume, hs] at h
        change (match Stack.push credited.stack (if success then 1 else 0) with
          | .error _ => _ | .ok _ => _) = _ at h
        rw [hp] at h
        simp only [Transition.done.injEq, Final.tooling.injEq] at h
        exact Or.inr ⟨incorporated, credited, heff, hcredit, hfull, h.1.symm⟩
      · intro h
        rcases h with ⟨_, hb⟩ | ⟨inc, credit, hinc, hcred, _, hd⟩
        · exact False.elim (hgood hb)
        · have hi := (ChildSettlement.settleChild_iff _ _ _ _ _ _).mpr hinc
          rw [hs] at hi
          cases hi
          have hcred' := (refund_spec_iff success c.newAccountCharged incorporated credit).mpr hcred
          have hsame : credited = credit := by simpa [credited] using hcred'
          subst credit
          subst diagnostic
          simp only [resume, hs]
          change (match Stack.push credited.stack (if success then 1 else 0) with
            | .error _ => _ | .ok _ => _) = _
          rw [hp]
    | ok stack =>
      have hroom := ((Proofs.Stack.push_ok_iff _ _ _).mp hp).1
      constructor
      · intro h
        simp only [resume, hs] at h
        change (match Stack.push credited.stack (if success then 1 else 0) with
          | .error _ => _ | .ok _ => _) = _ at h
        rw [hp] at h
        contradiction
      · intro h
        rcases h with ⟨_, hb⟩ | ⟨inc, credit, hinc, hcred, hfull, _⟩
        · exact False.elim (hgood hb)
        · have hi := (ChildSettlement.settleChild_iff _ _ _ _ _ _).mpr hinc
          rw [hs] at hi
          cases hi
          have hcred' := (refund_spec_iff success c.newAccountCharged incorporated credit).mpr hcred
          have hsame : credited = credit := by simpa [credited] using hcred'
          subst credit
          simp only [Stack.height] at hroom
          rw [← hsame] at hfull
          omega
/-- The continuation result is either a constrained next state or a diagnostic. -/
def ResumeOutcomeSpec (c : Continuation) (child : Frame.State) (success : Bool)
    (gas : Nat) (output : ByteArray) (rest : List Continuation) : Transition → Prop
  | .next out => ResumeSuccess c child success gas output rest out
  | .done (.tooling diagnostic .invalidContinuation) => ResumeFailure c child success gas output diagnostic
  | .done _ => False

theorem resume_done_only_invalid (c : Continuation) (child : Frame.State) (success : Bool)
    (gas : Nat) (output : ByteArray) (rest : List Continuation) (final : Final)
    (h : resume c child success gas output rest = .done final) :
    ∃ diagnostic, final = .tooling diagnostic .invalidContinuation := by
  cases hs : ChildSettlement.settleChild c.parent child success gas output with
  | error e =>
    simp only [resume, hs, Transition.done.injEq] at h
    exact ⟨child, h.symm⟩
  | ok incorporated =>
    let credited := if success then incorporated else refundNewAccount incorporated c.newAccountCharged
    cases hp : Stack.push credited.stack (if success then 1 else 0) with
    | error e =>
      simp only [resume, hs] at h
      change (match Stack.push credited.stack (if success then 1 else 0) with
        | .error _ => _ | .ok _ => _) = _ at h
      rw [hp] at h
      simp only [Transition.done.injEq] at h
      exact ⟨credited, h.symm⟩
    | ok stack =>
      simp only [resume, hs] at h
      change (match Stack.push credited.stack (if success then 1 else 0) with
        | .error _ => _ | .ok _ => _) = _ at h
      rw [hp] at h
      contradiction

theorem resume_iff (c : Continuation) (child : Frame.State) (success : Bool)
    (gas : Nat) (output : ByteArray) (rest : List Continuation) (result : Transition) :
    resume c child success gas output rest = result ↔ ResumeOutcomeSpec c child success gas output rest result := by
  cases result with
  | next out => exact resume_success_iff c child success gas output rest out
  | done final =>
    cases final with
    | terminal result =>
      simp only [ResumeOutcomeSpec, iff_false]
      intro h
      obtain ⟨_, hf⟩ := resume_done_only_invalid c child success gas output rest _ h
      contradiction
    | tooling d reason =>
      cases reason with
      | invalidContinuation => exact resume_failure_iff c child success gas output rest d
      | preparation why =>
        simp only [ResumeOutcomeSpec, iff_false]
        intro h
        obtain ⟨_, hf⟩ := resume_done_only_invalid c child success gas output rest _ h
        simp at hf
      | transfer why =>
        simp only [ResumeOutcomeSpec, iff_false]
        intro h
        obtain ⟨_, hf⟩ := resume_done_only_invalid c child success gas output rest _ h
        simp at hf
      | precompile | unsupported | incompleteWorld =>
        simp only [ResumeOutcomeSpec, iff_false]
        intro h
        obtain ⟨_, hf⟩ := resume_done_only_invalid c child success gas output rest _ h
        simp at hf
/-- Balance updates preserve exact duplicate-backed tracker histories. -/
def BalanceEffect (before after : TransactionState.State) (a : World.Address) (balance : Word) : Prop :=
  let account := { (TransactionAccount.selectedAccount (TransactionState.Reference.observe before) a) with balance := balance }
  after.parent = before.parent ∧ after.accountReads = a :: a :: before.accountReads ∧
  after.storageReads = (if account = World.emptyAccount then
    (before.writes.storageWrites.filter (fun entry => entry.1.1 == a)).map Prod.fst ++ before.storageReads
    else before.storageReads) ∧
  after.createdAccounts = before.createdAccounts ∧ after.snapshots = before.snapshots ∧
  after.writes.accountWrites = (if account = World.emptyAccount then (a, none) :: (a, some account) :: before.writes.accountWrites
    else (a, some account) :: before.writes.accountWrites) ∧
  after.writes.storageWrites = (if account = World.emptyAccount then
    before.writes.storageWrites.filter (fun entry => entry.1.1 != a) else before.writes.storageWrites) ∧
  after.writes.storageClears = (if account = World.emptyAccount then a :: before.writes.storageClears else before.writes.storageClears) ∧
  after.writes.codeWrites = before.writes.codeWrites ∧ after.writes.transientStorage = before.writes.transientStorage

theorem balance_effect_iff (before after : TransactionState.State) (a : World.Address) (balance : Word) :
    TransactionAccount.setAccountBalance before a balance = after ↔ BalanceEffect before after a balance := by
  unfold BalanceEffect
  rw [TransactionAccount.selectedAccount_eq]
  unfold TransactionAccount.setAccountBalance TransactionAccount.modifyState
  simp only [TransactionTracker.getAccount, TransactionTracker.getAccountOptional,
    TransactionTracker.setAccount, List.lookup_cons, beq_self_eq_true]
  by_cases he : { ((TransactionTracker.getAccountOptional before a).1).getD World.emptyAccount with balance := balance } = World.emptyAccount
  all_goals simp only [TransactionTracker.getAccountOptional] at he
  · simp [TransactionAccount.destroyAccount, TransactionTracker.setAccount,
      TransactionTracker.destroyStorage, he]
    cases after with
    | mk parent writes areads sreads created snapshots =>
      cases writes; simp only [TransactionState.State.mk.injEq, TransactionState.Snapshot.mk.injEq]; constructor <;> intro h <;> simp_all
  · simp [he]
    cases after with
    | mk parent writes areads sreads created snapshots =>
      cases writes; simp only [TransactionState.State.mk.injEq, TransactionState.Snapshot.mk.injEq]; constructor <;> intro h <;> simp_all
      rcases h with ⟨hp, hw, _⟩
      subst parent
      exact hw.1.symm
/-- Exact account-read history, including duplicate addresses. -/
def ReadExact (before after : TransactionState.State) (a : World.Address) : Prop :=
  after.parent = before.parent ∧ after.writes = before.writes ∧
  after.accountReads = a :: before.accountReads ∧ after.storageReads = before.storageReads ∧
  after.createdAccounts = before.createdAccounts ∧ after.snapshots = before.snapshots

theorem read_exact_iff (before after : TransactionState.State) (a : World.Address) :
    (TransactionTracker.getAccount before a).2 = after ↔ ReadExact before after a := by
  cases after
  simp [ReadExact, TransactionTracker.getAccount, TransactionTracker.getAccountOptional, eq_comm]

def ExactTransfer (before : TransactionState.State) (sender recipient : World.Address) (amount : Word) :
    Except (TransactionTransfer.TransferError × TransactionState.State) TransactionState.State → Prop
  | .error (.insufficientBalance, after) =>
    (TransactionAccount.selectedAccount (TransactionState.Reference.observe before) sender).balance.toNat < amount.toNat ∧
      ReadExact before after sender
  | .error (.recipientOverflow, after) =>
    amount.toNat ≤ (TransactionAccount.selectedAccount (TransactionState.Reference.observe before) sender).balance.toNat ∧
    ∃ debit : TransactionState.State,
      BalanceEffect before debit sender (BitVec.ofNat 256
        ((TransactionAccount.selectedAccount (TransactionState.Reference.observe before) sender).balance.toNat - amount.toNat)) ∧
      Word.modulus ≤ (TransactionAccount.selectedAccount (TransactionState.Reference.observe debit) recipient).balance.toNat + amount.toNat ∧
      ReadExact debit after recipient
  | .ok after =>
    amount.toNat ≤ (TransactionAccount.selectedAccount (TransactionState.Reference.observe before) sender).balance.toNat ∧
    ∃ debit : TransactionState.State,
      BalanceEffect before debit sender (BitVec.ofNat 256
        ((TransactionAccount.selectedAccount (TransactionState.Reference.observe before) sender).balance.toNat - amount.toNat)) ∧
      (TransactionAccount.selectedAccount (TransactionState.Reference.observe debit) recipient).balance.toNat + amount.toNat < Word.modulus ∧
      BalanceEffect debit after recipient (BitVec.ofNat 256
        ((TransactionAccount.selectedAccount (TransactionState.Reference.observe debit) recipient).balance.toNat + amount.toNat))

theorem exactTransfer_iff (before : TransactionState.State) (sender recipient : World.Address) (amount : Word)
    (result : Except (TransactionTransfer.TransferError × TransactionState.State) TransactionState.State) :
    TransactionTransfer.moveEther before sender recipient amount = result ↔ ExactTransfer before sender recipient amount result := by
  cases result with
  | error e =>
    rcases e with ⟨reason, after⟩
    cases reason with
    | insufficientBalance =>
      rw [TransactionTransfer.insufficient_iff]
      simp only [ExactTransfer, TransactionAccount.selectedAccount_eq, ← read_exact_iff, eq_comm]
    | recipientOverflow =>
      have ht := TransactionTransfer.overflow_iff before after sender recipient amount
      dsimp only at ht
      rw [ht]
      simp only [ExactTransfer, TransactionAccount.selectedAccount_eq, ← balance_effect_iff, ← read_exact_iff]
      constructor
      · rintro ⟨hbound, hover, rfl⟩
        exact ⟨hbound, _, rfl, hover, rfl⟩
      · rintro ⟨hbound, debit, hdebit, hover, hafter⟩
        subst debit
        exact ⟨hbound, hover, hafter.symm⟩
  | ok after =>
    have ht := TransactionTransfer.success_iff before after sender recipient amount
    dsimp only at ht
    rw [ht]
    simp only [ExactTransfer, TransactionAccount.selectedAccount_eq, ← balance_effect_iff]
    constructor
    · rintro ⟨hbound, hcredit, rfl⟩
      exact ⟨hbound, _, rfl, hcredit, rfl⟩
    · rintro ⟨hbound, debit, hdebit, hcredit, hafter⟩
      subst debit
      exact ⟨hbound, hcredit, hafter.symm⟩
/-- The saved scope retains exact transaction fields and duplicate histories. -/
def CheckpointExact (before after : TransactionState.State) : Prop :=
  after.parent = before.parent ∧ after.writes = before.writes ∧
  after.accountReads = before.accountReads ∧ after.storageReads = before.storageReads ∧
  after.createdAccounts = before.createdAccounts ∧ after.snapshots = before.writes :: before.snapshots

theorem checkpoint_exact_iff (before after : TransactionState.State) :
    TransactionState.snapshot before = after ↔ CheckpointExact before after := by
  cases after
  simp [CheckpointExact, TransactionState.snapshot, eq_comm]

def EntryShape (p : CallPreparation.Prepared) (out : Frame.State) : Prop :=
  out.code = p.code ∧ out.pc = 0 ∧ out.stack = Stack.empty ∧ out.gas = p.childGas ∧
  out.memory = Memory.Allocation.empty ∧ out.returnData = ByteArray.empty ∧
  out.context.environment = { p.parent.context.environment with currentTarget := p.address, caller := p.parent.context.environment.currentTarget, value := p.request.value } ∧
  Frame.FinishBytes p.parent p.request.inputOffset p.request.inputSize out.context.data ∧
  out.warmAddresses = p.parent.warmAddresses ∧ out.warmSlots = p.parent.warmSlots ∧
  out.isStatic = p.parent.isStatic ∧ out.stateGas = ⟨p.stateGrant, p.stateGrant, 0, 0, 0⟩

theorem entryShape_iff (p : CallPreparation.Prepared) (out : Frame.State)
    (tracker : TransactionState.State) (logs : List Frame.LogEntry) :
    { childFrame p with tracker := tracker, logs := logs } = out ↔
      EntryShape p out ∧ out.tracker = tracker ∧ out.logs = logs := by
  constructor
  · intro h
    subst out
    simp only [EntryShape, childFrame, true_and, and_self]
    exact ⟨⟨Frame.finish_bytes _ _ _, trivial⟩, trivial⟩
  · rintro ⟨shape, ht, hl⟩
    rcases shape with ⟨hc, hpc, hstack, hgas, hmem, hret, henv, hbytes, hwarm, hslots, hstatic, hmeter⟩
    have hb := inputBytes_unique p.parent p.request.inputOffset p.request.inputSize out.context.data
      ⟨(Memory.readRange p.parent.memory.store p.request.inputOffset.toNat p.request.inputSize.toNat).toArray⟩
      hbytes (Frame.finish_bytes _ _ _)
    apply ChildSettlement.frame_eq_of_fields <;> simp_all [childFrame]
    cases hctx : out.context with
    | mk data env => simp only [hctx] at hb henv; simp_all
/-- The EIP-7708 event records the original sender, recipient and value. -/
def EntryLog (p : CallPreparation.Prepared) : List Frame.LogEntry :=
  if p.parent.context.environment.currentTarget = p.address then [] else
    [⟨⟨2 ^ 160 - 2, by decide⟩,
      [Frame.logTopic (World.codeHash "Transfer(address,address,uint256)".toUTF8),
       Frame.logTopic (Environment.addressWord p.parent.context.environment.currentTarget),
       Frame.logTopic (Environment.addressWord p.address)], p.request.value.toBytesBE⟩]

def EntrySpec (p : CallPreparation.Prepared) :
    Except (TransactionTransfer.TransferError × Frame.State) Frame.State → Prop
  | .ok out => ∃ checkpoint, CheckpointExact p.parent.tracker checkpoint ∧ EntryShape p out ∧
      ((p.request.value = 0 ∧ out.tracker = checkpoint ∧ out.logs = []) ∨
       (p.request.value ≠ 0 ∧ ExactTransfer checkpoint p.parent.context.environment.currentTarget p.address p.request.value (.ok out.tracker) ∧ out.logs = EntryLog p))
  | .error (reason, out) => ∃ checkpoint, CheckpointExact p.parent.tracker checkpoint ∧ EntryShape p out ∧
      p.request.value ≠ 0 ∧ ExactTransfer checkpoint p.parent.context.environment.currentTarget p.address p.request.value (.error (reason, out.tracker)) ∧ out.logs = []

theorem entry_iff (p : CallPreparation.Prepared)
    (result : Except (TransactionTransfer.TransferError × Frame.State) Frame.State) :
    enterChild p = result ↔ EntrySpec p result := by
  cases result with
  | ok out =>
    constructor
    · intro h
      by_cases hv : p.request.value = 0
      · have fields := (zeroEntry_iff p out hv).mp h
        have shape : EntryShape p out := by
          rcases fields with ⟨_, hc, hpc, hstack, hgas, hmem, hret, henv, hbytes,
            _, _, _, _, _, _, hwarm, hslots, hstatic, hstate, _⟩
          exact ⟨hc, hpc, hstack, hgas, hmem, hret, henv, hbytes, hwarm, hslots, hstatic, hstate⟩
        have hchild : childFrame p = out := by simpa [enterChild, hv] using h
        refine ⟨TransactionState.snapshot p.parent.tracker, (checkpoint_exact_iff _ _).mp rfl, shape, Or.inl ⟨hv, ?_, ?_⟩⟩
        · simpa [childFrame] using congrArg Frame.State.tracker hchild.symm
        · simpa [childFrame] using congrArg Frame.State.logs hchild.symm
      · have hb : (p.request.value == 0) = false := by apply Bool.eq_false_iff.mpr; intro he; apply hv; exact of_decide_eq_true he
        cases ht : TransactionTransfer.moveEther (TransactionState.snapshot p.parent.tracker)
            p.parent.context.environment.currentTarget p.address p.request.value with
        | error e =>
          simp only [enterChild, hb, Bool.false_eq_true, ↓reduceIte, childFrame, ht] at h
          cases e; contradiction
        | ok tracker =>
          simp only [enterChild, hb, Bool.false_eq_true, ↓reduceIte, childFrame] at h
          rw [ht] at h
          simp only [Except.ok.injEq] at h
          let logs := if p.parent.context.environment.currentTarget == p.address then [] else
            [transferLog p.parent.context.environment.currentTarget p.address p.request.value]
          have hframe : { childFrame p with tracker := tracker, logs := logs } = out := by simpa [childFrame, logs] using h
          have shape := (entryShape_iff p out tracker logs).mp hframe
          refine ⟨TransactionState.snapshot p.parent.tracker, (checkpoint_exact_iff _ _).mp rfl, shape.1,
            Or.inr ⟨hv, ?_, ?_⟩⟩
          · rw [shape.2.1]; exact (exactTransfer_iff _ _ _ _ _).mp ht
          · rw [shape.2.2]; simp [logs, EntryLog, transferLog]
    · rintro ⟨checkpoint, hs, shape, zero | nonzero⟩
      · rcases zero with ⟨hv, ht, hl⟩
        have hcheckpoint := (checkpoint_exact_iff _ _).mpr hs
        have hf := (entryShape_iff p out checkpoint []).mpr ⟨shape, ht, hl⟩
        have hbase : childFrame p = out := by simpa [childFrame, hcheckpoint] using hf
        simpa [enterChild, hv] using congrArg (Except.ok (ε := TransactionTransfer.TransferError × Frame.State)) hbase
      · rcases nonzero with ⟨hv, ht, hl⟩
        have hcheckpoint := (checkpoint_exact_iff _ _).mpr hs
        have hmove := (exactTransfer_iff checkpoint _ _ _ _).mpr ht
        have hframe := (entryShape_iff p out out.tracker (EntryLog p)).mpr ⟨shape, rfl, hl⟩
        have hb : (p.request.value == 0) = false := by apply Bool.eq_false_iff.mpr; intro he; apply hv; exact of_decide_eq_true he
        rw [← hcheckpoint] at hmove
        simp only [enterChild, hb, Bool.false_eq_true, ↓reduceIte, childFrame, hmove]
        congr 1
        simpa [childFrame, EntryLog, transferLog] using hframe
  | error e =>
    rcases e with ⟨reason, out⟩
    constructor
    · intro h
      by_cases hv : p.request.value = 0
      · simp [enterChild, hv] at h
      · have hb : (p.request.value == 0) = false := by apply Bool.eq_false_iff.mpr; intro he; apply hv; exact of_decide_eq_true he
        cases ht : TransactionTransfer.moveEther (TransactionState.snapshot p.parent.tracker)
            p.parent.context.environment.currentTarget p.address p.request.value with
        | ok tracker =>
          simp only [enterChild, hb, Bool.false_eq_true, ↓reduceIte, childFrame, ht] at h
          contradiction
        | error err =>
          rcases err with ⟨why, tracker⟩
          simp only [enterChild, hb, Bool.false_eq_true, ↓reduceIte, childFrame] at h
          rw [ht] at h
          simp only [Except.error.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, hframe⟩
          have shape := (entryShape_iff p out tracker []).mp (by simpa [childFrame] using hframe)
          refine ⟨TransactionState.snapshot p.parent.tracker, (checkpoint_exact_iff _ _).mp rfl, shape.1, hv, ?_, shape.2.2⟩
          rw [shape.2.1]
          exact (exactTransfer_iff _ _ _ _ _).mp ht
    · rintro ⟨checkpoint, hs, shape, hv, ht, hl⟩
      have hcheckpoint := (checkpoint_exact_iff _ _).mpr hs
      have hmove := (exactTransfer_iff checkpoint _ _ _ _).mpr ht
      have hframe := (entryShape_iff p out out.tracker []).mpr ⟨shape, rfl, hl⟩
      have hb : (p.request.value == 0) = false := by apply Bool.eq_false_iff.mpr; intro he; apply hv; exact of_decide_eq_true he
      rw [← hcheckpoint] at hmove
      simp only [enterChild, hb, Bool.false_eq_true, ↓reduceIte, childFrame, hmove]
      congr 2
/-- Crediting state gas retains every non-meter frame field. -/
theorem refund_spec_retained (success charged : Bool) (before after : Frame.State)
    (h : RefundSpec success charged before after) :
    after.code = before.code ∧ after.pc = before.pc ∧ after.stack = before.stack ∧
    after.memory = before.memory ∧ after.context = before.context ∧ after.returnData = before.returnData ∧
    after.tracker = before.tracker ∧ after.warmAddresses = before.warmAddresses ∧
    after.warmSlots = before.warmSlots ∧ after.isStatic = before.isStatic ∧ after.logs = before.logs := by
  cases success <;> cases charged <;> simp [RefundSpec, CreditFields] at h <;> simp_all
end EthLib.EVM.NestedRunner
