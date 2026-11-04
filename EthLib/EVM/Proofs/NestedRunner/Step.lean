module

public import EthLib.EVM.Proofs.NestedRunner
public import EthLib.EVM.Proofs.Frame
public import EthLib.EVM.Proofs.CallPreparation
public import EthLib.EVM.Proofs.StaticCall

/-!
# Independent nested transitions

The frame rule and continuation relations specify the current partial runner.
CALL and STATICCALL each have their own route.
Unavailable call features remain tooling results.
-/

@[expose] public section
namespace EthLib.EVM.NestedRunner

/-- Outcomes handled without entering CALL or STATICCALL preparation. -/
def NonCallOutcome : Frame.Outcome → Prop
  | .callRequest _ _ | .staticCallRequest _ _ => False
  | _ => True

/-- Route a non-CALL frame outcome through its caller stack. -/
def NonCallRoute (m : Machine) : Frame.Outcome → Transition → Prop
  | .continue next, result => result = .next { m with frame := next }
  | .stop child, result =>
    match m.callers with
    | [] => result = .done (.terminal (.stopped child))
    | c :: rest => ResumeOutcomeSpec c child true child.gas ByteArray.empty rest result
  | .returned child output, result =>
    match m.callers with
    | [] => result = .done (.terminal (.returned child output))
    | c :: rest => ResumeOutcomeSpec c child true child.gas output rest result
  | .revert child gas output, result =>
    match m.callers with
    | [] => result = .done (.terminal (.reverted child gas output))
    | c :: rest => ResumeOutcomeSpec c child false (gas + child.stateGas.spilled) output rest result
  | .exception child reason, result =>
    if reason = .missingCode ∨ reason = .missingStorageAccount then
      result = .done (.tooling child .incompleteWorld)
    else match m.callers with
      | [] => result = .done (.terminal (.exception child reason))
      | c :: rest => ResumeOutcomeSpec c child false 0 ByteArray.empty rest result
  | .unsupported child op, result => result = .done (.tooling child (.unsupported op))
  | .callRequest _ _, _ => False
  | .staticCallRequest _ _, _ => False

/-- Independent frame rule followed by non-CALL nested routing. -/
def NonCallStep (m : Machine) (result : Transition) : Prop :=
  ∃ outcome, Frame.Rule m.frame outcome ∧ NonCallOutcome outcome ∧ NonCallRoute m outcome result

/-- Non-CALL routing has exactly the stated field and continuation effects. -/
theorem nonCallRoute_iff (m : Machine) (outcome : Frame.Outcome) (result : Transition)
    (h : Frame.step m.frame = outcome) (hn : NonCallOutcome outcome) :
    step m = result ↔ NonCallRoute m outcome result := by
  cases outcome with
  | «continue» next => simp [step, h, NonCallRoute, eq_comm]
  | stop child =>
    cases hc : m.callers with
    | nil => simp [step, h, NonCallRoute, hc, eq_comm]
    | cons c rest => simpa [step, h, NonCallRoute, hc] using resume_iff c child true child.gas ByteArray.empty rest result
  | returned child output =>
    cases hc : m.callers with
    | nil => simp [step, h, NonCallRoute, hc, eq_comm]
    | cons c rest => simpa [step, h, NonCallRoute, hc] using resume_iff c child true child.gas output rest result
  | revert child gas output =>
    cases hc : m.callers with
    | nil => simp [step, h, NonCallRoute, hc, eq_comm]
    | cons c rest => simpa [step, h, NonCallRoute, hc] using resume_iff c child false (gas + child.stateGas.spilled) output rest result
  | exception child reason =>
    cases reason <;> cases hc : m.callers <;> simp [step, h, NonCallRoute, exceptional, hc, resume_iff] <;> exact eq_comm
  | unsupported child op => simp [step, h, NonCallRoute, eq_comm]
  | callRequest input request => cases hn
  | staticCallRequest input request => cases hn

/-- The independent non-CALL relation is equivalent to the corresponding step. -/
theorem nonCallStep_iff (m : Machine) (result : Transition) :
    NonCallStep m result ↔ step m = result ∧ NonCallOutcome (Frame.step m.frame) := by
  constructor
  · rintro ⟨outcome, hrule, hn, hroute⟩
    have hframe := (Frame.step_iff_rule _ _).mpr hrule
    exact ⟨(nonCallRoute_iff m outcome result hframe hn).mpr hroute, hframe ▸ hn⟩
  · rintro ⟨hstep, hn⟩
    refine ⟨Frame.step m.frame, (Frame.step_iff_rule _ _).mp rfl, hn, ?_⟩
    exact (nonCallRoute_iff m _ result rfl hn).mp hstep

/-- Restore a rejected child's grants without changing unrelated fields. -/
def GrantRestore (p : CallPreparation.Prepared) (out : Frame.State) : Prop :=
  out.code = p.parent.code ∧ out.pc = p.parent.pc ∧ out.stack = p.parent.stack ∧
  out.gas = p.parent.gas + p.childGas ∧ out.memory = p.parent.memory ∧
  out.context = p.parent.context ∧ out.returnData = p.parent.returnData ∧
  out.tracker = p.parent.tracker ∧ out.warmAddresses = p.parent.warmAddresses ∧
  out.warmSlots = p.parent.warmSlots ∧ out.isStatic = p.parent.isStatic ∧ out.logs = p.parent.logs ∧
  out.stateGas.reservoir = p.parent.stateGas.reservoir + p.stateGrant ∧
  out.stateGas.baseline = p.parent.stateGas.baseline ∧
  out.stateGas.refundCounter = p.parent.stateGas.refundCounter ∧
  out.stateGas.spilled = p.parent.stateGas.spilled ∧
  out.stateGas.committedSpill = p.parent.stateGas.committedSpill

/-- Grant restoration exactly satisfies the independent field equations. -/
theorem grantRestore_iff (p : CallPreparation.Prepared) (out : Frame.State) :
    { p.parent with gas := p.parent.gas + p.childGas, stateGas := { p.parent.stateGas with reservoir := p.parent.stateGas.reservoir + p.stateGrant } } = out ↔
      GrantRestore p out := by
  constructor
  · intro h; subst out; simp [GrantRestore]
  · intro h
    rcases h with ⟨hc, hpc, hstack, hgas, hm, hctx, hret, ht, ha, hs, hstatic, hlogs,
      hreservoir, hbaseline, hrefund, hspill, hcommitted⟩
    apply ChildSettlement.frame_eq_of_fields <;> simp_all
    cases ho : out.stateGas with
    | mk ores obase orefund ospill ocommitted =>
      cases hp : p.parent.stateGas with
      | mk pres pbase prefund pspill pcommitted =>
        simp only [ho, hp] at hreservoir hbaseline hrefund hspill hcommitted
        simp_all

/-- A rejected call either pushes zero or reports the full stack. -/
def ZeroPushSpec (m : Machine) (credited : Frame.State) : Transition → Prop
  | .next out => credited.stack.val.length < 1024 ∧ out.depth = m.depth ∧ out.callers = m.callers ∧
      out.frame.code = credited.code ∧ out.frame.pc = credited.pc + 1 ∧
      out.frame.stack.val = 0 :: credited.stack.val ∧ out.frame.gas = credited.gas ∧
      out.frame.memory = credited.memory ∧ out.frame.context = credited.context ∧
      out.frame.returnData = credited.returnData ∧ out.frame.tracker = credited.tracker ∧
      out.frame.warmAddresses = credited.warmAddresses ∧ out.frame.warmSlots = credited.warmSlots ∧
      out.frame.isStatic = credited.isStatic ∧ out.frame.stateGas = credited.stateGas ∧ out.frame.logs = credited.logs
  | .done (.tooling diagnostic .invalidContinuation) => credited.stack.val.length = 1024 ∧ diagnostic = credited
  | _ => False

theorem zeroPush_iff (m : Machine) (credited : Frame.State) (result : Transition) :
    (match Stack.push credited.stack 0 with
    | .error _ => .done (.tooling credited .invalidContinuation)
    | .ok stack => .next { m with frame := { credited with stack := stack, pc := credited.pc + 1 } }) = result ↔
    ZeroPushSpec m credited result := by
  cases hp : Stack.push credited.stack 0 with
  | error err =>
    have he : err = .overflow := by
      cases err with
      | overflow => rfl
      | underflow => unfold Stack.push at hp; split at hp <;> cases hp
    subst err
    have hf := (Proofs.Stack.push_overflow_iff _ _).mp hp
    cases result with
    | next out => simp [ZeroPushSpec, Stack.height] at hf ⊢; omega
    | done final =>
      cases final with
      | terminal value => simp [ZeroPushSpec]
      | tooling d reason => cases reason <;> simp_all [ZeroPushSpec, Stack.height, eq_comm]
  | ok stack =>
    have hs := (Proofs.Stack.push_ok_iff _ _ _).mp hp
    cases result with
    | next out =>
      simp only [ZeroPushSpec]
      constructor
      · intro h
        cases h
        simp_all [Stack.height, Stack.toList]
      · intro h
        rcases h with ⟨hr, hd, hcallers, hc, hpc, hstack, hgas, hmem, hctx, hret, ht, ha, hslots, hstatic, hmeter, hlogs⟩
        have hst : stack = out.frame.stack := Subtype.ext (by simpa [Stack.toList] using hs.2.trans hstack.symm)
        cases out with
        | mk frame depth callers =>
          simp only at *
          subst depth
          subst callers
          apply congrArg Transition.next
          apply congrArg (fun frame => Machine.mk frame m.depth m.callers)
          apply ChildSettlement.frame_eq_of_fields <;> simp_all
    | done final =>
      cases final with
      | terminal value => simp [ZeroPushSpec]
      | tooling d reason =>
        cases reason <;> simp_all [ZeroPushSpec, Stack.height, eq_comm]
        omega
/-- Independent grant restoration, refund and zero-status effects. -/
def RejectSpec (m : Machine) (p : CallPreparation.Prepared) (result : Transition) : Prop :=
  ∃ restored credited, GrantRestore p restored ∧ RefundSpec false p.newAccountCharged restored credited ∧
    ZeroPushSpec m credited result

theorem reject_iff (m : Machine) (p : CallPreparation.Prepared) (result : Transition) :
    (let restored := { p.parent with gas := p.parent.gas + p.childGas, stateGas := { p.parent.stateGas with reservoir := p.parent.stateGas.reservoir + p.stateGrant } }
     let credited := refundNewAccount restored p.newAccountCharged
     match Stack.push credited.stack 0 with
     | .error _ => .done (.tooling credited .invalidContinuation)
     | .ok stack => .next { m with frame := { credited with stack := stack, pc := credited.pc + 1 } }) = result ↔
      RejectSpec m p result := by
  let restored : Frame.State := { p.parent with gas := p.parent.gas + p.childGas, stateGas := { p.parent.stateGas with reservoir := p.parent.stateGas.reservoir + p.stateGrant } }
  let credited := refundNewAccount restored p.newAccountCharged
  change (match Stack.push credited.stack 0 with
     | .error _ => .done (.tooling credited .invalidContinuation)
     | .ok stack => .next { m with frame := { credited with stack := stack, pc := credited.pc + 1 } }) = result ↔ _
  constructor
  · intro h
    have hpush := (zeroPush_iff m credited result).mp h
    exact ⟨restored, credited, (grantRestore_iff _ _).mp rfl,
      (refund_spec_iff false _ _ _).mp rfl, hpush⟩
  · rintro ⟨s, t, hs, ht, hp⟩
    have hrs := (grantRestore_iff p s).mpr hs
    have hrt := (refund_spec_iff false p.newAccountCharged s t).mpr ht
    change restored = s at hrs
    subst s
    change credited = t at hrt
    subst t
    exact (zeroPush_iff m credited result).mpr hp
/-- Current precompile addresses are a tooling boundary. -/
def PrecompileAddress (a : World.Address) : Prop := (1 ≤ a.val ∧ a.val ≤ 17) ∨ a.val = 256

theorem precompileAddress_iff (a : World.Address) : isPrecompile a = true ↔ PrecompileAddress a := by
  simp [isPrecompile, PrecompileAddress]

/-- The source gas check selects failure settlement before any hash computation. -/
def RipemdSpec (c : Continuation) (child : Frame.State) (rest : List Continuation) (result : Transition) : Prop :=
  (child.gas < 600 + 120 * ((child.context.data.size + 31) / 32) ∧
    ResumeOutcomeSpec c child false 0 ByteArray.empty rest result) ∨
  (600 + 120 * ((child.context.data.size + 31) / 32) ≤ child.gas ∧
    ResumeOutcomeSpec c child true (child.gas - (600 + 120 * ((child.context.data.size + 31) / 32)))
      (EthLib.Execution.Evm.Precompiles.Ripemd160.ripemd160 child.context.data) rest result)

/-- RIPEMD execution follows the independent gas and settlement cases. -/
theorem ripemdCall_iff (c : Continuation) (child : Frame.State) (rest : List Continuation) (result : Transition) :
    ripemdCall c child rest = result ↔ RipemdSpec c child rest result := by
  by_cases h : child.gas < 600 + 120 * ((child.context.data.size + 31) / 32)
  · simp only [ripemdCall, ripemdGas, ↓reduceIte, RipemdSpec, h, true_and, Nat.not_le_of_gt h, false_and, or_false]
    exact resume_iff _ _ _ _ _ _ _
  · have hl := Nat.le_of_not_gt h
    simp only [ripemdCall, ripemdGas, ↓reduceIte, RipemdSpec, h, false_and, false_or, hl, true_and]
    exact resume_iff _ _ _ _ _ _ _

def EntryDecision (m : Machine) (request : Frame.CallRequest) (p : CallPreparation.Prepared)
    (entry : Except (TransactionTransfer.TransferError × Frame.State) Frame.State) (result : Transition) : Prop :=
  match entry with
  | .error (reason, child) => result = .done (.tooling child (.transfer reason))
  | .ok child =>
    (p.address.val = 3 ∧ RipemdSpec ⟨p.parent, request, m.depth, p.newAccountCharged⟩ child m.callers result) ∨
    (p.address.val ≠ 3 ∧ PrecompileAddress p.address ∧ result = .done (.tooling child .precompile)) ∨
    (p.address.val ≠ 3 ∧ ¬ PrecompileAddress p.address ∧ result = .next ⟨child, m.depth + 1, ⟨p.parent, request, m.depth, p.newAccountCharged⟩ :: m.callers⟩)

def ChildRoute (m : Machine) (request : Frame.CallRequest) (p : CallPreparation.Prepared) (result : Transition) : Prop :=
  ∃ entry, EntrySpec p entry ∧ EntryDecision m request p entry result

theorem entryDecision_iff (m : Machine) (request : Frame.CallRequest) (p : CallPreparation.Prepared)
    (entry : Except (TransactionTransfer.TransferError × Frame.State) Frame.State) (result : Transition) :
    (match entry with
    | .error (reason, child) => .done (.tooling child (.transfer reason))
    | .ok child => if p.address.val == 3 then
        ripemdCall ⟨p.parent, request, m.depth, p.newAccountCharged⟩ child m.callers
      else if isPrecompile p.address then .done (.tooling child .precompile)
      else .next ⟨child, m.depth + 1, ⟨p.parent, request, m.depth, p.newAccountCharged⟩ :: m.callers⟩) = result ↔
      EntryDecision m request p entry result := by
  cases entry with
  | error err => cases err; simp [EntryDecision, eq_comm]
  | ok child =>
    by_cases h3 : p.address.val = 3
    · simp only [EntryDecision, h3, true_and, ne_eq, not_true_eq_false, false_and, or_false]
      exact ripemdCall_iff _ _ _ _
    · have hb : (p.address.val == 3) = false := beq_eq_false_iff_ne.mpr h3
      by_cases hp : PrecompileAddress p.address
      · have hc := (precompileAddress_iff p.address).mpr hp
        simp [EntryDecision, hb, h3, hc, hp, eq_comm]
      · have hc : isPrecompile p.address = false := by
          cases he : isPrecompile p.address <;> simp_all [precompileAddress_iff]
        simp [EntryDecision, hb, h3, hc, hp, eq_comm]

theorem childRoute_iff (m : Machine) (request : Frame.CallRequest) (p : CallPreparation.Prepared) (result : Transition) :
    (match enterChild p with
    | .error (reason, child) => .done (.tooling child (.transfer reason))
    | .ok child => if p.address.val == 3 then
        ripemdCall ⟨p.parent, request, m.depth, p.newAccountCharged⟩ child m.callers
      else if isPrecompile p.address then .done (.tooling child .precompile)
      else .next ⟨child, m.depth + 1, ⟨p.parent, request, m.depth, p.newAccountCharged⟩ :: m.callers⟩) = result ↔
      ChildRoute m request p result := by
  constructor
  · intro h
    exact ⟨enterChild p, (entry_iff p _).mp rfl, (entryDecision_iff _ _ _ _ _).mp h⟩
  · rintro ⟨entry, he, hr⟩
    have eq := (entry_iff p entry).mpr he
    rw [eq]
    exact (entryDecision_iff _ _ _ _ _).mpr hr
/-- Depth and balance rejection precede child entry. -/
def PreparedRoute (m : Machine) (request : Frame.CallRequest) (p : CallPreparation.Prepared) (result : Transition) : Prop :=
  ((1024 < m.depth + 1 ∨ p.insufficientBalance = true) ∧ RejectSpec m p result) ∨
  (m.depth + 1 ≤ 1024 ∧ p.insufficientBalance = false ∧ ChildRoute m request p result)

theorem preparedRoute_iff (m : Machine) (request : Frame.CallRequest) (p : CallPreparation.Prepared) (result : Transition) :
    (if m.depth + 1 > 1024 || p.insufficientBalance then
        let restored := { p.parent with gas := p.parent.gas + p.childGas, stateGas := { p.parent.stateGas with reservoir := p.parent.stateGas.reservoir + p.stateGrant } }
        let restored := refundNewAccount restored p.newAccountCharged
        match Stack.push restored.stack 0 with
        | .error _ => .done (.tooling restored .invalidContinuation)
        | .ok stack => .next { m with frame := { restored with stack, pc := restored.pc + 1 } }
      else
        match enterChild p with
        | .error (reason, child) => .done (.tooling child (.transfer reason))
        | .ok child => if p.address.val == 3 then
        ripemdCall ⟨p.parent, request, m.depth, p.newAccountCharged⟩ child m.callers
      else if isPrecompile p.address then .done (.tooling child .precompile)
          else .next ⟨child, m.depth + 1, ⟨p.parent, request, m.depth, p.newAccountCharged⟩ :: m.callers⟩) = result ↔
      PreparedRoute m request p result := by
  by_cases hd : 1024 < m.depth + 1
  · simp only [hd, decide_true, Bool.true_or, ↓reduceIte, PreparedRoute, true_or, true_and, Nat.not_le_of_gt hd, false_and, or_false]
    exact reject_iff m p result
  · have hl : m.depth + 1 ≤ 1024 := Nat.le_of_not_gt hd
    cases hb : p.insufficientBalance with
    | false =>
      simp only [hd, decide_false, Bool.false_or, hb, Bool.false_eq_true, ↓reduceIte, PreparedRoute, false_or, false_and, or_false, hl, true_and]
      exact childRoute_iff m request p result
    | true =>
      simp only [hd, decide_false, Bool.false_or, hb, ↓reduceIte, PreparedRoute, or_true, true_and, Bool.true_eq_false, false_and, and_false, or_false]
      exact reject_iff m p result
/-- An exceptional child either terminates or enters independent settlement. -/
def ExceptionalRoute (m : Machine) (child : Frame.State) (reason : Frame.Exception) (result : Transition) : Prop :=
  match m.callers with
  | [] => result = .done (.terminal (.exception child reason))
  | c :: rest => ResumeOutcomeSpec c child false 0 ByteArray.empty rest result

theorem exceptionalRoute_iff (m : Machine) (child : Frame.State) (reason : Frame.Exception) (result : Transition) :
    exceptional child reason m.callers = result ↔ ExceptionalRoute m child reason result := by
  cases hc : m.callers with
  | nil => simp [exceptional, ExceptionalRoute, hc, eq_comm]
  | cons c rest => simpa [exceptional, ExceptionalRoute, hc] using resume_iff c child false 0 ByteArray.empty rest result

def CallDecision (m : Machine) (request : Frame.CallRequest) (prep : CallPreparation.Result) (result : Transition) : Prop :=
  match prep with
  | .outOfGas diagnostic => ExceptionalRoute m diagnostic .outOfGas result
  | .tooling diagnostic reason => result = .done (.tooling diagnostic (.preparation reason))
  | .ready p => PreparedRoute m request p result

def CallRoute (m : Machine) (input : Frame.State) (request : Frame.CallRequest) (result : Transition) : Prop :=
  ∃ prep, CallPreparation.OutcomeSpec input request prep ∧ CallDecision m request prep result

theorem callDecision_iff (m : Machine) (request : Frame.CallRequest) (prep : CallPreparation.Result) (result : Transition) :
    (match prep with
    | .outOfGas diagnostic => exceptional diagnostic .outOfGas m.callers
    | .tooling diagnostic reason => .done (.tooling diagnostic (.preparation reason))
    | .ready p =>
      if m.depth + 1 > 1024 || p.insufficientBalance then
        let restored := { p.parent with gas := p.parent.gas + p.childGas, stateGas := { p.parent.stateGas with reservoir := p.parent.stateGas.reservoir + p.stateGrant } }
        let restored := refundNewAccount restored p.newAccountCharged
        match Stack.push restored.stack 0 with
        | .error _ => .done (.tooling restored .invalidContinuation)
        | .ok stack => .next { m with frame := { restored with stack, pc := restored.pc + 1 } }
      else match enterChild p with
        | .error (reason, child) => .done (.tooling child (.transfer reason))
        | .ok child => if p.address.val == 3 then
        ripemdCall ⟨p.parent, request, m.depth, p.newAccountCharged⟩ child m.callers
      else if isPrecompile p.address then .done (.tooling child .precompile)
          else .next ⟨child, m.depth + 1, ⟨p.parent, request, m.depth, p.newAccountCharged⟩ :: m.callers⟩) = result ↔
      CallDecision m request prep result := by
  cases prep with
  | outOfGas diagnostic => exact exceptionalRoute_iff m diagnostic .outOfGas result
  | tooling diagnostic reason => simp [CallDecision, eq_comm]
  | ready p => exact preparedRoute_iff m request p result

theorem callRoute_iff (m : Machine) (input : Frame.State) (request : Frame.CallRequest) (result : Transition)
    (hframe : Frame.step m.frame = .callRequest input request) :
    step m = result ↔ CallRoute m input request result := by
  simp only [step, hframe]
  constructor
  · intro h
    exact ⟨CallPreparation.prepare input request, (CallPreparation.prepare_iff _ _ _).mp rfl,
      (callDecision_iff _ _ _ _).mp h⟩
  · rintro ⟨prep, hp, hr⟩
    have he := (CallPreparation.prepare_iff input request prep).mpr hp
    rw [he]
    exact (callDecision_iff _ _ _ _).mpr hr

/-- Depth rejection returns both grants and pushes zero, with no state-gas refund. -/
def StaticRejectSpec (m : Machine) (p : CallPreparation.Prepared) (result : Transition) : Prop :=
  ∃ restored, GrantRestore p restored ∧ ZeroPushSpec m restored result

theorem staticReject_iff (m : Machine) (p : CallPreparation.Prepared) (result : Transition) :
    (let restored := { p.parent with gas := p.parent.gas + p.childGas, stateGas := { p.parent.stateGas with reservoir := p.parent.stateGas.reservoir + p.stateGrant } }
     match Stack.push restored.stack 0 with
     | .error _ => .done (.tooling restored .invalidContinuation)
     | .ok stack => .next { m with frame := { restored with stack, pc := restored.pc + 1 } }) = result ↔
      StaticRejectSpec m p result := by
  constructor
  · intro h
    exact ⟨_, (grantRestore_iff p _).mp rfl, (zeroPush_iff m _ result).mp h⟩
  · rintro ⟨restored, hr, hz⟩
    have he := (grantRestore_iff p restored).mpr hr
    subst restored
    exact (zeroPush_iff m _ result).mpr hz

/-- Independent STATICCALL child fields: a zero-value checkpointed entry with the static flag set. -/
def StaticEntry (p : CallPreparation.Prepared) (out : Frame.State) : Prop :=
  out.code = p.code ∧ out.pc = 0 ∧ out.stack = Stack.empty ∧ out.gas = p.childGas ∧
  out.memory = Memory.Allocation.empty ∧ out.returnData = ByteArray.empty ∧
  out.context.environment = { p.parent.context.environment with
    currentTarget := p.address, caller := p.parent.context.environment.currentTarget, value := p.request.value } ∧
  Frame.FinishBytes p.parent p.request.inputOffset p.request.inputSize out.context.data ∧
  CheckpointExact p.parent.tracker out.tracker ∧
  out.warmAddresses = p.parent.warmAddresses ∧ out.warmSlots = p.parent.warmSlots ∧
  out.isStatic = true ∧ out.stateGas = ⟨p.stateGrant, p.stateGrant, 0, 0, 0⟩ ∧ out.logs = []

theorem staticEntry_iff (p : CallPreparation.Prepared) (out : Frame.State) :
    staticChildFrame p = out ↔ StaticEntry p out := by
  constructor
  · intro h
    subst out
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, Frame.finish_bytes _ _ _, (checkpoint_exact_iff _ _).mp rfl,
      rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨hc, hpc, hstack, hgas, hmem, hret, henv, hbytes, hcheck, hwarm, hslots, hstatic, hmeter, hlogs⟩
    have hb := inputBytes_unique p.parent p.request.inputOffset p.request.inputSize out.context.data
      ⟨(Memory.readRange p.parent.memory.store p.request.inputOffset.toNat p.request.inputSize.toNat).toArray⟩
      hbytes (Frame.finish_bytes _ _ _)
    have ht := (checkpoint_exact_iff _ _).mpr hcheck
    apply ChildSettlement.frame_eq_of_fields <;> simp_all [staticChildFrame, childFrame]
    cases hctx : out.context with
    | mk data env => simp only [hctx] at hb henv; simp_all

/-- After the depth check the callee address selects RIPEMD, a tooling precompile or a new child. -/
def StaticChildDecision (m : Machine) (request : Frame.CallRequest) (p : CallPreparation.Prepared)
    (child : Frame.State) (result : Transition) : Prop :=
  (p.address.val = 3 ∧ RipemdSpec ⟨p.parent, request, m.depth, false⟩ child m.callers result) ∨
  (p.address.val ≠ 3 ∧ PrecompileAddress p.address ∧ result = .done (.tooling child .precompile)) ∨
  (p.address.val ≠ 3 ∧ ¬ PrecompileAddress p.address ∧
    result = .next ⟨child, m.depth + 1, ⟨p.parent, request, m.depth, false⟩ :: m.callers⟩)

theorem staticChildDecision_iff (m : Machine) (request : Frame.CallRequest) (p : CallPreparation.Prepared)
    (child : Frame.State) (result : Transition) :
    (if p.address.val == 3 then ripemdCall ⟨p.parent, request, m.depth, false⟩ child m.callers
      else if isPrecompile p.address then .done (.tooling child .precompile)
      else .next ⟨child, m.depth + 1, ⟨p.parent, request, m.depth, false⟩ :: m.callers⟩) = result ↔
      StaticChildDecision m request p child result := by
  by_cases h3 : p.address.val = 3
  · simp only [StaticChildDecision, h3, true_and, ne_eq, not_true_eq_false, false_and, or_false]
    exact ripemdCall_iff _ _ _ _
  · have hb : (p.address.val == 3) = false := beq_eq_false_iff_ne.mpr h3
    by_cases hp : PrecompileAddress p.address
    · have hc := (precompileAddress_iff p.address).mpr hp
      simp [StaticChildDecision, hb, h3, hc, hp, eq_comm]
    · have hc : isPrecompile p.address = false := by
        cases he : isPrecompile p.address <;> simp_all [precompileAddress_iff]
      simp [StaticChildDecision, hb, h3, hc, hp, eq_comm]

/-- The STATICCALL lifecycle after preparation: depth rejection or child entry. -/
def StaticDecision (m : Machine) (request : Frame.CallRequest) (p : CallPreparation.Prepared)
    (result : Transition) : Prop :=
  (1024 < m.depth + 1 ∧ StaticRejectSpec m p result) ∨
  (m.depth + 1 ≤ 1024 ∧ ∃ child, StaticEntry p child ∧ StaticChildDecision m request p child result)

theorem staticDispatch_iff (m : Machine) (request : Frame.CallRequest) (p : CallPreparation.Prepared)
    (result : Transition) : staticDispatch m request p = result ↔ StaticDecision m request p result := by
  by_cases hd : 1024 < m.depth + 1
  · simp only [staticDispatch, hd, ↓reduceIte, StaticDecision, true_and, Nat.not_le_of_gt hd, false_and, or_false]
    exact staticReject_iff m p result
  · have hl : m.depth + 1 ≤ 1024 := Nat.le_of_not_gt hd
    simp only [staticDispatch, hd, ↓reduceIte, StaticDecision, false_and, false_or, hl, true_and]
    constructor
    · intro h
      exact ⟨staticChildFrame p, (staticEntry_iff p _).mp rfl,
        (staticChildDecision_iff m request p _ result).mp h⟩
    · rintro ⟨child, he, hr⟩
      have heq := (staticEntry_iff p child).mpr he
      subst child
      exact (staticChildDecision_iff m request p _ result).mpr hr

/-- Preparation failures route like CALL; a ready preparation enters the static lifecycle. -/
def StaticPrepDecision (m : Machine) (request : Frame.CallRequest) (prep : CallPreparation.Result)
    (result : Transition) : Prop :=
  match prep with
  | .outOfGas diagnostic => ExceptionalRoute m diagnostic .outOfGas result
  | .tooling diagnostic reason => result = .done (.tooling diagnostic (.preparation reason))
  | .ready p => StaticDecision m request p result

def StaticRoute (m : Machine) (input : Frame.State) (request : Frame.CallRequest) (result : Transition) : Prop :=
  ∃ prep, StaticCall.OutcomeSpec input request prep ∧ StaticPrepDecision m request prep result

theorem staticPrepDecision_iff (m : Machine) (request : Frame.CallRequest) (prep : CallPreparation.Result)
    (result : Transition) :
    (match prep with
    | .outOfGas diagnostic => exceptional diagnostic .outOfGas m.callers
    | .tooling diagnostic reason => .done (.tooling diagnostic (.preparation reason))
    | .ready p => staticDispatch m request p) = result ↔
      StaticPrepDecision m request prep result := by
  cases prep with
  | outOfGas diagnostic => exact exceptionalRoute_iff m diagnostic .outOfGas result
  | tooling diagnostic reason => simp [StaticPrepDecision, eq_comm]
  | ready p => exact staticDispatch_iff m request p result

theorem staticRoute_iff (m : Machine) (input : Frame.State) (request : Frame.CallRequest) (result : Transition)
    (hframe : Frame.step m.frame = .staticCallRequest input request) :
    step m = result ↔ StaticRoute m input request result := by
  simp only [step, hframe]
  constructor
  · intro h
    exact ⟨StaticCall.prepare input request, (StaticCall.prepare_iff _ _ _).mp rfl,
      (staticPrepDecision_iff _ _ _ _).mp h⟩
  · rintro ⟨prep, hp, hr⟩
    have he := (StaticCall.prepare_iff input request prep).mpr hp
    rw [he]
    exact (staticPrepDecision_iff _ _ _ _).mpr hr

def StepSpec (m : Machine) (result : Transition) : Prop :=
  ∃ outcome, Frame.Rule m.frame outcome ∧
    match outcome with
    | .callRequest input request => CallRoute m input request result
    | .staticCallRequest input request => StaticRoute m input request result
    | _ => NonCallRoute m outcome result

theorem step_iff_spec (m : Machine) (result : Transition) : step m = result ↔ StepSpec m result := by
  constructor
  · intro h
    refine ⟨Frame.step m.frame, (Frame.step_iff_rule _ _).mp rfl, ?_⟩
    cases hframe : Frame.step m.frame with
    | callRequest input request => exact (callRoute_iff m input request result hframe).mp h
    | staticCallRequest input request => exact (staticRoute_iff m input request result hframe).mp h
    | «continue» s => exact (nonCallRoute_iff m _ result hframe trivial).mp h
    | stop s => exact (nonCallRoute_iff m _ result hframe trivial).mp h
    | returned s bytes => exact (nonCallRoute_iff m _ result hframe trivial).mp h
    | revert s gas bytes => exact (nonCallRoute_iff m _ result hframe trivial).mp h
    | exception s reason => exact (nonCallRoute_iff m _ result hframe trivial).mp h
    | unsupported s op => exact (nonCallRoute_iff m _ result hframe trivial).mp h
  · rintro ⟨outcome, hrule, hroute⟩
    have hframe := (Frame.step_iff_rule _ _).mpr hrule
    cases outcome with
    | callRequest input request => exact (callRoute_iff m input request result hframe).mpr hroute
    | staticCallRequest input request => exact (staticRoute_iff m input request result hframe).mpr hroute
    | «continue» s => exact (nonCallRoute_iff m _ result hframe trivial).mpr hroute
    | stop s => exact (nonCallRoute_iff m _ result hframe trivial).mpr hroute
    | returned s bytes => exact (nonCallRoute_iff m _ result hframe trivial).mpr hroute
    | revert s gas bytes => exact (nonCallRoute_iff m _ result hframe trivial).mpr hroute
    | exception s reason => exact (nonCallRoute_iff m _ result hframe trivial).mpr hroute
    | unsupported s op => exact (nonCallRoute_iff m _ result hframe trivial).mpr hroute
/-- Bounded execution expressed only through independent nested step rules. -/
inductive RuleTrace : Nat → Machine → Result → Prop where
  | exhausted (m) : RuleTrace 0 m (.exhausted m)
  | done {fuel m final} : StepSpec m (.done final) → RuleTrace (fuel + 1) m final.result
  | next {fuel m next result} : StepSpec m (.next next) → RuleTrace fuel next result →
      RuleTrace (fuel + 1) m result

/-- Every finite executable run has an independent rule trace. -/
theorem run_ruleTrace (fuel : Nat) (m : Machine) : RuleTrace fuel m (run fuel m) := by
  induction fuel generalizing m with
  | zero => exact .exhausted m
  | succ fuel ih =>
    cases hs : step m with
    | done final =>
      have hr := (step_iff_spec m (.done final)).mp hs
      simpa [run, hs] using (RuleTrace.done (fuel := fuel) hr)
    | next next =>
      have hr := (step_iff_spec m (.next next)).mp hs
      simpa [run, hs] using (RuleTrace.next hr (ih next))

/-- Each independent trace determines the bounded result. -/
theorem run_of_ruleTrace {fuel : Nat} {m : Machine} {result : Result}
    (h : RuleTrace fuel m result) : run fuel m = result := by
  induction h with
  | exhausted m => rfl
  | done hr =>
    have hs := (step_iff_spec _ _).mpr hr
    simp [run, hs]
  | next hr _ ih =>
    have hs := (step_iff_spec _ _).mpr hr
    simpa [run, hs] using ih

/-- Bounded nested execution and independent rule traces are equivalent. -/
theorem run_iff_ruleTrace (fuel : Nat) (m : Machine) (result : Result) :
    run fuel m = result ↔ RuleTrace fuel m result := by
  constructor
  · intro h; rw [← h]; exact run_ruleTrace fuel m
  · exact run_of_ruleTrace

/-- Splitting fuel resumes the machine retained by an exhaustion trace. -/
theorem ruleTrace_split (fuel extra : Nat) (m next : Machine) (result : Result)
    (first : RuleTrace fuel m (.exhausted next)) :
    RuleTrace (fuel + extra) m result ↔ RuleTrace extra next result := by
  rw [← run_iff_ruleTrace, ← run_iff_ruleTrace, run_add, run_of_ruleTrace first]

/-- A completed final result is stable when more fuel is supplied. -/
theorem ruleTrace_final_extra (fuel extra : Nat) (m : Machine) (final : Final)
    (h : RuleTrace fuel m final.result) : RuleTrace (fuel + extra) m final.result := by
  apply (run_iff_ruleTrace _ _ _).mp
  rw [run_add, run_of_ruleTrace h]
  cases final <;> rfl
end EthLib.EVM.NestedRunner
