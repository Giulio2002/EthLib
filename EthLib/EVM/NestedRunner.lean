module

public import EthLib.EVM.Runner
public import EthLib.EVM.CallPreparation
public import EthLib.EVM.StaticCall
public import EthLib.Execution.Evm.Precompiles.Ripemd160

/-!
# Fuel-bounded nested CALL execution

This is an incomplete Amsterdam CALL and STATICCALL path for nondelegated calls.
Delegation and unavailable precompiles are tooling outcomes.
CALLCODE, DELEGATECALL and the CREATE family remain unsupported instructions.
Fuel bounds the whole machine, including child and continuation steps.
-/

@[expose] public section
namespace EthLib.EVM.NestedRunner

/-- A suspended parent and its output range. -/
structure Continuation where
  parent : Frame.State
  request : Frame.CallRequest
  depth : Nat
  newAccountCharged : Bool

/-- Explicit unavailable features and invalid interface states. -/
inductive Tooling where
  | preparation (reason : CallPreparation.Tooling)
  | precompile | unsupported (op : Opcode) | incompleteWorld | invalidContinuation
  | transfer (reason : TransactionTransfer.TransferError)
  deriving DecidableEq, Repr

/-- Recognize the Amsterdam precompile address set. -/
def isPrecompile (address : World.Address) : Bool :=
  (1 ≤ address.val && address.val ≤ 17) || address.val == 256

/-- Parent and child execution state, with the caller-supplied current depth. -/
structure Machine where
  frame : Frame.State
  depth : Nat
  callers : List Continuation

/-- A terminal result is distinct from fuel exhaustion and tooling failure. -/
inductive Result where
  | terminal (result : Runner.Result)
  | exhausted (machine : Machine)
  | tooling (frame : Frame.State) (reason : Tooling)

/-- A completed transition cannot itself manufacture fuel exhaustion. -/
inductive Final where
  | terminal (result : Runner.Result)
  | tooling (frame : Frame.State) (reason : Tooling)

/-- Embed a completed transition into a bounded-run result. -/
def Final.result : Final → Result
  | .terminal result => .terminal result
  | .tooling frame reason => .tooling frame reason

/-- A machine transition may continue, finish or stop at a tooling boundary. -/
inductive Transition where
  | next (machine : Machine)
  | done (result : Final)

/-- Build a child after the CALL preparation and checkpoint. -/
def childFrame (p : CallPreparation.Prepared) : Frame.State :=
  let env := p.parent.context.environment
  let context : CallData.Context :=
    ⟨⟨(Memory.readRange p.parent.memory.store p.request.inputOffset.toNat
      p.request.inputSize.toNat).toArray⟩,
      { env with currentTarget := p.address, caller := env.currentTarget, value := p.request.value }⟩
  { code := p.code, pc := 0, stack := Stack.empty, gas := p.childGas,
    memory := Memory.Allocation.empty,
    memoryValid := by intro a h; rfl,
    context := context, returnData := ByteArray.empty,
    tracker := TransactionState.snapshot p.parent.tracker,
    warmAddresses := p.parent.warmAddresses, warmSlots := p.parent.warmSlots,
    isStatic := p.parent.isStatic,
    stateGas := ⟨p.stateGrant, p.stateGrant, 0, 0, 0⟩, logs := [] }

/-- Amsterdam `vm/__init__.py`, `emit_transfer_log`, EIP-7708. -/
def transferLog (sender recipient : World.Address) (amount : Word) : Frame.LogEntry :=
  ⟨⟨2 ^ 160 - 2, by decide⟩,
    [Frame.logTopic (World.codeHash "Transfer(address,address,uint256)".toUTF8),
     Frame.logTopic (Environment.addressWord sender), Frame.logTopic (Environment.addressWord recipient)],
    amount.toBytesBE⟩

/-- Transfer after the tracker snapshot, before executing the child code. -/
def enterChild (p : CallPreparation.Prepared) : Except (TransactionTransfer.TransferError × Frame.State) Frame.State :=
  let child := childFrame p
  if p.request.value == 0 then .ok child else
  let sender := p.parent.context.environment.currentTarget
  match TransactionTransfer.moveEther child.tracker sender p.address p.request.value with
  | .error (reason, tracker) => .error (reason, { child with tracker })
  | .ok tracker =>
    let logs := if sender == p.address then [] else [transferLog sender p.address p.request.value]
    .ok { child with tracker, logs }

/-- Refund a failed call's new-account state charge after incorporation. -/
def refundNewAccount (parent : Frame.State) (charged : Bool) : Frame.State :=
  if charged then Frame.withStateMeter parent (Gas.StateMeter.creditState (Frame.stateMeter parent) 183600)
  else parent

/-- Resume a parent after incorporating a protocol child result. -/
def resume (c : Continuation) (child : Frame.State) (success : Bool)
    (gas : Nat) (output : ByteArray) (rest : List Continuation) : Transition :=
  match ChildSettlement.settleChild c.parent child success gas output with
  | .error _ => .done (.tooling child .invalidContinuation)
  | .ok incorporated =>
    let parent := if success then incorporated else refundNewAccount incorporated c.newAccountCharged
    let bytes := output.data.toList.take c.request.outputSize.toNat
    let memory := Memory.Allocation.write parent.memory c.request.outputOffset.toNat bytes
    let valid := Memory.Allocation.write_valid_for_frame _ _ _ parent.memoryValid
    match Stack.push parent.stack (if success then 1 else 0) with
    | .error _ => .done (.tooling parent .invalidContinuation)
    | .ok stack => .next ⟨{ parent with
        memory := memory, memoryValid := valid, stack := stack, pc := parent.pc + 1 }, c.depth, rest⟩

/-- Amsterdam `vm/precompiled_contracts/ripemd160.py` and `vm/gas.py`. -/
def ripemdGas (data : ByteArray) : Nat := 600 + 120 * ((data.size + 31) / 32)

/-- Charge the child before hashing, then incorporate success or exceptional failure. -/
def ripemdCall (c : Continuation) (child : Frame.State) (rest : List Continuation) : Transition :=
  let cost := ripemdGas child.context.data
  if child.gas < cost then resume c child false 0 ByteArray.empty rest
  else resume c child true (child.gas - cost)
    (EthLib.Execution.Evm.Precompiles.Ripemd160.ripemd160 child.context.data) rest

/-- An exceptional child rolls back before its parent resumes. -/
def exceptional (child : Frame.State) (reason : Frame.Exception)
    (callers : List Continuation) : Transition :=
  match callers with
  | [] => .done (.terminal (.exception child reason))
  | c :: rest => resume c child false 0 ByteArray.empty rest

/-- Build a STATICCALL child.

Amsterdam `generic_call` sets `is_static` to `is_staticcall or evm.is_static`, which is true here.
The value is zero, so `process_message` moves no ether and the child keeps the checkpoint tracker.
-/
def staticChildFrame (p : CallPreparation.Prepared) : Frame.State :=
  { childFrame p with isStatic := true }

/-- Amsterdam `generic_call` after STATICCALL preparation.

The only preflight check is the depth limit, because STATICCALL has no balance check.
No new-account charge exists, so a rejected or failed call refunds no state gas.
-/
def staticDispatch (m : Machine) (request : Frame.CallRequest) (p : CallPreparation.Prepared) : Transition :=
  if m.depth + 1 > 1024 then
    -- `restore_child_gas` returns both grants, then the parent pushes zero.
    let restored := { p.parent with
      gas := p.parent.gas + p.childGas,
      stateGas := { p.parent.stateGas with reservoir := p.parent.stateGas.reservoir + p.stateGrant } }
    match Stack.push restored.stack 0 with
    | .error _ => .done (.tooling restored .invalidContinuation)
    | .ok stack => .next { m with frame := { restored with stack, pc := restored.pc + 1 } }
  else
    let child := staticChildFrame p
    let c : Continuation := ⟨p.parent, request, m.depth, false⟩
    if p.address.val == 3 then ripemdCall c child m.callers
    else if isPrecompile p.address then .done (.tooling child .precompile)
    else .next ⟨child, m.depth + 1, c :: m.callers⟩

/-- One step of the nested machine. -/
def step (m : Machine) : Transition :=
  match Frame.step m.frame with
  | .continue next => .next { m with frame := next }
  | .stop child =>
    match m.callers with
    | [] => .done (.terminal (.stopped child))
    | c :: rest => resume c child true child.gas ByteArray.empty rest
  | .returned child output =>
    match m.callers with
    | [] => .done (.terminal (.returned child output))
    | c :: rest => resume c child true child.gas output rest
  | .revert child gas output =>
    match m.callers with
    | [] => .done (.terminal (.reverted child gas output))
    | c :: rest => resume c child false (gas + child.stateGas.spilled) output rest
  | .exception child .missingCode | .exception child .missingStorageAccount =>
    .done (.tooling child .incompleteWorld)
  | .exception child reason => exceptional child reason m.callers
  | .unsupported child op => .done (.tooling child (.unsupported op))
  | .callRequest input request =>
    match CallPreparation.prepare input request with
    | .outOfGas diagnostic => exceptional diagnostic .outOfGas m.callers
    | .tooling diagnostic reason => .done (.tooling diagnostic (.preparation reason))
    | .ready p =>
      if m.depth + 1 > 1024 || p.insufficientBalance then
        let restored := { p.parent with
          gas := p.parent.gas + p.childGas, stateGas := { p.parent.stateGas with reservoir := p.parent.stateGas.reservoir + p.stateGrant } }
        let restored := refundNewAccount restored p.newAccountCharged
        match Stack.push restored.stack 0 with
        | .error _ => .done (.tooling restored .invalidContinuation)
        | .ok stack => .next { m with frame := { restored with stack, pc := restored.pc + 1 } }
      else
        match enterChild p with
        | .error (reason, child) => .done (.tooling child (.transfer reason))
        | .ok child =>
          if p.address.val == 3 then
            ripemdCall ⟨p.parent, request, m.depth, p.newAccountCharged⟩ child m.callers
          else if isPrecompile p.address then .done (.tooling child .precompile)
          else .next ⟨child, m.depth + 1, ⟨p.parent, request, m.depth, p.newAccountCharged⟩ :: m.callers⟩
  | .staticCallRequest input request =>
    match StaticCall.prepare input request with
    | .outOfGas diagnostic => exceptional diagnostic .outOfGas m.callers
    | .tooling diagnostic reason => .done (.tooling diagnostic (.preparation reason))
    | .ready p => staticDispatch m request p

/-- Execute up to `fuel` machine transitions, including nested calls. -/
def run : Nat → Machine → Result
  | 0, m => .exhausted m
  | fuel + 1, m =>
    match step m with
    | .done result => result.result
    | .next next => run fuel next

end EthLib.EVM.NestedRunner
