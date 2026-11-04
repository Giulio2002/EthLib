module

public import EthLib.EVM.TransactionTracker
public import EthLib.EVM.TransactionAccount
public import EthLib.EVM.CallData
public import EthLib.EVM.ReturnData
public import EthLib.EVM.Stack
public import EthLib.EVM.PushImmediate
public import EthLib.EVM.StackImmediate
public import EthLib.EVM.JumpDest
public import EthLib.EVM.Gas
public import EthLib.EVM.Gas.StateMeter
public import EthLib.EVM.Memory.Invariant
public import EthLib.EVM.Word.AddMulMod
public import EthLib.EVM.Word.Exp
public import EthLib.EVM.Word.DivMod
public import EthLib.EVM.Word.SignedDivMod
public import EthLib.EVM.Word.Comparisons
public import EthLib.EVM.Word.Bitwise
public import EthLib.EVM.Word.Shifts
public import EthLib.EVM.Word.ByteSignExtend
public import EthLib.Cryptography.Hash.Keccak

/-!
# Frame instruction subset

The instruction rules come from Cancun execution-specs revision
`fd9298410ec7218838c8348f69c1eb633f1797dc`, `vm/interpreter.py`,
`vm/instructions/stack.py`, `arithmetic.py`, `comparison.py`, `bitwise.py`,
`control_flow.py`, `memory.py`, `block.py`, `environment.py`, and `vm/gas.py`.
Amsterdam `vm/instructions/block.py`, `slot_number`, defines SLOTNUM at the same revision.
Amsterdam `vm/instructions/stack.py` defines DUPN, SWAPN and EXCHANGE.
The blob fee observation uses the supplied schedule, which can differ from Cancun.
An exception carries a diagnostic frame, including reads performed before failure.
Its gas is zero at the message boundary; its stack is not a protocol final state.
Unsupported instructions are a tooling result and do not execute.
-/

@[expose] public section
namespace EthLib.EVM.Frame

/-- State-gas fields supplied at frame entry; execution gas is held in `State.gas`. -/
structure StateGas where
  reservoir : Nat := 0
  baseline : Nat := 0
  refundCounter : Int := 0
  spilled : Nat := 0
  committedSpill : Nat := 0
  deriving DecidableEq, Repr

/-- Amsterdam `blocks.py`, `Log`, at revision
`fd9298410ec7218838c8348f69c1eb633f1797dc`.
Topics are the big-endian 32-byte encodings of stack words. -/
structure LogEntry where
  address : World.Address
  topics : List { bytes : ByteArray // bytes.size = 32 }
  data : ByteArray
  deriving DecidableEq

/-- The fields used by this instruction subset. -/
structure State where
  code : ByteArray
  pc : Nat
  stack : Stack
  gas : Nat
  memory : Memory.Allocation.State
  memoryValid : Memory.Allocation.Valid memory
  context : CallData.Context
  returnData : ByteArray
  tracker : TransactionState.State
  warmAddresses : List World.Address
  warmSlots : List (World.Address × Word)
  isStatic : Bool := false
  stateGas : StateGas := {}
  logs : List LogEntry := []

/-- Operands removed by Amsterdam `instructions/system.py`, `call` or `staticcall`.

STATICCALL has no value operand, so its request carries value zero. -/
structure CallRequest where
  gas : Word
  address : Word
  value : Word
  inputOffset : Word
  inputSize : Word
  outputOffset : Word
  outputSize : Word

/-- Exceptional halts distinguished by their first failing check. -/
inductive Exception where
  | invalidOpcode | invalidJumpDestination | outOfGas | stackUnderflow | stackOverflow | outOfBoundsRead | invalidParameter
  | writeInStaticContext | missingStorageAccount | missingCode
  deriving DecidableEq, Repr

/-- Frame outcomes include a typed revert for future semantics.

The carried frame is diagnostic and does not represent world-state rollback.
Unsupported instructions are tooling outcomes. -/
inductive Outcome where
  | continue (state : State)
  | stop (state : State)
  | returned (state : State) (output : ByteArray)
  | revert (input : State) (gas : Nat) (output : ByteArray)
  | exception (input : State) (reason : Exception)
  | unsupported (input : State) (opcode : Opcode)
  | callRequest (input : State) (request : CallRequest)
  | staticCallRequest (input : State) (request : CallRequest)

def failStack (s : State) : StackError → Outcome
  | .underflow => .exception s .stackUnderflow
  | .overflow => .exception s .stackOverflow

def charge (s : State) (cost : Nat) (k : Nat → Outcome) : Outcome :=
  match Gas.charge s.gas cost with
  | .error _ => .exception s .outOfGas
  | .ok gas => k gas

/-- Amsterdam `instructions/system.py`, `return_` and `revert`, at revision
`fd9298410ec7218838c8348f69c1eb633f1797dc`.
The diagnostic frame retains the expansion and the charged gas. -/
def finish (s : State) (reverting : Bool) : Outcome :=
  match Stack.pop s.stack with
  | .error e => failStack s e
  | .ok (offset, first) =>
    match Stack.pop first with
    | .error e => failStack { s with stack := first } e
    | .ok (length, stack) =>
      let input := { s with stack }
      charge input (Gas.rangeCost s.memory.words offset.toNat length.toNat) fun gas =>
        let memory := Memory.Allocation.expand s.memory offset.toNat length.toNat
        let frame := { input with gas, memory, memoryValid :=
          Memory.Allocation.expand_valid_for_frame _ _ _ s.memoryValid }
        let output : ByteArray := ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩
        if reverting then .revert frame gas output else .returned frame output

/-- Execute RETURN at any code position. -/
def returnOp (s : State) : Outcome := finish s false

/-- Execute REVERT at any code position. -/
def revertOp (s : State) : Outcome := finish s true

/-- Interpret the 32 digest bytes as a big-endian word. -/
def digestWord (digest : Vector UInt8 32) : Word :=
  BitVec.ofNat 256 (EthLib.Base.bytesToNat digest.toArray.toList)

/-- Cancun `instructions/keccak.py`, `keccak`, at revision
`fd9298410ec7218838c8348f69c1eb633f1797dc`.
The gas check precedes the memory read and the hash. -/
def keccak (s : State) : Outcome :=
  match Stack.pop s.stack with
  | .error e => failStack s e
  | .ok (offset, stack) =>
    match Stack.pop stack with
    | .error e => failStack s e
    | .ok (length, stack) =>
      charge s (Gas.keccakCost s.memory.words offset.toNat length.toNat) fun gas =>
        let bytes : ByteArray := ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩
        let digest := EthLib.Cryptography.Hash.Keccak.keccak256 bytes
        match Stack.push stack (digestWord digest) with
        | .error e => failStack s e
        | .ok stack =>
          .continue { s with stack, gas, pc := s.pc + 1, memory := Memory.Allocation.expand s.memory offset.toNat length.toNat, memoryValid := Memory.Allocation.expand_valid_for_frame _ _ _ s.memoryValid }

/-- Total conversion for frame observations.

Values at least `2^256` are an extension beyond the source U256 domain.
-/
def observationWord (n : Nat) : Word := BitVec.ofNat 256 n

/-- Charge before pushing an observation.

Cancun `control_flow.py`, `pc` and `gas_left`, and `memory.py`, `msize`,
charge before calling `stack.py`, `push`.
Cancun `block.py`, `coinbase`, `timestamp`, `number`, `prev_randao`,
`gas_limit`, `chain_id`, and `environment.py`, `base_fee`, do the same.
`gas.py` gives each instruction the cost `BASE`, or two gas.
-/
def observe (s : State) (value : Nat → Nat) : Outcome :=
  charge s 2 fun gas =>
    match Stack.push s.stack (observationWord (value gas)) with
    | .error e => failStack s e
    | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }

/-- Amsterdam `environment.py`, `self_balance`, charges before recording the account read. -/
def selfBalance (s : State) : Outcome :=
  charge s 5 fun gas =>
    let result := TransactionTracker.getAccount s.tracker s.context.environment.currentTarget
    match Stack.push s.stack result.1.balance with
    | .error e => failStack { s with tracker := result.2 } e
    | .ok stack => .continue { s with stack, gas, pc := s.pc + 1, tracker := result.2 }

/-- Amsterdam `utils/address.py`, `to_address_masked`, keeps the low 160 bits. -/
def balanceAddress (word : Word) : World.Address :=
  ⟨word.toNat % (2 ^ 160), Nat.mod_lt _ (by decide)⟩

/-- Amsterdam `environment.py`, `balance`, warms a cold address before charging. -/
def balance (s : State) : Outcome :=
  match Stack.pop s.stack with
  | .error e => failStack s e
  | .ok (word, stack) =>
    let address := balanceAddress word
    let warm := s.warmAddresses.contains address
    let touched := if warm then s.warmAddresses else address :: s.warmAddresses
    let input := { s with stack, warmAddresses := touched }
    charge input (if warm then 100 else 3000) fun gas =>
      let result := TransactionTracker.getAccount s.tracker address
      match Stack.push stack result.1.balance with
      | .error e => failStack { input with tracker := result.2, gas } e
      | .ok stack => .continue { input with stack, gas, pc := s.pc + 1, tracker := result.2 }

/-- Amsterdam `environment.py`, `extcodesize`, at revision
`fd9298410ec7218838c8348f69c1eb633f1797dc`.
Missing code is explicit for a supplied incomplete code store. -/
def extCodeSize (s : State) : Outcome :=
  match Stack.pop s.stack with
  | .error e => failStack s e
  | .ok (word, stack) =>
    let address := balanceAddress word
    let warm := s.warmAddresses.contains address
    let touched := if warm then s.warmAddresses else address :: s.warmAddresses
    let input := { s with stack, warmAddresses := touched }
    charge input (if warm then 200 else 3100) fun gas =>
      let result := TransactionTracker.getAccount s.tracker address
      let read := { input with tracker := result.2, gas }
      match TransactionAccount.getCode result.2 result.1.codeHash with
      | none => .exception read .missingCode
      | some code =>
        match Stack.push stack (BitVec.ofNat 256 code.size) with
        | .error e => failStack read e
        | .ok stack => .continue { read with stack, pc := s.pc + 1 }

/-- Amsterdam `environment.py`, `extcodehash`, at the same revision.
The empty account returns zero, even when explicitly present. -/
def extCodeHash (s : State) : Outcome :=
  match Stack.pop s.stack with
  | .error e => failStack s e
  | .ok (word, stack) =>
    let address := balanceAddress word
    let warm := s.warmAddresses.contains address
    let touched := if warm then s.warmAddresses else address :: s.warmAddresses
    let input := { s with stack, warmAddresses := touched }
    charge input (if warm then 100 else 3000) fun gas =>
      let result := TransactionTracker.getAccount s.tracker address
      let value := if result.1 == World.emptyAccount then 0 else result.1.codeHash
      match Stack.push stack value with
      | .error e => failStack { input with tracker := result.2, gas } e
      | .ok stack => .continue { input with stack, gas, pc := s.pc + 1, tracker := result.2 }

/-- Amsterdam `environment.py`, `extcodecopy`, at revision
`fd9298410ec7218838c8348f69c1eb633f1797dc`.
An incomplete supplied code store produces `missingCode` after memory expansion. -/
def extCodeCopy (s : State) : Outcome :=
  match Stack.pop s.stack with
  | .error e => failStack s e
  | .ok (word, first) =>
    match Stack.pop first with
    | .error e => failStack { s with stack := first } e
    | .ok (destination, second) =>
      match Stack.pop second with
      | .error e => failStack { s with stack := second } e
      | .ok (source, third) =>
        match Stack.pop third with
        | .error e => failStack { s with stack := third } e
        | .ok (length, stack) =>
          let address := balanceAddress word
          let warm := s.warmAddresses.contains address
          let touched := if warm then s.warmAddresses else address :: s.warmAddresses
          let input := { s with stack, warmAddresses := touched }
          let cost := (if warm then 200 else 3100) + 3 * ((length.toNat + 31) / 32) +
            Gas.rangeCost s.memory.words destination.toNat length.toNat
          charge input cost fun gas =>
            let expanded := Memory.Allocation.expand s.memory destination.toNat length.toNat
            let read := TransactionTracker.getAccount s.tracker address
            let charged := { input with gas, tracker := read.2, memory := expanded, memoryValid := Memory.Allocation.expand_valid_for_frame _ _ _ s.memoryValid }
            match TransactionAccount.getCode read.2 read.1.codeHash with
            | none => .exception charged .missingCode
            | some code =>
              let bytes := CallData.readRange code source.toNat length.toNat
              .continue { charged with pc := s.pc + 1, memory := Memory.Allocation.write expanded destination.toNat bytes, memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ charged.memoryValid }

/-- Amsterdam `instructions/storage.py`, `sload`, warms a cold slot before charging. -/
def sload (s : State) : Outcome :=
  match Stack.pop s.stack with
  | .error e => failStack s e
  | .ok (key, stack) =>
    let address := s.context.environment.currentTarget
    let slot := (address, key)
    let warm := s.warmSlots.contains slot
    let touched := if warm then s.warmSlots else slot :: s.warmSlots
    let input := { s with stack, warmSlots := touched }
    charge input (if warm then 100 else 2100) fun gas =>
      let result := TransactionTracker.getStorage s.tracker address key
      match Stack.push stack result.1 with
      | .error e => failStack { input with tracker := result.2, gas } e
      | .ok stack => .continue { input with stack, gas, pc := s.pc + 1, tracker := result.2 }

/-- Amsterdam `storage.py`, `tload`, at revision
`fd9298410ec7218838c8348f69c1eb633f1797dc`.
The key is popped before the fixed gas charge. -/
def tload (s : State) : Outcome :=
  match Stack.pop s.stack with
  | .error e => failStack s e
  | .ok (key, stack) =>
    let input := { s with stack }
    charge input 100 fun gas =>
      let value := TransactionTracker.getTransientStorage s.tracker
        s.context.environment.currentTarget key
      match Stack.push stack value with
      | .error e => failStack { input with gas } e
      | .ok stack => .continue { input with stack, gas, pc := s.pc + 1 }

/-- Amsterdam `storage.py`, `tstore`, at revision
`fd9298410ec7218838c8348f69c1eb633f1797dc`.
Static protection precedes both pops and the fixed gas charge. -/
def tstore (s : State) : Outcome :=
  if s.isStatic then .exception s .writeInStaticContext else
  match Stack.pop s.stack with
  | .error e => failStack s e
  | .ok (key, first) =>
    match Stack.pop first with
    | .error e => failStack { s with stack := first } e
    | .ok (value, stack) =>
      let input := { s with stack }
      charge input 100 fun gas =>
        let tracker := TransactionTracker.setTransientStorage s.tracker
          s.context.environment.currentTarget key value
        .continue { input with gas, tracker, pc := s.pc + 1 }

/-- Encode a topic in the fixed-width source representation. -/
def logTopic (word : Word) : { bytes : ByteArray // bytes.size = 32 } :=
  ⟨word.toBytesBE, by
    change (EthLib.Base.natToBytes 32 word.toNat).toArray.size = 32
    have size (len n : Nat) : (EthLib.Base.natToBytes len n).length = len := by
      induction len generalizing n with
      | zero => rfl
      | succ len ih => simp [EthLib.Base.natToBytes, ih]
    simpa using size 32 word.toNat⟩

/-- Pop topics in source order and retain the stack at an underflow. -/
def popLogTopics : Nat → Stack → Except Stack (List Word × Stack)
  | 0, stack => .ok ([], stack)
  | n + 1, stack =>
    match Stack.pop stack with
    | .error _ => .error stack
    | .ok (topic, rest) =>
      match popLogTopics n rest with
      | .error stack => .error stack
      | .ok (topics, stack) => .ok (topic :: topics, stack)

/-- Amsterdam `instructions/log.py`, `log_n`, and `gas.py`, `GasCosts`,
at revision `fd9298410ec7218838c8348f69c1eb633f1797dc`. -/
def logN (s : State) (count : Fin 5) : Outcome :=
  match Stack.pop s.stack with
  | .error e => failStack s e
  | .ok (offset, first) =>
    match Stack.pop first with
    | .error e => failStack { s with stack := first } e
    | .ok (length, rest) =>
      match popLogTopics count.val rest with
      | .error stack => .exception { s with stack } .stackUnderflow
      | .ok (topics, stack) =>
        let input := { s with stack }
        charge input (375 + 8 * length.toNat + 375 * count.val +
          Gas.rangeCost s.memory.words offset.toNat length.toNat) fun gas =>
          let memory := Memory.Allocation.expand s.memory offset.toNat length.toNat
          let expanded := { input with gas, memory, memoryValid :=
            Memory.Allocation.expand_valid_for_frame _ _ _ s.memoryValid }
          if s.isStatic then .exception expanded .writeInStaticContext else
            let entry : LogEntry := ⟨s.context.environment.currentTarget,
              topics.map logTopic,
              ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩⟩
            .continue { expanded with logs := s.logs ++ [entry], pc := s.pc + 1 }

/-- Form the source meter using the frame's current execution-gas field. -/
def stateMeter (s : State) : Gas.StateMeter.Meter :=
  ⟨s.gas, s.stateGas.reservoir, s.stateGas.baseline, s.stateGas.refundCounter,
    s.stateGas.spilled, s.stateGas.committedSpill⟩

/-- Store all meter fields after a source meter operation. -/
def withStateMeter (s : State) (m : Gas.StateMeter.Meter) : State :=
  { s with gas := m.executionGas, stateGas :=
    ⟨m.stateGas, m.baseline, m.refundCounter, m.spilled, m.committedSpill⟩ }

/-- Amsterdam `storage.py`, `sstore`, at revision
`fd9298410ec7218838c8348f69c1eb633f1797dc`.
The carried exception frame records operations that precede failure. -/
def sstore (s : State) : Outcome :=
  if s.isStatic then .exception s .writeInStaticContext else
  match Stack.pop s.stack with
  | .error e => failStack s e
  | .ok (key, first) =>
    match Stack.pop first with
    | .error e => failStack { s with stack := first } e
    | .ok (value, stack) =>
      let input := { s with stack }
      let address := s.context.environment.currentTarget
      let slot := (address, key)
      let warm := s.warmSlots.contains slot
      let access := if warm then 100 else 2100
      if s.gas < max access 2301 then .exception input .outOfGas else
      let touched := if warm then s.warmSlots else slot :: s.warmSlots
      let original := TransactionState.getStorageOriginal s.tracker address key
      let currentResult := TransactionTracker.getStorage s.tracker address key
      let current := currentResult.1
      let changed := current != value
      let writeCost := if original == current && changed then 10000 else 0
      let clearRefund : Int := if changed && original != 0 && current != 0 && value == 0 then 11616 else 0
      let reverseRefund : Int := if changed && original != 0 && current == 0 then 11616 else 0
      let restoreRefund : Int := if changed && original == value then 10000 else 0
      let base := { input with warmSlots := touched, tracker := currentResult.2 }
      let adjusted := Gas.StateMeter.adjustRefund (stateMeter base) (clearRefund - reverseRefund + restoreRefund)
      let credited := if changed && original == value && original == 0 then
        Gas.StateMeter.creditState adjusted 97920 else adjusted
      let ready := withStateMeter base credited
      let cost := access + writeCost
      if ready.gas < cost then .exception ready .outOfGas else
      let charged := { ready with gas := ready.gas - cost }
      let stateCost := if original == current && changed && original == 0 then 97920 else 0
      match Gas.StateMeter.chargeState (stateMeter charged) stateCost with
      | .error _ => .exception charged .outOfGas
      | .ok meter =>
        let charged := withStateMeter charged meter
        match TransactionTracker.setStorage charged.tracker address key value with
        | .error (_, tracker) => .exception { charged with tracker } .missingStorageAccount
        | .ok tracker => .continue { charged with tracker, pc := s.pc + 1 }

/-- Amsterdam `environment.py`, `blob_base_fee`, charges before computing and pushing. -/
def blobBaseFee (s : State) : Outcome :=
  observe s (fun _ => BlobFee.calculateWith s.context.environment.blobFeeSchedule s.context.environment.excessBlobGas)

/-- Copy an immutable source after checking operands and gas.

Cancun `environment.py`, `calldatacopy` and `codecopy` charge before reading.
-/
def inputCopy (s : State) (data : ByteArray) : Outcome :=
  match Stack.pop s.stack with
  | .error e => failStack s e
  | .ok (destination, stack) =>
    match Stack.pop stack with
    | .error e => failStack s e
    | .ok (source, stack) =>
      match Stack.pop stack with
      | .error e => failStack s e
      | .ok (length, stack) =>
        charge s (Gas.inputCopyCost s.memory.words destination.toNat length.toNat) fun gas =>
          let bytes := CallData.readRange data source.toNat length.toNat
          .continue { s with stack, gas, pc := s.pc + 1, memory := Memory.Allocation.write s.memory destination.toNat bytes, memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid }

/-- Copy checked return data after charging for destination expansion.

Cancun `environment.py`, `returndatacopy`, checks bounds after gas.
-/
def returnDataCopy (s : State) : Outcome :=
  match Stack.pop s.stack with
  | .error e => failStack s e
  | .ok (destination, stack) =>
    match Stack.pop stack with
    | .error e => failStack s e
    | .ok (source, stack) =>
      match Stack.pop stack with
      | .error e => failStack s e
      | .ok (length, stack) =>
        charge s (Gas.inputCopyCost s.memory.words destination.toNat length.toNat) fun gas =>
          match ReturnData.read s.returnData source.toNat length.toNat with
          | .error _ => .exception s .outOfBoundsRead
          | .ok bytes =>
            .continue { s with stack, gas, pc := s.pc + 1, memory := Memory.Allocation.write s.memory destination.toNat bytes, memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid }

/-- Cancun `environment.py`, `blob_hash`: pop, charge, look up, then push. -/
def blobHash (s : State) : Outcome :=
  match Stack.pop s.stack with
  | .error e => failStack s e
  | .ok (index, stack) =>
    charge s 3 fun gas =>
      match Stack.push stack (Environment.blobHash s.context.environment index) with
      | .error e => failStack s e
      | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }

/-- Cancun `block.py`, `block_hash`, pops before charging 20 gas.

The history argument uses the total extension described by `Environment.blockHash`.
-/
def blockHash (s : State) (history : Environment.BlockHistory) : Outcome :=
  match Stack.pop s.stack with
  | .error e => failStack s e
  | .ok (index, stack) =>
    charge s 20 fun gas =>
      match Stack.push stack (Environment.blockHash history s.context.environment.number index) with
      | .error e => failStack s e
      | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }

/-- Osaka `bitwise.py`, `count_leading_zeros`, pops before charging five gas. -/
def clz (s : State) : Outcome :=
  match Stack.pop s.stack with
  | .error e => failStack s e
  | .ok (a, stack) =>
    charge s 5 fun gas =>
      match Stack.push stack (Word.countLeadingZeros a) with
      | .error e => failStack s e
      | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }

/-- Amsterdam `vm/instructions/stack.py`, `dupn`.

Gas is charged before reading and validating the immediate.
The byte reader pads beyond the code with zero.
-/
def dupn (s : State) : Outcome :=
  charge s 3 fun gas =>
    match StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) with
    | none => .exception s .invalidParameter
    | some n =>
      match s.stack.dupAt (n - 1) with
      | .error e => failStack s e
      | .ok stack => .continue { s with stack, gas, pc := s.pc + 2 }

/-- Amsterdam `vm/instructions/stack.py`, `swapn`. -/
def swapn (s : State) : Outcome :=
  charge s 3 fun gas =>
    match StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) with
    | none => .exception s .invalidParameter
    | some n =>
      match s.stack.exchangeAt 0 n with
      | .error e => failStack s e
      | .ok stack => .continue { s with stack, gas, pc := s.pc + 2 }

/-- Amsterdam `vm/instructions/stack.py`, `exchange`. -/
def exchange (s : State) : Outcome :=
  charge s 3 fun gas =>
    match StackImmediate.decodePair (StackImmediate.byte s.code s.pc) with
    | none => .exception s .invalidParameter
    | some (n, m) =>
      match s.stack.exchangeAt n m with
      | .error e => failStack s e
      | .ok stack => .continue { s with stack, gas, pc := s.pc + 2 }

/-- Suspend CALL after its operand pops and static-value check.
Pricing, state access and child execution follow this suspension. -/
def callEntry (s : State) : Outcome :=
  match items : s.stack.val with
  | gas :: address :: value :: inputOffset :: inputSize :: outputOffset :: outputSize :: rest =>
    let stack : Stack := ⟨rest, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
    let input := { s with stack }
    if s.isStatic && value != 0 then .exception input .writeInStaticContext
    else .callRequest input ⟨gas, address, value, inputOffset, inputSize, outputOffset, outputSize⟩
  | _ => failStack { s with stack := Stack.empty } .underflow

/-- Suspend STATICCALL after its six operand pops.

Amsterdam `vm/instructions/system.py`, `staticcall`, has no value operand.
The request therefore carries value zero.
It also has no static-context check of its own, so it suspends in any context.
Pricing, state access and child execution follow this suspension. -/
def staticCallEntry (s : State) : Outcome :=
  match items : s.stack.val with
  | gas :: address :: inputOffset :: inputSize :: outputOffset :: outputSize :: rest =>
    let stack : Stack := ⟨rest, by have bound := s.stack.property; rw [items] at bound; simp at bound; omega⟩
    .staticCallRequest { s with stack } ⟨gas, address, 0, inputOffset, inputSize, outputOffset, outputSize⟩
  | _ => failStack { s with stack := Stack.empty } .underflow

/-- Execute one instruction or stop at the end of code. -/
def step (s : State) : Outcome :=
  if h : s.pc < s.code.size then
    match Opcode.decode s.code[s.pc] with
    | none | some .invalid => .exception s .invalidOpcode
    | some .stop => .stop { s with pc := s.pc + 1 }
    | some (.push n) =>
      charge s (if n.val = 0 then 2 else 3) fun gas =>
        match Stack.push s.stack (PushImmediate.value s.code s.pc n) with
        | .error e => failStack s e
        | .ok stack => .continue { s with stack, gas, pc := PushImmediate.nextPC s.pc n }
    -- Cancun `control_flow.py`, `jump`: pop, charge, then validate the full word.
    | some .dupn => dupn s
    | some .swapn => swapn s
    | some .exchange => exchange s
    | some .jump =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (destination, stack) =>
        charge s 8 fun gas =>
          if JumpDest.contains s.code destination.toNat then
            .continue { s with stack, gas, pc := destination.toNat }
          else .exception s .invalidJumpDestination
    -- Cancun `control_flow.py`, `jumpi`: the destination is popped first.
    | some .jumpi =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (destination, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (condition, stack) =>
          charge s 10 fun gas =>
            if condition.toNat = 0 then
              .continue { s with stack, gas, pc := s.pc + 1 }
            else if JumpDest.contains s.code destination.toNat then
              .continue { s with stack, gas, pc := destination.toNat }
            else .exception s .invalidJumpDestination
    -- Cancun `control_flow.py`, `jumpdest`: charge before advancing.
    | some .jumpdest =>
      charge s 1 fun gas => .continue { s with gas, pc := s.pc + 1 }
    | some .blockhash => blockHash s s.context.environment.blockHashes
    | some .blobhash => blobHash s
    -- Cancun `environment.py`, `calldataload`: pop before charging.
    | some .calldataload =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (offset, stack) =>
        charge s 3 fun gas =>
          match Stack.push stack (CallData.load s.context offset) with
          | .error e => failStack s e
          | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `environment.py`: copy from the selected immutable source.
    | some .calldatacopy => inputCopy s s.context.data
    | some .codecopy => inputCopy s s.code
    | some .returndatacopy => returnDataCopy s
    | some .keccak => keccak s
    -- Cancun `environment.py`, `calldatasize` and `codesize`: charge before push.
    -- Cancun `environment.py`: charge before pushing supplied metadata.
    | some .sload => sload s
    | some .sstore => sstore s
    | some .tload => tload s
    | some .tstore => tstore s
    | some .balance => balance s
    | some .extcodesize => extCodeSize s
    | some .extcodehash => extCodeHash s
    | some .extcodecopy => extCodeCopy s
    | some .return => returnOp s
    | some .revert => revertOp s
    | some (.log count) => logN s count
    | some .selfbalance => selfBalance s
    | some .address => observe s (fun _ => s.context.environment.currentTarget.val)
    | some .origin => observe s (fun _ => s.context.environment.origin.val)
    | some .caller => observe s (fun _ => s.context.environment.caller.val)
    | some .callvalue => observe s (fun _ => s.context.environment.value.toNat)
    | some .gasprice => observe s (fun _ => s.context.environment.gasPrice.toNat)
    | some .coinbase => observe s (fun _ => s.context.environment.coinbase.val)
    | some .timestamp => observe s (fun _ => s.context.environment.timestamp.toNat)
    | some .number => observe s (fun _ => s.context.environment.number.toNat)
    | some .slotnum => observe s (fun _ => s.context.environment.slotNumber.val)
    | some .prevrandao => observe s (fun _ => s.context.environment.prevRandao.toNat)
    | some .gaslimit => observe s (fun _ => s.context.environment.gasLimit.toNat)
    | some .chainid => observe s (fun _ => s.context.environment.chainId.val)
    | some .basefee => observe s (fun _ => s.context.environment.baseFee.toNat)
    | some .blobbasefee => blobBaseFee s
    | some .calldatasize => observe s (fun _ => s.context.data.size)
    | some .codesize => observe s (fun _ => s.code.size)
    | some .returndatasize => observe s (fun _ => s.returnData.size)
    | some .pc => observe s (fun _ => s.pc)
    | some .msize => observe s (fun _ => Memory.Allocation.byteSize s.memory)
    | some .gas => observe s id
    -- Cancun `memory.py`, `mcopy`: pop all operands and charge before copying.
    | some .mcopy =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (destination, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (source, stack) =>
          match Stack.pop stack with
          | .error e => failStack s e
          | .ok (length, stack) =>
            charge s (Gas.mcopyCost s.memory.words destination.toNat source.toNat length.toNat) fun gas =>
              .continue { s with stack, gas, pc := s.pc + 1, memory := Memory.Allocation.copy s.memory destination.toNat source.toNat length.toNat, memoryValid := Memory.Allocation.copy_valid_for_frame _ _ _ _ s.memoryValid }
    -- Cancun `memory.py`, `mload`: pop, charge, expand, then read.
    | some .mload =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (offset, stack) =>
        charge s (3 + Gas.rangeCost s.memory.words offset.toNat 32) fun gas =>
          let result := Memory.Allocation.loadWord s.memory offset.toNat
          match Stack.push stack result.1 with
          | .error e => failStack s e
          | .ok stack => .continue { s with stack, gas, pc := s.pc + 1, memory := result.2, memoryValid := Memory.Allocation.expand_valid_for_frame _ _ _ s.memoryValid }
    -- Cancun `memory.py`, `mstore`: the offset is popped before the value.
    | some .mstore =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (offset, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (value, stack) =>
          charge s (3 + Gas.rangeCost s.memory.words offset.toNat 32) fun gas =>
            .continue { s with stack, gas, pc := s.pc + 1, memory := Memory.Allocation.storeWord s.memory offset.toNat value, memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid }
    -- Cancun `memory.py`, `mstore8`: only the low byte is written.
    | some .mstore8 =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (offset, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (value, stack) =>
          charge s (3 + Gas.rangeCost s.memory.words offset.toNat 1) fun gas =>
            .continue { s with stack, gas, pc := s.pc + 1, memory := Memory.Allocation.storeByte s.memory offset.toNat value, memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ s.memoryValid }
    | some .pop =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (_, stack) =>
        charge s 2 fun gas => .continue { s with stack, gas, pc := s.pc + 1 }
    | some .add =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.add a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `arithmetic.py`, `addmod`: pop three operands before charging.
    | some .addmod =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          match Stack.pop stack with
          | .error e => failStack s e
          | .ok (m, stack) =>
            charge s 8 fun gas =>
              match Stack.push stack (Word.addmod a b m) with
              | .error e => failStack s e
              | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `arithmetic.py`, `mulmod`: pop three operands before charging.
    | some .mulmod =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          match Stack.pop stack with
          | .error e => failStack s e
          | .ok (m, stack) =>
            charge s 8 fun gas =>
              match Stack.push stack (Word.mulmod a b m) with
              | .error e => failStack s e
              | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `arithmetic.py`, `exp`: base is popped before exponent.
    | some .exp =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (base, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (exponent, stack) =>
          charge s (Gas.expCost exponent) fun gas =>
            match Stack.push stack (Word.exp base exponent) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `arithmetic.py`, `mul`: pop twice before charging `OPCODE_MUL`.
    | some .mul =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 5 fun gas =>
            match Stack.push stack (Word.mul a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `arithmetic.py`, `sub`: the first pop is the left operand.
    | some .sub =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.sub a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `arithmetic.py`, `div`: the first pop is the left operand.
    | some .div =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 5 fun gas =>
            match Stack.push stack (Word.div a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `arithmetic.py`, `mod`: the first pop is the left operand.
    | some .mod =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 5 fun gas =>
            match Stack.push stack (Word.mod a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `arithmetic.py`, `sdiv`: the first pop is the left operand.
    | some .sdiv =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 5 fun gas =>
            match Stack.push stack (Word.sdiv a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `arithmetic.py`, `smod`: the first pop is the left operand.
    | some .smod =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 5 fun gas =>
            match Stack.push stack (Word.smod a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `comparison.py`, `less_than`: pop both operands before charging gas.
    | some .lt =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.ltResult a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `comparison.py`, `greater_than`: pop both operands before charging gas.
    | some .gt =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.gtResult a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `comparison.py`, `signed_less_than`: pop both operands before charging gas.
    | some .slt =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.sltResult a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `comparison.py`, `signed_greater_than`: pop both operands before charging gas.
    | some .sgt =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.sgtResult a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `comparison.py`, `equal`: pop both operands before charging gas.
    | some .eq =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.eqResult a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `bitwise.py`, `bitwise_and`: pop both operands before charging gas.
    | some .and =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.bitwiseAnd a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `bitwise.py`, `bitwise_or`: pop both operands before charging gas.
    | some .or =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.bitwiseOr a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `bitwise.py`, `bitwise_xor`: pop both operands before charging gas.
    | some .xor =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.bitwiseXor a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `bitwise.py`, `bitwise_shl`: pop the index or count first.
    | some .shl =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.shl a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `bitwise.py`, `bitwise_shr`: pop the index or count first.
    | some .shr =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.shr a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `bitwise.py`, `bitwise_sar`: pop the index or count first.
    | some .sar =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.sar a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `bitwise.py`, `get_byte`: pop the index or count first.
    | some .byte =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 3 fun gas =>
            match Stack.push stack (Word.byte a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `arithmetic.py`, `signextend`: pop the index or count first.
    | some .signextend =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        match Stack.pop stack with
        | .error e => failStack s e
        | .ok (b, stack) =>
          charge s 5 fun gas =>
            match Stack.push stack (Word.signextend a b) with
            | .error e => failStack s e
            | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    -- Cancun `comparison.py`, `is_zero`: pop the operand before charging gas.
    | some .iszero =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        charge s 3 fun gas =>
          match Stack.push stack (Word.iszeroResult a) with
          | .error e => failStack s e
          | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    | some .call => callEntry s
    | some .staticcall => staticCallEntry s
    | some .clz => clz s
    -- Cancun `bitwise.py`, `bitwise_not`: pop the operand before charging gas.
    | some .not =>
      match Stack.pop s.stack with
      | .error e => failStack s e
      | .ok (a, stack) =>
        charge s 3 fun gas =>
          match Stack.push stack (Word.bitwiseNot a) with
          | .error e => failStack s e
          | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    | some (.dup i) =>
      charge s 3 fun gas =>
        match Stack.dup s.stack i with
        | .error e => failStack s e
        | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    | some (.swap i) =>
      charge s 3 fun gas =>
        match Stack.swap s.stack i with
        | .error e => failStack s e
        | .ok stack => .continue { s with stack, gas, pc := s.pc + 1 }
    | some op => .unsupported s op
  else .stop s

/-- The frame carried by an outcome, including diagnostic input for failures. -/
def Outcome.frame : Outcome → State
  | .continue s | .stop s | .returned s _ | .revert s _ _ | .exception s _ | .unsupported s _ | .callRequest s _
  | .staticCallRequest s _ => s

/-- Message-boundary observations modeled by this subset. -/
inductive Boundary where
  | stopped (gas : Nat)
  | returned (gas : Nat) (output : ByteArray)
  | reverted (gas : Nat) (output : ByteArray)
  | exceptional (gas : Nat) (reason : Exception)

/-- Project the modeled observations for terminal EVM outcomes.

Cancun `vm/interpreter.py`, `process_message`, burns all remaining gas on
`ExceptionalHalt` and clears output.
RETURN and REVERT retain their gas and output.
World rollback is outside this subset.
-/
def settle : Outcome → Option Boundary
  | .stop s => some (.stopped s.gas)
  | .returned s output => some (.returned s.gas output)
  | .revert _ gas output => some (.reverted gas output)
  | .exception _ reason => some (.exceptional 0 reason)
  | .continue _ | .unsupported _ _ | .callRequest _ _ | .staticCallRequest _ _ => none

end EthLib.EVM.Frame
