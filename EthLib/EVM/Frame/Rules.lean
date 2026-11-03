module

public import EthLib.EVM.Frame

/-!
# Frame transition rules

These rules state stack and gas conditions without invoking the executable step.
The sources are Cancun execution-specs revision
`fd9298410ec7218838c8348f69c1eb633f1797dc`, `vm/interpreter.py`,
`vm/instructions/stack.py`, `arithmetic.py`, `comparison.py`, `bitwise.py`,
`control_flow.py`, `memory.py`, `block.py`, and `environment.py`.
CLZ follows Osaka `vm/instructions/bitwise.py`, `count_leading_zeros`, at the same revision.
Amsterdam `vm/instructions/block.py`, `slot_number`, defines SLOTNUM at the same revision.
Amsterdam `vm/instructions/stack.py` defines DUPN, SWAPN and EXCHANGE.
The blob fee rule uses the supplied schedule, which can differ from Cancun.
-/

@[expose] public section
namespace EthLib.EVM.Frame

/-- The instruction at an in-bounds program counter. -/
def At (s : State) (op : Option Opcode) : Prop :=
  ∃ h : s.pc < s.code.size, Opcode.decode s.code[s.pc] = op

/-- Assigned opcodes for which this subset has no execution rule. -/
def Unsupported : Opcode → Prop
  | .call | .return | .revert | .log _ | .extcodecopy | .extcodesize | .extcodehash | .tload | .tstore | .sstore | .sload | .balance | .selfbalance | .dupn | .swapn | .exchange | .blockhash | .blobhash | .blobbasefee | .coinbase | .timestamp | .number | .slotnum | .prevrandao | .gaslimit | .chainid | .basefee | .address | .origin | .caller | .callvalue | .gasprice | .keccak | .returndatacopy | .returndatasize | .calldatacopy | .codecopy | .calldataload | .calldatasize | .codesize | .mcopy | .mload | .mstore | .mstore8 | .pc | .msize | .gas | .jump | .jumpi | .jumpdest | .addmod | .mulmod | .exp | .shl | .shr | .sar | .byte | .signextend | .lt | .gt | .slt | .sgt | .eq | .iszero | .clz | .and | .or | .xor | .not | .stop | .invalid | .add | .mul | .sub | .div | .mod | .sdiv | .smod | .pop | .push _ | .dup _ | .swap _ => False
  | _ => True

/-- Exact fields of a continuing frame, including fields untouched by this slice. -/
def Advances (s t : State) (pc gas : Nat) (xs : List Word) : Prop :=
  t.code = s.code ∧ t.memory = s.memory ∧ t.pc = pc ∧ t.gas = gas ∧ t.stack.val = xs ∧ t.context = s.context ∧ t.returnData = s.returnData ∧ t.tracker = s.tracker ∧ t.warmAddresses = s.warmAddresses ∧ t.warmSlots = s.warmSlots ∧ t.isStatic = s.isStatic ∧ t.stateGas = s.stateGas ∧ t.logs = s.logs

/-- Exact fields after a memory instruction. -/
def AdvancesMemory (s t : State) (memory : Memory.Allocation.State)
    (pc gas : Nat) (xs : List Word) : Prop :=
  t.code = s.code ∧ t.memory = memory ∧ t.pc = pc ∧ t.gas = gas ∧ t.stack.val = xs ∧ t.context = s.context ∧ t.returnData = s.returnData ∧ t.tracker = s.tracker ∧ t.warmAddresses = s.warmAddresses ∧ t.warmSlots = s.warmSlots ∧ t.isStatic = s.isStatic ∧ t.stateGas = s.stateGas ∧ t.logs = s.logs

/-- A successful MCOPY with observed pops determines the resulting frame. -/
theorem mcopy_actual_fields (s t : State) (destination source length : Word)
    (first second rest : Stack) (at_ : At s (some .mcopy))
    (p1 : s.stack.pop = .ok (destination, first))
    (p2 : first.pop = .ok (source, second))
    (p3 : second.pop = .ok (length, rest)) (run : step s = .continue t) :
    Gas.mcopyCost s.memory.words destination.toNat source.toNat length.toNat ≤ s.gas ∧
    AdvancesMemory s t (Memory.Allocation.copy s.memory destination.toNat source.toNat length.toNat)
      (s.pc + 1) (s.gas - Gas.mcopyCost s.memory.words destination.toNat source.toNat length.toNat)
      rest.val := by
  obtain ⟨bounds, decoded⟩ := at_
  by_cases gas : Gas.mcopyCost s.memory.words destination.toNat source.toNat length.toNat ≤ s.gas
  · simp only [step, dite_eq_left bounds, decoded, p1, p2, p3, charge, Gas.charge,
      ite_eq_left gas] at run
    cases run
    exact ⟨gas, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp [step, bounds, decoded, p1, p2, p3, charge, Gas.charge, gas] at run

/-- Cancun `runtime.py`: the source byte length at an instruction boundary. -/
def jumpSourceLength (b : UInt8) : Nat :=
  if 0x60 ≤ b.toNat ∧ b.toNat ≤ 0x7f then 1 + (b.toNat - 0x5f) else 1

/-- Instruction boundaries reached by the source byte-length rule. -/
inductive JumpBoundaryFrom (code : ByteArray) : Nat → Nat → Prop where
  | here (pc : Nat) (inside : pc < code.size) : JumpBoundaryFrom code pc pc
  | step (pc x : Nat) (inside : pc < code.size)
      (later : JumpBoundaryFrom code (pc + jumpSourceLength (PushImmediate.byteAt code pc)) x) :
      JumpBoundaryFrom code pc x

/-- A valid target is a JUMPDEST byte at a source instruction boundary. -/
def ValidJumpDest (code : ByteArray) (pc : Nat) : Prop :=
  JumpBoundaryFrom code 0 pc ∧ PushImmediate.byteAt code pc = 0x5b

/-- The natural observation selected by an introspection opcode. -/
inductive Observation where
  | pc | msize | gas | calldatasize | codesize | returndatasize
  | address | origin | caller | callvalue | gasprice
  | coinbase | timestamp | number | slotnum | prevrandao | gaslimit | chainid | basefee | blobbasefee
  deriving DecidableEq

/-- Opcode corresponding to an observation. -/
def Observation.opcode : Observation → Opcode
  | .address => .address | .origin => .origin | .caller => .caller
  | .callvalue => .callvalue | .gasprice => .gasprice
  | .coinbase => .coinbase
  | .timestamp => .timestamp
  | .slotnum => .slotnum
  | .number => .number
  | .prevrandao => .prevrandao
  | .gaslimit => .gaslimit
  | .chainid => .chainid
  | .basefee => .basefee
  | .blobbasefee => .blobbasefee
  | .pc => .pc | .msize => .msize | .gas => .gas
  | .calldatasize => .calldatasize | .codesize => .codesize | .returndatasize => .returndatasize

/-- Value observed after the instruction has paid its gas cost. -/
def Observation.value (o : Observation) (s : State) : Nat :=
  match o with
  | .address => s.context.environment.currentTarget.val
  | .origin => s.context.environment.origin.val
  | .caller => s.context.environment.caller.val
  | .callvalue => s.context.environment.value.toNat
  | .gasprice => s.context.environment.gasPrice.toNat
  | .coinbase => s.context.environment.coinbase.val
  | .timestamp => s.context.environment.timestamp.toNat
  | .slotnum => s.context.environment.slotNumber.val
  | .number => s.context.environment.number.toNat
  | .prevrandao => s.context.environment.prevRandao.toNat
  | .gaslimit => s.context.environment.gasLimit.toNat
  | .chainid => s.context.environment.chainId.val
  | .basefee => s.context.environment.baseFee.toNat
  | .blobbasefee => BlobFee.calculateWith s.context.environment.blobFeeSchedule s.context.environment.excessBlobGas
  | .pc => s.pc
  | .msize => Memory.Allocation.byteSize s.memory
  | .gas => s.gas - 2
  | .calldatasize => s.context.data.size
  | .codesize => s.code.size
  | .returndatasize => s.returnData.size

/-- Immutable source selected by an input copy instruction. -/
inductive InputSource where
  | calldata | code
  deriving DecidableEq

/-- The instruction associated with a source. -/
def InputSource.opcode : InputSource → Opcode
  | .calldata => .calldatacopy
  | .code => .codecopy

/-- The bytes selected from the current frame. -/
def InputSource.bytes (source : InputSource) (s : State) : ByteArray :=
  match source with
  | .calldata => s.context.data
  | .code => s.code

/-- The mathematical result for a block number and an oldest-first history.

A missing in-window entry is the total extension of the source indexing rule.
-/
def BlockHashValue (history : List Word) (current index : Word) (value : Word) : Prop :=
  (index.toNat < current.toNat ∧ current.toNat ≤ index.toNat + 256 ∧
    current.toNat - index.toNat ≤ history.length ∧
    ∃ h : history.length - (current.toNat - index.toNat) < history.length,
      value = history[history.length - (current.toNat - index.toNat)]'h) ∨
  ((current.toNat ≤ index.toNat ∨ index.toNat + 256 < current.toNat ∨
    history.length < current.toNat - index.toNat) ∧ value = 0)

/-- Account selected by the overlay before the transaction-start parent. -/
def SelfBalanceAccount (s : State) : World.Account :=
  let a := s.context.environment.currentTarget
  (match s.tracker.writes.accountWrites.lookup a with
   | some value => value
   | none => s.tracker.parent.accounts.lookup a).getD World.emptyAccount

/-- The source account read records the target without changing other fields. -/
def SelfBalanceRead (s : State) : TransactionState.State :=
  { s.tracker with accountReads := s.context.environment.currentTarget :: s.tracker.accountReads }

/-- A BALANCE operand denotes its low 160 bits. -/
def BalanceAddress (word : Word) : World.Address :=
  ⟨word.toNat % (2 ^ 160), Nat.mod_lt _ (by decide)⟩

/-- Warm membership is separate from transaction tracker reads. -/
def BalanceWarm (s : State) (a : World.Address) : List World.Address :=
  if a ∈ s.warmAddresses then s.warmAddresses else a :: s.warmAddresses

/-- Amsterdam account-access gas depends on prior warm membership. -/
def BalanceCost (s : State) (a : World.Address) : Nat :=
  if a ∈ s.warmAddresses then 100 else 3000

/-- The overlay shadows the immutable parent, including tombstones. -/
def BalanceAccount (s : State) (a : World.Address) : World.Account :=
  (match s.tracker.writes.accountWrites.lookup a with
   | some value => value
   | none => s.tracker.parent.accounts.lookup a).getD World.emptyAccount

/-- Record the account read after a successful gas charge. -/
def BalanceRead (s : State) (a : World.Address) : TransactionState.State :=
  { s.tracker with accountReads := a :: s.tracker.accountReads }

/-- EXTCODESIZE adds Amsterdam's separate code-reading charge. -/
def ExtCodeSizeCost (s : State) (a : World.Address) : Nat := BalanceCost s a + 100

/-- EXTCODECOPY charges access, code reading, word copying and memory expansion. -/
def ExtCodeCopyCost (s : State) (a : World.Address) (destination length : Word) : Nat :=
  ExtCodeSizeCost s a + 3 * ((length.toNat + 31) / 32) +
    Gas.rangeCost s.memory.words destination.toNat length.toNat

/-- Code lookup follows the empty sentinel, transaction overlay and parent store. -/
def ExtCodeBytes (s : State) (a : World.Address) : Option ByteArray :=
  let hash := (BalanceAccount s a).codeHash
  if hash = World.emptyCodeHash then some ByteArray.empty else
  match s.tracker.writes.codeWrites.lookup hash with
  | some code => some code
  | none => s.tracker.parent.codes.lookup hash

/-- EXTCODEHASH returns zero for the source's empty account. -/
def ExtCodeHashValue (s : State) (a : World.Address) : Word :=
  let account := BalanceAccount s a
  if account = World.emptyAccount then 0 else account.codeHash

/-- Slot warming is independent of tracker reads and account warmth. -/
def SloadWarm (s : State) (key : Word) : List (World.Address × Word) :=
  let slot := (s.context.environment.currentTarget, key)
  if slot ∈ s.warmSlots then s.warmSlots else slot :: s.warmSlots

/-- Amsterdam storage-access gas uses the initial slot warm set. -/
def SloadCost (s : State) (key : Word) : Nat :=
  if (s.context.environment.currentTarget, key) ∈ s.warmSlots then 100 else 2100

/-- Effective storage gives writes priority over clears and the parent. -/
def SloadValue (s : State) (key : Word) : Word :=
  let address := s.context.environment.currentTarget
  match s.tracker.writes.storageWrites.lookup (address, key) with
  | some value => value
  | none => if address ∈ s.tracker.writes.storageClears then 0 else World.getStorage s.tracker.parent address key

/-- A successful storage read records the full target and key. -/
def SloadRead (s : State) (key : Word) : TransactionState.State :=
  { s.tracker with storageReads := (s.context.environment.currentTarget, key) :: s.tracker.storageReads }

/-- Amsterdam `storage.py`, `sstore`: independent conditions for state-dependent pricing.

The four refund terms are stated as implications so that each source condition
can be checked independently for arbitrary original, current, and new values. -/
def SstorePricing (original current value : Word) (writeCost stateCost : Nat)
    (clearRefund reverseRefund restoreRefund : Int) (credit : Bool) : Prop :=
  (original = current ∧ current ≠ value → writeCost = 10000) ∧
  (¬ (original = current ∧ current ≠ value) → writeCost = 0) ∧
  (original = current ∧ current ≠ value ∧ original = 0 → stateCost = 97920) ∧
  (¬ (original = current ∧ current ≠ value ∧ original = 0) → stateCost = 0) ∧
  (current ≠ value ∧ original ≠ 0 ∧ current ≠ 0 ∧ value = 0 → clearRefund = 11616) ∧
  (¬ (current ≠ value ∧ original ≠ 0 ∧ current ≠ 0 ∧ value = 0) → clearRefund = 0) ∧
  (current ≠ value ∧ original ≠ 0 ∧ current = 0 → reverseRefund = 11616) ∧
  (¬ (current ≠ value ∧ original ≠ 0 ∧ current = 0) → reverseRefund = 0) ∧
  (current ≠ value ∧ original = value → restoreRefund = 10000) ∧
  (¬ (current ≠ value ∧ original = value) → restoreRefund = 0) ∧
  (credit = true ↔ current ≠ value ∧ original = value ∧ original = 0)

/-- The successful post-sentry read leaves all unrelated fields unchanged. -/
def SstoreReadFields (s t : State) (rest : Stack) (key : Word) : Prop :=
  t.code = s.code ∧ t.pc = s.pc ∧ t.stack = rest ∧ t.gas = s.gas ∧
  t.memory = s.memory ∧ t.context = s.context ∧ t.returnData = s.returnData ∧
  t.warmAddresses = s.warmAddresses ∧ t.warmSlots = SloadWarm s key ∧
  t.isStatic = s.isStatic ∧ t.stateGas = s.stateGas ∧
  t.tracker.parent = s.tracker.parent ∧ t.tracker.writes = s.tracker.writes ∧
  t.tracker.accountReads = s.tracker.accountReads ∧
  t.tracker.storageReads = (s.context.environment.currentTarget, key) :: s.tracker.storageReads ∧
  t.tracker.createdAccounts = s.tracker.createdAccounts ∧
  t.tracker.snapshots = s.tracker.snapshots ∧ t.logs = s.logs

/-- Fields unaffected by state-gas accounting. -/
def SstoreMeterRetained (s t : State) : Prop :=
  t.code = s.code ∧ t.pc = s.pc ∧ t.stack = s.stack ∧ t.memory = s.memory ∧
  t.context = s.context ∧ t.returnData = s.returnData ∧ t.tracker = s.tracker ∧
  t.warmAddresses = s.warmAddresses ∧ t.warmSlots = s.warmSlots ∧ t.isStatic = s.isStatic ∧
  t.stateGas.baseline = s.stateGas.baseline ∧ t.stateGas.committedSpill = s.stateGas.committedSpill ∧ t.logs = s.logs

/-- The independent refund adjustment and optional state-gas credit. -/
def SstoreCreditFields (s t : State) (delta : Int) (credit : Bool) : Prop :=
  SstoreMeterRetained s t ∧ t.stateGas.refundCounter = s.stateGas.refundCounter + delta ∧
  ((credit = false ∧ t.gas = s.gas ∧ t.stateGas.reservoir = s.stateGas.reservoir ∧
      t.stateGas.spilled = s.stateGas.spilled) ∨
    (credit = true ∧
      ((97920 ≤ s.stateGas.spilled ∧ t.gas = s.gas + 97920 ∧
          t.stateGas.spilled + 97920 = s.stateGas.spilled ∧ t.stateGas.reservoir = s.stateGas.reservoir) ∨
       (s.stateGas.spilled < 97920 ∧ t.gas = s.gas + s.stateGas.spilled ∧
          t.stateGas.spilled = 0 ∧ t.stateGas.reservoir = s.stateGas.reservoir + (97920 - s.stateGas.spilled)))))

/-- State-gas charging draws from the reservoir before execution gas. -/
def SstoreChargeFields (s t : State) (amount : Nat) : Prop :=
  SstoreMeterRetained s t ∧ t.stateGas.refundCounter = s.stateGas.refundCounter ∧
  ((amount ≤ s.stateGas.reservoir ∧ t.stateGas.reservoir + amount = s.stateGas.reservoir ∧
      t.gas = s.gas ∧ t.stateGas.spilled = s.stateGas.spilled) ∨
    (s.stateGas.reservoir < amount ∧ amount ≤ s.stateGas.reservoir + s.gas ∧
      t.stateGas.reservoir = 0 ∧ t.gas + (amount - s.stateGas.reservoir) = s.gas ∧
      t.stateGas.spilled = s.stateGas.spilled + (amount - s.stateGas.reservoir)))

/-- Original storage observes the immutable parent unless the account was created. -/
def SstoreOriginal (s : State) (key : Word) : Word :=
  if s.context.environment.currentTarget ∈ s.tracker.createdAccounts then 0
  else World.getStorage s.tracker.parent s.context.environment.currentTarget key

/-- State-dependent pricing and its refund/credit effects after the sentry. -/
def SstoreReady (s ready : State) (rest : Stack) (key value : Word)
    (executionCost stateCost : Nat) : Prop :=
  ∃ read : State, ∃ writeCost : Nat, ∃ clear reverse restore : Int, ∃ credit : Bool,
    SstoreReadFields s read rest key ∧
    SstorePricing (SstoreOriginal s key) (SloadValue s key) value
      writeCost stateCost clear reverse restore credit ∧
    SstoreCreditFields read ready (clear - reverse + restore) credit ∧
    executionCost = SloadCost s key + writeCost

/-- The execution-gas charge changes only execution gas. -/
def SstoreExecutionFields (s t : State) (cost : Nat) : Prop :=
  SstoreMeterRetained s t ∧ t.stateGas = s.stateGas ∧ t.gas + cost = s.gas

/-- Account lookup observes overlay tombstones before the immutable parent. -/
def SstoreAccount (s : State) : Option World.Account :=
  let address := s.context.environment.currentTarget
  match s.tracker.writes.accountWrites.lookup address with
  | some account => account
  | none => World.getAccountOptional s.tracker.parent address

/-- A storage-write attempt records the account read and keeps other fields. -/
def SstoreWriteFields (s t : State) (key value : Word) (success : Bool) : Prop :=
  t.code = s.code ∧ t.pc = (if success then s.pc + 1 else s.pc) ∧
  t.stack = s.stack ∧ t.gas = s.gas ∧ t.memory = s.memory ∧ t.context = s.context ∧
  t.returnData = s.returnData ∧ t.warmAddresses = s.warmAddresses ∧
  t.warmSlots = s.warmSlots ∧ t.isStatic = s.isStatic ∧ t.stateGas = s.stateGas ∧
  t.tracker.parent = s.tracker.parent ∧
  t.tracker.writes.accountWrites = s.tracker.writes.accountWrites ∧
  t.tracker.writes.storageWrites =
    (if success then ((s.context.environment.currentTarget, key), value) :: s.tracker.writes.storageWrites
     else s.tracker.writes.storageWrites) ∧
  t.tracker.writes.codeWrites = s.tracker.writes.codeWrites ∧
  t.tracker.writes.storageClears = s.tracker.writes.storageClears ∧
  t.tracker.writes.transientStorage = s.tracker.writes.transientStorage ∧
  t.tracker.accountReads = s.context.environment.currentTarget :: s.tracker.accountReads ∧
  t.tracker.storageReads = s.tracker.storageReads ∧
  t.tracker.createdAccounts = s.tracker.createdAccounts ∧ t.tracker.snapshots = s.tracker.snapshots ∧ t.logs = s.logs

/-- Independent source cases for the SSTORE helper at any code and program counter. -/
inductive SstoreLocal : State → Outcome → Prop where
  | sstoreStatic (s) : s.isStatic = true →
      SstoreLocal s (.exception s .writeInStaticContext)
  | sstoreUnderflow (s) : s.isStatic = false → s.stack.val = [] →
      SstoreLocal s (.exception s .stackUnderflow)
  | sstoreSecondUnderflow (s : State) (rest : Stack) (key : Word) :
      s.isStatic = false → s.stack.val = key :: rest.val → rest.val = [] →
      SstoreLocal s (.exception { s with stack := rest } .stackUnderflow)
  | sstoreSentry (s : State) (first rest : Stack) (key value : Word) :
      s.isStatic = false → s.stack.val = key :: first.val →
      first.val = value :: rest.val → s.gas < 2301 →
      SstoreLocal s (.exception { s with stack := rest } .outOfGas)
  | sstoreExecutionGas (s ready : State) (first rest : Stack) (key value : Word) (cost stateCost : Nat) :
      s.isStatic = false → s.stack.val = key :: first.val →
      first.val = value :: rest.val → 2301 ≤ s.gas →
      SstoreReady s ready rest key value cost stateCost → ready.gas < cost →
      SstoreLocal s (.exception ready .outOfGas)
  | sstoreStateGas (s ready charged : State) (first rest : Stack) (key value : Word) (cost stateCost : Nat) :
      s.isStatic = false → s.stack.val = key :: first.val →
      first.val = value :: rest.val → 2301 ≤ s.gas →
      SstoreReady s ready rest key value cost stateCost → cost ≤ ready.gas →
      SstoreExecutionFields ready charged cost → charged.stateGas.reservoir + charged.gas < stateCost →
      SstoreLocal s (.exception charged .outOfGas)
  | sstoreMissing (s ready charged paid result : State) (first rest : Stack) (key value : Word) (cost stateCost : Nat) :
      s.isStatic = false → s.stack.val = key :: first.val →
      first.val = value :: rest.val → 2301 ≤ s.gas →
      SstoreReady s ready rest key value cost stateCost → cost ≤ ready.gas →
      SstoreExecutionFields ready charged cost → SstoreChargeFields charged paid stateCost →
      SstoreAccount paid = none → SstoreWriteFields paid result key value false →
      SstoreLocal s (.exception result .missingStorageAccount)
  | sstoreSuccess (s ready charged paid result : State) (first rest : Stack) (key value : Word) (cost stateCost : Nat) :
      s.isStatic = false → s.stack.val = key :: first.val →
      first.val = value :: rest.val → 2301 ≤ s.gas →
      SstoreReady s ready rest key value cost stateCost → cost ≤ ready.gas →
      SstoreExecutionFields ready charged cost → SstoreChargeFields charged paid stateCost →
      SstoreAccount paid ≠ none → SstoreWriteFields paid result key value true →
      SstoreLocal s (.continue result)

/-- Source-oriented rules for one frame transition. -/
def TransientValueRule (s : State) (key : Word) : Word :=
  (s.tracker.writes.transientStorage.lookup (s.context.environment.currentTarget, key)).getD 0

/-- Exact transient-write representation and all retained tracker fields. -/
def TransientWriteFields (s t : TransactionState.State) (a : World.Address) (key value : Word) : Prop :=
  t.parent = s.parent ∧ t.accountReads = s.accountReads ∧ t.storageReads = s.storageReads ∧
  t.createdAccounts = s.createdAccounts ∧ t.snapshots = s.snapshots ∧
  t.writes.accountWrites = s.writes.accountWrites ∧ t.writes.storageWrites = s.writes.storageWrites ∧
  t.writes.codeWrites = s.writes.codeWrites ∧ t.writes.storageClears = s.writes.storageClears ∧
  t.writes.transientStorage =
    (if value = 0 then [] else [((a, key), value)]) ++
      s.writes.transientStorage.filter (fun entry => entry.1 != (a, key))

/-- The two frame-local terminal memory instructions. -/
inductive FinishKind where
  | return_ | revert_
  deriving DecidableEq

/-- Opcode corresponding to a terminal memory instruction. -/
def FinishKind.opcode : FinishKind → Opcode
  | .return_ => .return
  | .revert_ => .revert

/-- Result corresponding to a terminal memory instruction. -/
def FinishKind.outcome : FinishKind → State → ByteArray → Outcome
  | .return_, frame, output => .returned frame output
  | .revert_, frame, output => .revert frame frame.gas output

inductive Rule : State → Outcome → Prop where
  | endCode (s) : s.code.size ≤ s.pc → Rule s (.stop s)
  | stop (s) : At s (some .stop) → Rule s (.stop { s with pc := s.pc + 1 })
  | invalid (s) : At s none ∨ At s (some .invalid) → Rule s (.exception s .invalidOpcode)
  | unsupported (s op) : At s (some op) → Unsupported op → Rule s (.unsupported s op)
  | callUnderflow (s) : At s (some .call) → s.stack.val.length < 7 →
      Rule s (.exception { s with stack := Stack.empty } .stackUnderflow)
  | callStatic (s stack gas address value inputOffset inputSize outputOffset outputSize) :
      At s (some .call) →
      s.stack.val = gas :: address :: value :: inputOffset :: inputSize :: outputOffset :: outputSize :: stack.val →
      s.isStatic = true → value ≠ 0 →
      Rule s (.exception { s with stack } .writeInStaticContext)
  | callSuspend (s stack gas address value inputOffset inputSize outputOffset outputSize) :
      At s (some .call) →
      s.stack.val = gas :: address :: value :: inputOffset :: inputSize :: outputOffset :: outputSize :: stack.val →
      (s.isStatic = false ∨ value = 0) →
      Rule s (.callRequest { s with stack } ⟨gas, address, value, inputOffset, inputSize, outputOffset, outputSize⟩)

  | tloadUnderflow (s) : At s (some .tload) → s.stack.val = [] →
      Rule s (.exception s .stackUnderflow)
  | tloadGas (s : State) (rest : Stack) (key : Word) :
      At s (some .tload) → s.stack.val = key :: rest.val → s.gas < 100 →
      Rule s (.exception { s with stack := rest } .outOfGas)
  | tload (s t : State) (rest : Stack) (key : Word) :
      At s (some .tload) → s.stack.val = key :: rest.val → 100 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 100) (TransientValueRule s key :: rest.val) →
      Rule s (.continue t)
  | tstoreStatic (s) : At s (some .tstore) → s.isStatic = true →
      Rule s (.exception s .writeInStaticContext)
  | tstoreUnderflow (s) : At s (some .tstore) → s.isStatic = false → s.stack.val = [] →
      Rule s (.exception s .stackUnderflow)
  | tstoreSecondUnderflow (s : State) (rest : Stack) (key : Word) :
      At s (some .tstore) → s.isStatic = false → s.stack.val = key :: rest.val → rest.val = [] →
      Rule s (.exception { s with stack := rest } .stackUnderflow)
  | tstoreGas (s : State) (first rest : Stack) (key value : Word) :
      At s (some .tstore) → s.isStatic = false → s.stack.val = key :: first.val →
      first.val = value :: rest.val → s.gas < 100 →
      Rule s (.exception { s with stack := rest } .outOfGas)
  | tstore (s t : State) (first rest : Stack) (key value : Word) (tracker : TransactionState.State) :
      At s (some .tstore) → s.isStatic = false → s.stack.val = key :: first.val →
      first.val = value :: rest.val → 100 ≤ s.gas →
      TransientWriteFields s.tracker tracker s.context.environment.currentTarget key value →
      Advances { s with tracker } t (s.pc + 1) (s.gas - 100) rest.val → Rule s (.continue t)
  | sstoreStatic (s) : At s (some .sstore) → s.isStatic = true →
      Rule s (.exception s .writeInStaticContext)
  | sstoreUnderflow (s) : At s (some .sstore) → s.isStatic = false → s.stack.val = [] →
      Rule s (.exception s .stackUnderflow)
  | sstoreSecondUnderflow (s : State) (rest : Stack) (key : Word) :
      At s (some .sstore) → s.isStatic = false → s.stack.val = key :: rest.val → rest.val = [] →
      Rule s (.exception { s with stack := rest } .stackUnderflow)
  | sstoreSentry (s : State) (first rest : Stack) (key value : Word) :
      At s (some .sstore) → s.isStatic = false → s.stack.val = key :: first.val →
      first.val = value :: rest.val → s.gas < 2301 →
      Rule s (.exception { s with stack := rest } .outOfGas)
  | sstoreExecutionGas (s ready : State) (first rest : Stack) (key value : Word) (cost stateCost : Nat) :
      At s (some .sstore) → s.isStatic = false → s.stack.val = key :: first.val →
      first.val = value :: rest.val → 2301 ≤ s.gas →
      SstoreReady s ready rest key value cost stateCost → ready.gas < cost →
      Rule s (.exception ready .outOfGas)
  | sstoreStateGas (s ready charged : State) (first rest : Stack) (key value : Word) (cost stateCost : Nat) :
      At s (some .sstore) → s.isStatic = false → s.stack.val = key :: first.val →
      first.val = value :: rest.val → 2301 ≤ s.gas →
      SstoreReady s ready rest key value cost stateCost → cost ≤ ready.gas →
      SstoreExecutionFields ready charged cost → charged.stateGas.reservoir + charged.gas < stateCost →
      Rule s (.exception charged .outOfGas)
  | sstoreMissing (s ready charged paid result : State) (first rest : Stack) (key value : Word) (cost stateCost : Nat) :
      At s (some .sstore) → s.isStatic = false → s.stack.val = key :: first.val →
      first.val = value :: rest.val → 2301 ≤ s.gas →
      SstoreReady s ready rest key value cost stateCost → cost ≤ ready.gas →
      SstoreExecutionFields ready charged cost → SstoreChargeFields charged paid stateCost →
      SstoreAccount paid = none → SstoreWriteFields paid result key value false →
      Rule s (.exception result .missingStorageAccount)
  | sstoreSuccess (s ready charged paid result : State) (first rest : Stack) (key value : Word) (cost stateCost : Nat) :
      At s (some .sstore) → s.isStatic = false → s.stack.val = key :: first.val →
      first.val = value :: rest.val → 2301 ≤ s.gas →
      SstoreReady s ready rest key value cost stateCost → cost ≤ ready.gas →
      SstoreExecutionFields ready charged cost → SstoreChargeFields charged paid stateCost →
      SstoreAccount paid ≠ none → SstoreWriteFields paid result key value true →
      Rule s (.continue result)
  | sloadUnderflow (s) : At s (some .sload) → s.stack.val = [] →
      Rule s (.exception s .stackUnderflow)
  | sloadGas (s : State) (rest : Stack) (key : Word) : At s (some .sload) → s.stack.val = key :: rest.val →
      s.gas < SloadCost s key →
      Rule s (.exception { s with stack := rest, warmSlots := SloadWarm s key } .outOfGas)
  | sload (s t : State) (rest : Stack) (key : Word) : At s (some .sload) → s.stack.val = key :: rest.val →
      SloadCost s key ≤ s.gas →
      Advances { s with warmSlots := SloadWarm s key, tracker := SloadRead s key } t (s.pc + 1)
        (s.gas - SloadCost s key) (SloadValue s key :: rest.val) → Rule s (.continue t)
  | balanceUnderflow (s) : At s (some .balance) → s.stack.val = [] →
      Rule s (.exception s .stackUnderflow)
  | balanceGas (s : State) (rest : Stack) (x : Word) : At s (some .balance) → s.stack.val = x :: rest.val →
      s.gas < BalanceCost s (BalanceAddress x) →
      Rule s (.exception { s with stack := rest, warmAddresses := BalanceWarm s (BalanceAddress x) } .outOfGas)
  | balance (s t : State) (rest : Stack) (x : Word) : At s (some .balance) → s.stack.val = x :: rest.val →
      BalanceCost s (BalanceAddress x) ≤ s.gas →
      Advances { s with warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x) } t (s.pc + 1)
        (s.gas - BalanceCost s (BalanceAddress x))
        ((BalanceAccount s (BalanceAddress x)).balance :: rest.val) → Rule s (.continue t)
  | extCodeSizeUnderflow (s) : At s (some .extcodesize) → s.stack.val = [] →
      Rule s (.exception s .stackUnderflow)
  | extCodeSizeGas (s : State) (rest : Stack) (x : Word) : At s (some .extcodesize) →
      s.stack.val = x :: rest.val → s.gas < ExtCodeSizeCost s (BalanceAddress x) →
      Rule s (.exception { s with stack := rest, warmAddresses := BalanceWarm s (BalanceAddress x) } .outOfGas)
  | extCodeSizeMissing (s : State) (rest : Stack) (x : Word) : At s (some .extcodesize) →
      s.stack.val = x :: rest.val → ExtCodeSizeCost s (BalanceAddress x) ≤ s.gas →
      ExtCodeBytes s (BalanceAddress x) = none →
      Rule s (.exception { s with stack := rest, warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x), gas := s.gas - ExtCodeSizeCost s (BalanceAddress x) } .missingCode)
  | extCodeSize (s t : State) (rest : Stack) (x : Word) (code : ByteArray) : At s (some .extcodesize) →
      s.stack.val = x :: rest.val → ExtCodeSizeCost s (BalanceAddress x) ≤ s.gas →
      ExtCodeBytes s (BalanceAddress x) = some code →
      Advances { s with warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x) }
        t (s.pc + 1) (s.gas - ExtCodeSizeCost s (BalanceAddress x)) (BitVec.ofNat 256 code.size :: rest.val) →
      Rule s (.continue t)
  | extCodeHashUnderflow (s) : At s (some .extcodehash) → s.stack.val = [] →
      Rule s (.exception s .stackUnderflow)
  | extCodeHashGas (s : State) (rest : Stack) (x : Word) : At s (some .extcodehash) →
      s.stack.val = x :: rest.val → s.gas < BalanceCost s (BalanceAddress x) →
      Rule s (.exception { s with stack := rest, warmAddresses := BalanceWarm s (BalanceAddress x) } .outOfGas)
  | extCodeHash (s t : State) (rest : Stack) (x : Word) : At s (some .extcodehash) →
      s.stack.val = x :: rest.val → BalanceCost s (BalanceAddress x) ≤ s.gas →
      Advances { s with warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x) }
        t (s.pc + 1) (s.gas - BalanceCost s (BalanceAddress x)) (ExtCodeHashValue s (BalanceAddress x) :: rest.val) →
      Rule s (.continue t)
  | extCodeCopyEmpty (s) : At s (some .extcodecopy) → s.stack.val = [] →
      Rule s (.exception s .stackUnderflow)
  | extCodeCopySecond (s : State) (first : Stack) (x : Word) : At s (some .extcodecopy) →
      s.stack.val = x :: first.val → first.val = [] → Rule s (.exception { s with stack := first } .stackUnderflow)
  | extCodeCopyThird (s : State) (first second : Stack) (x destination : Word) : At s (some .extcodecopy) →
      s.stack.val = x :: first.val → first.val = destination :: second.val → second.val = [] →
      Rule s (.exception { s with stack := second } .stackUnderflow)
  | extCodeCopyFourth (s : State) (first second third : Stack) (x destination source : Word) : At s (some .extcodecopy) →
      s.stack.val = x :: first.val → first.val = destination :: second.val → second.val = source :: third.val → third.val = [] →
      Rule s (.exception { s with stack := third } .stackUnderflow)
  | extCodeCopyGas (s : State) (first second third rest : Stack) (x destination source length : Word) :
      At s (some .extcodecopy) → s.stack.val = x :: first.val → first.val = destination :: second.val →
      second.val = source :: third.val → third.val = length :: rest.val →
      s.gas < ExtCodeCopyCost s (BalanceAddress x) destination length →
      Rule s (.exception { s with stack := rest, warmAddresses := BalanceWarm s (BalanceAddress x) } .outOfGas)
  | extCodeCopyMissing (s t : State) (first second third rest : Stack) (x destination source length : Word) :
      At s (some .extcodecopy) → s.stack.val = x :: first.val → first.val = destination :: second.val →
      second.val = source :: third.val → third.val = length :: rest.val →
      ExtCodeCopyCost s (BalanceAddress x) destination length ≤ s.gas → ExtCodeBytes s (BalanceAddress x) = none →
      AdvancesMemory { s with warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x) }
        t (Memory.Allocation.expand s.memory destination.toNat length.toNat) s.pc
        (s.gas - ExtCodeCopyCost s (BalanceAddress x) destination length) rest.val → Rule s (.exception t .missingCode)
  | extCodeCopy (s t : State) (first second third rest : Stack) (x destination source length : Word) (code : ByteArray) :
      At s (some .extcodecopy) → s.stack.val = x :: first.val → first.val = destination :: second.val →
      second.val = source :: third.val → third.val = length :: rest.val →
      ExtCodeCopyCost s (BalanceAddress x) destination length ≤ s.gas → ExtCodeBytes s (BalanceAddress x) = some code →
      AdvancesMemory { s with warmAddresses := BalanceWarm s (BalanceAddress x), tracker := BalanceRead s (BalanceAddress x) }
        t (Memory.Allocation.write (Memory.Allocation.expand s.memory destination.toNat length.toNat) destination.toNat
          (CallData.readRange code source.toNat length.toNat)) (s.pc + 1)
        (s.gas - ExtCodeCopyCost s (BalanceAddress x) destination length) rest.val → Rule s (.continue t)
  | finishEmpty (s : State) (kind : FinishKind) : At s (some kind.opcode) → s.stack.val = [] →
      Rule s (.exception s .stackUnderflow)
  | finishSecond (s : State) (kind : FinishKind) (first : Stack) (offset : Word) :
      At s (some kind.opcode) → s.stack.val = offset :: first.val → first.val = [] →
      Rule s (.exception { s with stack := first } .stackUnderflow)
  | finishGas (s : State) (kind : FinishKind) (first rest : Stack) (offset length : Word) :
      At s (some kind.opcode) → s.stack.val = offset :: first.val → first.val = length :: rest.val →
      s.gas < Gas.rangeCost s.memory.words offset.toNat length.toNat →
      Rule s (.exception { s with stack := rest } .outOfGas)
  | finishReturn (s t : State) (first rest : Stack) (offset length : Word) :
      At s (some .return) → s.stack.val = offset :: first.val → first.val = length :: rest.val →
      Gas.rangeCost s.memory.words offset.toNat length.toNat ≤ s.gas →
      AdvancesMemory s t (Memory.Allocation.expand s.memory offset.toNat length.toNat) s.pc
        (s.gas - Gas.rangeCost s.memory.words offset.toNat length.toNat) rest.val →
      Rule s (.returned t ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩)
  | finishRevert (s t : State) (first rest : Stack) (offset length : Word) :
      At s (some .revert) → s.stack.val = offset :: first.val → first.val = length :: rest.val →
      Gas.rangeCost s.memory.words offset.toNat length.toNat ≤ s.gas →
      AdvancesMemory s t (Memory.Allocation.expand s.memory offset.toNat length.toNat) s.pc
        (s.gas - Gas.rangeCost s.memory.words offset.toNat length.toNat) rest.val →
      Rule s (.revert t t.gas ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩)
  | logEmpty (s : State) (count : Fin 5) : At s (some (.log count)) → s.stack.val = [] →
      Rule s (.exception s .stackUnderflow)
  | logSecond (s : State) (count : Fin 5) (first : Stack) (offset : Word) :
      At s (some (.log count)) → s.stack.val = offset :: first.val → first.val = [] →
      Rule s (.exception { s with stack := first } .stackUnderflow)
  | logTopicsUnderflow (s : State) (count : Fin 5) (first rest : Stack) (offset length : Word) :
      At s (some (.log count)) → s.stack.val = offset :: first.val → first.val = length :: rest.val →
      rest.val.length < count.val → Rule s (.exception { s with stack := Stack.empty } .stackUnderflow)
  | logGas (s : State) (count : Fin 5) (first rest tail : Stack) (offset length : Word) (topics : List Word) :
      At s (some (.log count)) → s.stack.val = offset :: first.val → first.val = length :: rest.val →
      rest.val = topics ++ tail.val → topics.length = count.val →
      s.gas < 375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat →
      Rule s (.exception { s with stack := tail } .outOfGas)
  | logStatic (s t : State) (count : Fin 5) (first rest tail : Stack) (offset length : Word) (topics : List Word) :
      At s (some (.log count)) → s.stack.val = offset :: first.val → first.val = length :: rest.val →
      rest.val = topics ++ tail.val → topics.length = count.val → s.isStatic = true →
      375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat ≤ s.gas →
      AdvancesMemory s t (Memory.Allocation.expand s.memory offset.toNat length.toNat) s.pc
        (s.gas - (375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat)) tail.val →
      Rule s (.exception t .writeInStaticContext)
  | logSuccess (s t : State) (count : Fin 5) (first rest tail : Stack) (offset length : Word) (topics : List Word) :
      At s (some (.log count)) → s.stack.val = offset :: first.val → first.val = length :: rest.val →
      rest.val = topics ++ tail.val → topics.length = count.val → s.isStatic = false →
      375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat ≤ s.gas →
      AdvancesMemory { s with logs := s.logs ++ [⟨s.context.environment.currentTarget, topics.map logTopic,
          ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩⟩] }
        t (Memory.Allocation.expand s.memory offset.toNat length.toNat) (s.pc + 1)
        (s.gas - (375 + 8 * length.toNat + 375 * count.val + Gas.rangeCost s.memory.words offset.toNat length.toNat)) tail.val →
      Rule s (.continue t)
  | selfBalanceGas (s) : At s (some .selfbalance) → s.gas < 5 →
      Rule s (.exception s .outOfGas)
  | selfBalanceFull (s) : At s (some .selfbalance) → 5 ≤ s.gas →
      s.stack.val.length = 1024 →
      Rule s (.exception { s with tracker := SelfBalanceRead s } .stackOverflow)
  | selfBalance (s t) : At s (some .selfbalance) → 5 ≤ s.gas →
      s.stack.val.length < 1024 →
      Advances { s with tracker := SelfBalanceRead s } t (s.pc + 1) (s.gas - 5)
        ((SelfBalanceAccount s).balance :: s.stack.val) → Rule s (.continue t)
  | dupnGas (s) : At s (some .dupn) → s.gas < 3 → Rule s (.exception s .outOfGas)
  | dupnInvalid (s) : At s (some .dupn) → 3 ≤ s.gas →
      StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = none →
      Rule s (.exception s .invalidParameter)
  | dupnUnderflow (s n) : At s (some .dupn) → 3 ≤ s.gas →
      StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = some n →
      s.stack.height ≤ n - 1 → Rule s (.exception s .stackUnderflow)
  | dupnOverflow (s n) : At s (some .dupn) → 3 ≤ s.gas →
      StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = some n →
      n - 1 < s.stack.height → s.stack.height = 1024 → Rule s (.exception s .stackOverflow)
  | dupn (s t n) (depth : n - 1 < s.stack.height) : At s (some .dupn) → 3 ≤ s.gas →
      StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = some n →
      s.stack.height < 1024 →
      Advances s t (s.pc + 2) (s.gas - 3) (s.stack.toList[n - 1]'depth :: s.stack.toList) →
      Rule s (.continue t)
  | swapnGas (s) : At s (some .swapn) → s.gas < 3 → Rule s (.exception s .outOfGas)
  | swapnInvalid (s) : At s (some .swapn) → 3 ≤ s.gas →
      StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = none →
      Rule s (.exception s .invalidParameter)
  | swapnUnderflow (s n) : At s (some .swapn) → 3 ≤ s.gas →
      StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = some n →
      s.stack.height ≤ n → Rule s (.exception s .stackUnderflow)
  | swapn (s t n) (depth : n < s.stack.height) : At s (some .swapn) → 3 ≤ s.gas →
      StackImmediate.decodeSingle (StackImmediate.byte s.code s.pc) = some n →
      Advances s t (s.pc + 2) (s.gas - 3)
        ((s.stack.toList.set 0 (s.stack.toList[n]'depth)).set n
          (s.stack.toList[0]'(by change 0 < s.stack.height; omega))) → Rule s (.continue t)
  | exchangeGas (s) : At s (some .exchange) → s.gas < 3 → Rule s (.exception s .outOfGas)
  | exchangeInvalid (s) : At s (some .exchange) → 3 ≤ s.gas →
      StackImmediate.decodePair (StackImmediate.byte s.code s.pc) = none →
      Rule s (.exception s .invalidParameter)
  | exchangeUnderflow (s n m) : At s (some .exchange) → 3 ≤ s.gas →
      StackImmediate.decodePair (StackImmediate.byte s.code s.pc) = some (n, m) →
      (s.stack.height ≤ n ∨ s.stack.height ≤ m) → Rule s (.exception s .stackUnderflow)
  | exchange (s t n m) (hn : n < s.stack.height) (hm : m < s.stack.height) :
      At s (some .exchange) → 3 ≤ s.gas →
      StackImmediate.decodePair (StackImmediate.byte s.code s.pc) = some (n, m) →
      Advances s t (s.pc + 2) (s.gas - 3)
        ((s.stack.toList.set n (s.stack.toList[m]'hm)).set m (s.stack.toList[n]'hn)) →
      Rule s (.continue t)
  | keccakEmpty (s) : At s (some .keccak) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | keccakGas (s offset length xs) : At s (some .keccak) →
      s.stack.val = offset :: length :: xs →
      s.gas < Gas.keccakCost s.memory.words offset.toNat length.toNat →
      Rule s (.exception s .outOfGas)
  | keccak (s t offset length xs) : At s (some .keccak) →
      s.stack.val = offset :: length :: xs →
      Gas.keccakCost s.memory.words offset.toNat length.toNat ≤ s.gas →
      AdvancesMemory s t (Memory.Allocation.expand s.memory offset.toNat length.toNat)
        (s.pc + 1) (s.gas - Gas.keccakCost s.memory.words offset.toNat length.toNat)
        (digestWord (EthLib.Cryptography.Hash.Keccak.keccak256
          ⟨(Memory.readRange s.memory.store offset.toNat length.toNat).toArray⟩) :: xs) →
      Rule s (.continue t)
  | calldataloadEmpty (s) : At s (some .calldataload) → s.stack.val = [] →
      Rule s (.exception s .stackUnderflow)
  | calldataloadGas (s x xs) : At s (some .calldataload) → s.stack.val = x :: xs →
      s.gas < 3 → Rule s (.exception s .outOfGas)
  | calldataload (s t x xs) : At s (some .calldataload) → s.stack.val = x :: xs →
      3 ≤ s.gas → Advances s t (s.pc + 1) (s.gas - 3)
        (CallData.load s.context x :: xs) → Rule s (.continue t)
  | blockhashEmpty (s) : At s (some .blockhash) → s.stack.val = [] →
      Rule s (.exception s .stackUnderflow)
  | blockhashGas (s x xs) : At s (some .blockhash) → s.stack.val = x :: xs →
      s.gas < 20 → Rule s (.exception s .outOfGas)
  | blockhash (s t x xs value) : At s (some .blockhash) → s.stack.val = x :: xs →
      20 ≤ s.gas → BlockHashValue s.context.environment.blockHashes
        s.context.environment.number x value →
      Advances s t (s.pc + 1) (s.gas - 20) (value :: xs) → Rule s (.continue t)
  | blobhashEmpty (s) : At s (some .blobhash) → s.stack.val = [] →
      Rule s (.exception s .stackUnderflow)
  | blobhashGas (s x xs) : At s (some .blobhash) → s.stack.val = x :: xs →
      s.gas < 3 → Rule s (.exception s .outOfGas)
  | blobhash (s t x xs) : At s (some .blobhash) → s.stack.val = x :: xs →
      3 ≤ s.gas → Advances s t (s.pc + 1) (s.gas - 3)
        (Environment.blobHash s.context.environment x :: xs) → Rule s (.continue t)
  | returnDataCopyEmpty (s) : At s (some .returndatacopy) →
      s.stack.val.length < 3 → Rule s (.exception s .stackUnderflow)
  | returnDataCopyGas (s) (destination offset length xs) :
      At s (some .returndatacopy) → s.stack.val = destination :: offset :: length :: xs →
      s.gas < Gas.inputCopyCost s.memory.words destination.toNat length.toNat →
      Rule s (.exception s .outOfGas)
  | returnDataCopyBounds (s) (destination offset length xs) :
      At s (some .returndatacopy) → s.stack.val = destination :: offset :: length :: xs →
      Gas.inputCopyCost s.memory.words destination.toNat length.toNat ≤ s.gas →
      s.returnData.size < offset.toNat + length.toNat → Rule s (.exception s .outOfBoundsRead)
  | returnDataCopy (s t) (destination offset length xs) :
      At s (some .returndatacopy) → s.stack.val = destination :: offset :: length :: xs →
      Gas.inputCopyCost s.memory.words destination.toNat length.toNat ≤ s.gas →
      offset.toNat + length.toNat ≤ s.returnData.size →
      AdvancesMemory s t (Memory.Allocation.write s.memory destination.toNat
        ((s.returnData.data.toList.drop offset.toNat).take length.toNat))
        (s.pc + 1) (s.gas - Gas.inputCopyCost s.memory.words destination.toNat length.toNat) xs →
      Rule s (.continue t)
  | inputCopyEmpty (s) (source : InputSource) : At s (some source.opcode) →
      s.stack.val.length < 3 → Rule s (.exception s .stackUnderflow)
  | inputCopyGas (s) (source : InputSource) (destination offset length xs) :
      At s (some source.opcode) → s.stack.val = destination :: offset :: length :: xs →
      s.gas < Gas.inputCopyCost s.memory.words destination.toNat length.toNat →
      Rule s (.exception s .outOfGas)
  | inputCopy (s t) (source : InputSource) (destination offset length xs) :
      At s (some source.opcode) → s.stack.val = destination :: offset :: length :: xs →
      Gas.inputCopyCost s.memory.words destination.toNat length.toNat ≤ s.gas →
      AdvancesMemory s t (Memory.Allocation.write s.memory destination.toNat
        (CallData.readRange (source.bytes s) offset.toNat length.toNat))
        (s.pc + 1) (s.gas - Gas.inputCopyCost s.memory.words destination.toNat length.toNat) xs →
      Rule s (.continue t)
  | mcopyEmpty (s) : At s (some .mcopy) → s.stack.val.length < 3 →
      Rule s (.exception s .stackUnderflow)
  | mcopyGas (s destination source length xs) : At s (some .mcopy) →
      s.stack.val = destination :: source :: length :: xs →
      s.gas < Gas.mcopyCost s.memory.words destination.toNat source.toNat length.toNat →
      Rule s (.exception s .outOfGas)
  | mcopy (s t destination source length xs) : At s (some .mcopy) →
      s.stack.val = destination :: source :: length :: xs →
      Gas.mcopyCost s.memory.words destination.toNat source.toNat length.toNat ≤ s.gas →
      AdvancesMemory s t (Memory.Allocation.copy s.memory destination.toNat source.toNat length.toNat)
        (s.pc + 1) (s.gas - Gas.mcopyCost s.memory.words destination.toNat source.toNat length.toNat) xs →
      Rule s (.continue t)
  | mloadEmpty (s) : At s (some .mload) → s.stack.val = [] →
      Rule s (.exception s .stackUnderflow)
  | mloadGas (s offset xs) : At s (some .mload) → s.stack.val = offset :: xs →
      s.gas < 3 + Gas.rangeCost s.memory.words offset.toNat 32 →
      Rule s (.exception s .outOfGas)
  | mload (s t offset xs) : At s (some .mload) → s.stack.val = offset :: xs →
      3 + Gas.rangeCost s.memory.words offset.toNat 32 ≤ s.gas →
      AdvancesMemory s t (Memory.Allocation.loadWord s.memory offset.toNat).2
        (s.pc + 1) (s.gas - (3 + Gas.rangeCost s.memory.words offset.toNat 32))
        ((Memory.Allocation.loadWord s.memory offset.toNat).1 :: xs) → Rule s (.continue t)
  | mstoreEmpty (s) : At s (some .mstore) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | mstoreGas (s offset value xs) : At s (some .mstore) →
      s.stack.val = offset :: value :: xs →
      s.gas < 3 + Gas.rangeCost s.memory.words offset.toNat 32 →
      Rule s (.exception s .outOfGas)
  | mstore (s t offset value xs) : At s (some .mstore) →
      s.stack.val = offset :: value :: xs →
      3 + Gas.rangeCost s.memory.words offset.toNat 32 ≤ s.gas →
      AdvancesMemory s t (Memory.Allocation.storeWord s.memory offset.toNat value)
        (s.pc + 1) (s.gas - (3 + Gas.rangeCost s.memory.words offset.toNat 32)) xs →
      Rule s (.continue t)
  | mstore8Empty (s) : At s (some .mstore8) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | mstore8Gas (s offset value xs) : At s (some .mstore8) →
      s.stack.val = offset :: value :: xs →
      s.gas < 3 + Gas.rangeCost s.memory.words offset.toNat 1 →
      Rule s (.exception s .outOfGas)
  | mstore8 (s t offset value xs) : At s (some .mstore8) →
      s.stack.val = offset :: value :: xs →
      3 + Gas.rangeCost s.memory.words offset.toNat 1 ≤ s.gas →
      AdvancesMemory s t (Memory.Allocation.storeByte s.memory offset.toNat value)
        (s.pc + 1) (s.gas - (3 + Gas.rangeCost s.memory.words offset.toNat 1)) xs →
      Rule s (.continue t)
  | jumpEmpty (s) : At s (some .jump) → s.stack.val = [] →
      Rule s (.exception s .stackUnderflow)
  | jumpGas (s x xs) : At s (some .jump) → s.stack.val = x :: xs → s.gas < 8 →
      Rule s (.exception s .outOfGas)
  | jumpInvalid (s x xs) : At s (some .jump) → s.stack.val = x :: xs → 8 ≤ s.gas →
      ¬ ValidJumpDest s.code x.toNat → Rule s (.exception s .invalidJumpDestination)
  | jump (s t x xs) : At s (some .jump) → s.stack.val = x :: xs → 8 ≤ s.gas →
      ValidJumpDest s.code x.toNat → Advances s t x.toNat (s.gas - 8) xs → Rule s (.continue t)
  | jumpiEmpty (s) : At s (some .jumpi) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | jumpiGas (s x y xs) : At s (some .jumpi) → s.stack.val = x :: y :: xs → s.gas < 10 →
      Rule s (.exception s .outOfGas)
  | jumpiInvalid (s x y xs) : At s (some .jumpi) → s.stack.val = x :: y :: xs → 10 ≤ s.gas →
      y.toNat ≠ 0 → ¬ ValidJumpDest s.code x.toNat →
      Rule s (.exception s .invalidJumpDestination)
  | jumpiFalse (s t x y xs) : At s (some .jumpi) → s.stack.val = x :: y :: xs → 10 ≤ s.gas →
      y.toNat = 0 → Advances s t (s.pc + 1) (s.gas - 10) xs → Rule s (.continue t)
  | jumpiTrue (s t x y xs) : At s (some .jumpi) → s.stack.val = x :: y :: xs → 10 ≤ s.gas →
      y.toNat ≠ 0 → ValidJumpDest s.code x.toNat →
      Advances s t x.toNat (s.gas - 10) xs → Rule s (.continue t)
  | jumpdestGas (s) : At s (some .jumpdest) → s.gas < 1 → Rule s (.exception s .outOfGas)
  | jumpdest (s t) : At s (some .jumpdest) → 1 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 1) s.stack.val → Rule s (.continue t)
  | observationGas (s) (o : Observation) : At s (some o.opcode) → s.gas < 2 →
      Rule s (.exception s .outOfGas)
  | observationFull (s) (o : Observation) : At s (some o.opcode) → 2 ≤ s.gas →
      s.stack.val.length = 1024 → Rule s (.exception s .stackOverflow)
  | observation (s t) (o : Observation) : At s (some o.opcode) → 2 ≤ s.gas →
      s.stack.val.length < 1024 →
      Advances s t (s.pc + 1) (s.gas - 2)
        (BitVec.ofNat 256 (o.value s) :: s.stack.val) → Rule s (.continue t)
  | pushGas (s n) : At s (some (.push n)) → s.gas < (if n.val = 0 then 2 else 3) →
      Rule s (.exception s .outOfGas)
  | pushFull (s n) : At s (some (.push n)) → (if n.val = 0 then 2 else 3) ≤ s.gas →
      s.stack.val.length = 1024 → Rule s (.exception s .stackOverflow)
  | push (s t n) : At s (some (.push n)) → (if n.val = 0 then 2 else 3) ≤ s.gas →
      s.stack.val.length < 1024 →
      Advances s t (PushImmediate.nextPC s.pc n) (s.gas - (if n.val = 0 then 2 else 3))
        (PushImmediate.value s.code s.pc n :: s.stack.val) → Rule s (.continue t)
  | popEmpty (s) : At s (some .pop) → s.stack.val = [] → Rule s (.exception s .stackUnderflow)
  | popGas (s x xs) : At s (some .pop) → s.stack.val = x :: xs → s.gas < 2 →
      Rule s (.exception s .outOfGas)
  | pop (s t x xs) : At s (some .pop) → s.stack.val = x :: xs → 2 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 2) xs → Rule s (.continue t)
  | addEmpty (s) : At s (some .add) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | addGas (s x y xs) : At s (some .add) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | add (s t x y xs) : At s (some .add) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.add x y :: xs) → Rule s (.continue t)
  | addmodEmpty (s) : At s (some .addmod) → s.stack.val.length < 3 →
      Rule s (.exception s .stackUnderflow)
  | addmodGas (s x y m xs) : At s (some .addmod) → s.stack.val = x :: y :: m :: xs → s.gas < 8 →
      Rule s (.exception s .outOfGas)
  | addmod (s t x y m xs) : At s (some .addmod) → s.stack.val = x :: y :: m :: xs → 8 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 8) (Word.addmod x y m :: xs) → Rule s (.continue t)
  | mulmodEmpty (s) : At s (some .mulmod) → s.stack.val.length < 3 →
      Rule s (.exception s .stackUnderflow)
  | mulmodGas (s x y m xs) : At s (some .mulmod) → s.stack.val = x :: y :: m :: xs → s.gas < 8 →
      Rule s (.exception s .outOfGas)
  | mulmod (s t x y m xs) : At s (some .mulmod) → s.stack.val = x :: y :: m :: xs → 8 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 8) (Word.mulmod x y m :: xs) → Rule s (.continue t)
  | expEmpty (s) : At s (some .exp) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | expGas (s x y xs) : At s (some .exp) → s.stack.val = x :: y :: xs → s.gas < Gas.expCost y →
      Rule s (.exception s .outOfGas)
  | exp (s t x y xs) : At s (some .exp) → s.stack.val = x :: y :: xs → Gas.expCost y ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - Gas.expCost y) (Word.exp x y :: xs) → Rule s (.continue t)
  | mulEmpty (s) : At s (some .mul) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | mulGas (s x y xs) : At s (some .mul) → s.stack.val = x :: y :: xs → s.gas < 5 →
      Rule s (.exception s .outOfGas)
  | mul (s t x y xs) : At s (some .mul) → s.stack.val = x :: y :: xs → 5 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 5) (Word.mul x y :: xs) → Rule s (.continue t)
  | subEmpty (s) : At s (some .sub) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | subGas (s x y xs) : At s (some .sub) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | sub (s t x y xs) : At s (some .sub) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.sub x y :: xs) → Rule s (.continue t)
  | divEmpty (s) : At s (some .div) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | divGas (s x y xs) : At s (some .div) → s.stack.val = x :: y :: xs → s.gas < 5 →
      Rule s (.exception s .outOfGas)
  | div (s t x y xs) : At s (some .div) → s.stack.val = x :: y :: xs → 5 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 5) (Word.div x y :: xs) → Rule s (.continue t)
  | modEmpty (s) : At s (some .mod) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | modGas (s x y xs) : At s (some .mod) → s.stack.val = x :: y :: xs → s.gas < 5 →
      Rule s (.exception s .outOfGas)
  | mod (s t x y xs) : At s (some .mod) → s.stack.val = x :: y :: xs → 5 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 5) (Word.mod x y :: xs) → Rule s (.continue t)
  | sdivEmpty (s) : At s (some .sdiv) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | sdivGas (s x y xs) : At s (some .sdiv) → s.stack.val = x :: y :: xs → s.gas < 5 →
      Rule s (.exception s .outOfGas)
  | sdiv (s t x y xs) : At s (some .sdiv) → s.stack.val = x :: y :: xs → 5 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 5) (Word.sdiv x y :: xs) → Rule s (.continue t)
  | smodEmpty (s) : At s (some .smod) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | smodGas (s x y xs) : At s (some .smod) → s.stack.val = x :: y :: xs → s.gas < 5 →
      Rule s (.exception s .outOfGas)
  | smod (s t x y xs) : At s (some .smod) → s.stack.val = x :: y :: xs → 5 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 5) (Word.smod x y :: xs) → Rule s (.continue t)
  | ltEmpty (s) : At s (some .lt) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | ltGas (s x y xs) : At s (some .lt) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | lt (s t x y xs) : At s (some .lt) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.ltResult x y :: xs) → Rule s (.continue t)
  | gtEmpty (s) : At s (some .gt) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | gtGas (s x y xs) : At s (some .gt) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | gt (s t x y xs) : At s (some .gt) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.gtResult x y :: xs) → Rule s (.continue t)
  | sltEmpty (s) : At s (some .slt) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | sltGas (s x y xs) : At s (some .slt) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | slt (s t x y xs) : At s (some .slt) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.sltResult x y :: xs) → Rule s (.continue t)
  | sgtEmpty (s) : At s (some .sgt) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | sgtGas (s x y xs) : At s (some .sgt) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | sgt (s t x y xs) : At s (some .sgt) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.sgtResult x y :: xs) → Rule s (.continue t)
  | eqEmpty (s) : At s (some .eq) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | eqGas (s x y xs) : At s (some .eq) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | eq (s t x y xs) : At s (some .eq) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.eqResult x y :: xs) → Rule s (.continue t)
  | andEmpty (s) : At s (some .and) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | andGas (s x y xs) : At s (some .and) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | and (s t x y xs) : At s (some .and) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.bitwiseAnd x y :: xs) → Rule s (.continue t)
  | shlEmpty (s) : At s (some .shl) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | shlGas (s x y xs) : At s (some .shl) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | shl (s t x y xs) : At s (some .shl) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.shl x y :: xs) → Rule s (.continue t)
  | shrEmpty (s) : At s (some .shr) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | shrGas (s x y xs) : At s (some .shr) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | shr (s t x y xs) : At s (some .shr) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.shr x y :: xs) → Rule s (.continue t)
  | sarEmpty (s) : At s (some .sar) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | sarGas (s x y xs) : At s (some .sar) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | sar (s t x y xs) : At s (some .sar) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.sar x y :: xs) → Rule s (.continue t)
  | byteEmpty (s) : At s (some .byte) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | byteGas (s x y xs) : At s (some .byte) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | byte (s t x y xs) : At s (some .byte) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.byte x y :: xs) → Rule s (.continue t)
  | signextendEmpty (s) : At s (some .signextend) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | signextendGas (s x y xs) : At s (some .signextend) → s.stack.val = x :: y :: xs → s.gas < 5 →
      Rule s (.exception s .outOfGas)
  | signextend (s t x y xs) : At s (some .signextend) → s.stack.val = x :: y :: xs → 5 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 5) (Word.signextend x y :: xs) → Rule s (.continue t)
  | orEmpty (s) : At s (some .or) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | orGas (s x y xs) : At s (some .or) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | or (s t x y xs) : At s (some .or) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.bitwiseOr x y :: xs) → Rule s (.continue t)
  | xorEmpty (s) : At s (some .xor) → s.stack.val.length < 2 →
      Rule s (.exception s .stackUnderflow)
  | xorGas (s x y xs) : At s (some .xor) → s.stack.val = x :: y :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | xor (s t x y xs) : At s (some .xor) → s.stack.val = x :: y :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.bitwiseXor x y :: xs) → Rule s (.continue t)
  | iszeroEmpty (s) : At s (some .iszero) → s.stack.val = [] → Rule s (.exception s .stackUnderflow)
  | iszeroGas (s x xs) : At s (some .iszero) → s.stack.val = x :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | iszero (s t x xs) : At s (some .iszero) → s.stack.val = x :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.iszeroResult x :: xs) → Rule s (.continue t)
  | clzEmpty (s) : At s (some .clz) → s.stack.val = [] → Rule s (.exception s .stackUnderflow)
  | clzGas (s x xs) : At s (some .clz) → s.stack.val = x :: xs → s.gas < 5 →
      Rule s (.exception s .outOfGas)
  | clz (s t x xs) : At s (some .clz) → s.stack.val = x :: xs → 5 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 5) (Word.countLeadingZeros x :: xs) → Rule s (.continue t)
  | notEmpty (s) : At s (some .not) → s.stack.val = [] → Rule s (.exception s .stackUnderflow)
  | notGas (s x xs) : At s (some .not) → s.stack.val = x :: xs → s.gas < 3 →
      Rule s (.exception s .outOfGas)
  | not (s t x xs) : At s (some .not) → s.stack.val = x :: xs → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3) (Word.bitwiseNot x :: xs) → Rule s (.continue t)
  | dupGas (s i) : At s (some (.dup i)) → s.gas < 3 → Rule s (.exception s .outOfGas)
  | dupEmpty (s i) : At s (some (.dup i)) → 3 ≤ s.gas → s.stack.val.length ≤ i.val →
      Rule s (.exception s .stackUnderflow)
  | dupFull (s i) : At s (some (.dup i)) → 3 ≤ s.gas → i.val < s.stack.val.length →
      s.stack.val.length = 1024 → Rule s (.exception s .stackOverflow)
  | dup (s t i) (h : i.val < s.stack.val.length) : At s (some (.dup i)) → 3 ≤ s.gas →
      s.stack.val.length < 1024 →
      Advances s t (s.pc + 1) (s.gas - 3) (s.stack.val[i.val] :: s.stack.val) →
      Rule s (.continue t)
  | swapGas (s i) : At s (some (.swap i)) → s.gas < 3 → Rule s (.exception s .outOfGas)
  | swapEmpty (s i) : At s (some (.swap i)) → 3 ≤ s.gas → s.stack.val.length ≤ i.val + 1 →
      Rule s (.exception s .stackUnderflow)
  | swap (s t i) (h : i.val + 1 < s.stack.val.length) : At s (some (.swap i)) → 3 ≤ s.gas →
      Advances s t (s.pc + 1) (s.gas - 3)
        ((s.stack.val.set 0 s.stack.val[i.val + 1]).set (i.val + 1) (s.stack.val[0]'(by omega))) →
      Rule s (.continue t)

end EthLib.EVM.Frame
