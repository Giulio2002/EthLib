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
  | .dupn | .swapn | .exchange | .blockhash | .blobhash | .blobbasefee | .coinbase | .timestamp | .number | .slotnum | .prevrandao | .gaslimit | .chainid | .basefee | .address | .origin | .caller | .callvalue | .gasprice | .keccak | .returndatacopy | .returndatasize | .calldatacopy | .codecopy | .calldataload | .calldatasize | .codesize | .mcopy | .mload | .mstore | .mstore8 | .pc | .msize | .gas | .jump | .jumpi | .jumpdest | .addmod | .mulmod | .exp | .shl | .shr | .sar | .byte | .signextend | .lt | .gt | .slt | .sgt | .eq | .iszero | .clz | .and | .or | .xor | .not | .stop | .invalid | .add | .mul | .sub | .div | .mod | .sdiv | .smod | .pop | .push _ | .dup _ | .swap _ => False
  | _ => True

/-- Exact fields of a continuing frame, including fields untouched by this slice. -/
def Advances (s t : State) (pc gas : Nat) (xs : List Word) : Prop :=
  t.code = s.code ∧ t.memory = s.memory ∧ t.pc = pc ∧ t.gas = gas ∧ t.stack.val = xs ∧ t.context = s.context ∧ t.returnData = s.returnData

/-- Exact fields after a memory instruction. -/
def AdvancesMemory (s t : State) (memory : Memory.Allocation.State)
    (pc gas : Nat) (xs : List Word) : Prop :=
  t.code = s.code ∧ t.memory = memory ∧ t.pc = pc ∧ t.gas = gas ∧ t.stack.val = xs ∧ t.context = s.context ∧ t.returnData = s.returnData

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
    exact ⟨gas, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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

/-- Source-oriented rules for one frame transition. -/
inductive Rule : State → Outcome → Prop where
  | endCode (s) : s.code.size ≤ s.pc → Rule s (.stop s)
  | stop (s) : At s (some .stop) → Rule s (.stop { s with pc := s.pc + 1 })
  | invalid (s) : At s none ∨ At s (some .invalid) → Rule s (.exception s .invalidOpcode)
  | unsupported (s op) : At s (some op) → Unsupported op → Rule s (.unsupported s op)
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
