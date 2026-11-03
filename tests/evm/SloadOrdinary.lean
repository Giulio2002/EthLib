import EthLib.EVM

open EthLib.EVM

deriving instance DecidableEq for World.State
deriving instance DecidableEq for TransactionState.Snapshot
deriving instance DecidableEq for TransactionState.State
deriving instance DecidableEq for BlobFee.Schedule
deriving instance DecidableEq for Environment.Context
deriving instance DecidableEq for CallData.Context

private def env : Environment.Context :=
  ⟨7, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, [25, 26], [27, 28], BlobFee.amsterdam⟩

private def writes : List ((World.Address × Word) × Word) := [((7, 3), 42), ((7, 3), 43), ((8, 3), 7)]
private def tracker : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩), (8, ⟨2, 98, 9⟩)], [((7, 3), 90), ((7, 4), 91), ((8, 3), 92)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(7, none), (8, some ⟨3, 42, 9⟩)], writes, [(9, ⟨#[2]⟩)], [7], [((7, 2), 3)]⟩,
    [8], [(8, 3)], [7, 9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩

-- The expected tracker is stated from fixed fixture values and explicit writes and reads.
private def expectedTracker (ws : List ((World.Address × Word) × Word)) (clears : List World.Address)
    (reads : List (World.Address × Word)) : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩), (8, ⟨2, 98, 9⟩)], [((7, 3), 90), ((7, 4), 91), ((8, 3), 92)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(7, none), (8, some ⟨3, 42, 9⟩)], ws, [(9, ⟨#[2]⟩)], clears, [((7, 2), 3)]⟩,
    [8], reads, [7, 9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩

private def initialMemory : Memory.Allocation.State :=
  Memory.Allocation.write Memory.Allocation.empty 2 [0xa1, 0xb2]
private theorem memoryValid : Memory.Allocation.Valid initialMemory :=
  Memory.Allocation.write_valid_for_frame _ _ _ (by intro a _; rfl)

private def frame : Frame.State :=
  ⟨⟨#[0xfe]⟩, 99, ⟨[3, 11], by decide⟩, 2100, initialMemory, memoryValid,
    ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩, tracker, [41, 42], [(7, 4), (8, 3)]⟩

private def expected (code : ByteArray) (pc : Nat) (stack : Stack) (gas : Nat)
    (tx : TransactionState.State) (slots : List (World.Address × Word)) : Frame.State :=
  ⟨code, pc, stack, gas, ⟨[(2, 0xa1), (3, 0xb2)], 1⟩,
    (by change Memory.Allocation.Valid initialMemory; exact memoryValid),
    ⟨⟨#[4]⟩, ⟨7, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
      [25, 26], [27, 28], ⟨⟨11684671, by decide⟩⟩⟩⟩, ⟨#[6]⟩, tx, [41, 42], slots⟩

private def sameFrame (actual expected : Frame.State) : Bool :=
  decide (actual.code = expected.code ∧ actual.pc = expected.pc ∧
    actual.stack.val = expected.stack.val ∧ actual.gas = expected.gas ∧
    actual.memory = expected.memory ∧ actual.context = expected.context ∧
    actual.returnData = expected.returnData ∧ actual.tracker = expected.tracker ∧
    actual.warmAddresses = expected.warmAddresses ∧ actual.warmSlots = expected.warmSlots)

private def check (ok : Bool) : IO Unit :=
  if ok then pure () else throw (IO.userError "SLOAD full-frame assertion failed")

-- A write shadows a clear and parent even when the account is marked created.
#eval check <| match Frame.sload frame with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 ⟨[42, 11], by decide⟩ 0
      (expectedTracker [((7, 3), 42), ((7, 3), 43), ((8, 3), 7)] [7] [(7, 3), (8, 3)]) [(7, 3), (7, 4), (8, 3)]) &&
      TransactionState.getStorageOriginal tracker 7 3 == 0
  | _ => false

-- Warm membership preserves duplicate entries and charges 100.
#eval check <| match Frame.sload { frame with gas := 100, warmSlots := [(7, 3), (7, 4), (7, 3), (8, 3)] } with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 ⟨[42, 11], by decide⟩ 0
      (expectedTracker [((7, 3), 42), ((7, 3), 43), ((8, 3), 7)] [7] [(7, 3), (8, 3)]) [(7, 3), (7, 4), (7, 3), (8, 3)])
  | _ => false

-- A cold failed charge warms the slot after popping but before a tracker read.
#eval check <| match Frame.sload { frame with gas := 2099 } with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfe]⟩ 99 ⟨[11], by decide⟩ 2099
      (expectedTracker [((7, 3), 42), ((7, 3), 43), ((8, 3), 7)] [7] [(8, 3)]) [(7, 3), (7, 4), (8, 3)])
  | _ => false

#eval check <| match Frame.sload { frame with gas := 99, warmSlots := [(7, 3), (7, 4), (7, 3), (8, 3)] } with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfe]⟩ 99 ⟨[11], by decide⟩ 99
      (expectedTracker [((7, 3), 42), ((7, 3), 43), ((8, 3), 7)] [7] [(8, 3)]) [(7, 3), (7, 4), (7, 3), (8, 3)])
  | _ => false

-- Underflow wins over insufficient gas and leaves every frame field unchanged.
#eval check <| match Frame.sload { frame with gas := 0, stack := Stack.empty } with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xfe]⟩ 99 Stack.empty 0
      (expectedTracker [((7, 3), 42), ((7, 3), 43), ((8, 3), 7)] [7] [(8, 3)]) [(7, 4), (8, 3)])
  | _ => false

-- Clear shadows parent slot 4; removing the clear exposes the parent value 91.
#eval check <| match Frame.sload { frame with gas := 100, stack := ⟨[4, 11], by decide⟩ } with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 ⟨[0, 11], by decide⟩ 0
      (expectedTracker [((7, 3), 42), ((7, 3), 43), ((8, 3), 7)] [7] [(7, 4), (8, 3)]) [(7, 4), (8, 3)])
  | _ => false

#eval check <| match Frame.sload { frame with gas := 100, stack := ⟨[4, 11], by decide⟩, tracker := { tracker with writes := { tracker.writes with storageClears := [] } } } with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 ⟨[91, 11], by decide⟩ 0
      (expectedTracker [((7, 3), 42), ((7, 3), 43), ((8, 3), 7)] [] [(7, 4), (8, 3)]) [(7, 4), (8, 3)])
  | _ => false

-- The full 256-bit key, including its top bit, remains distinct from key 3.
#eval check <| match Frame.sload { frame with stack := ⟨[BitVec.ofNat 256 (2^255 + 3), 11], by decide⟩ } with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 ⟨[0, 11], by decide⟩ 0
      (expectedTracker [((7, 3), 42), ((7, 3), 43), ((8, 3), 7)] [7] [(7, BitVec.ofNat 256 (2^255 + 3)), (8, 3)])
      [(7, BitVec.ofNat 256 (2^255 + 3)), (7, 4), (8, 3)])
  | _ => false

#eval check <| match Frame.sload { frame with stack := ⟨[0, 11], by decide⟩ } with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 ⟨[0, 11], by decide⟩ 0
      (expectedTracker [((7, 3), 42), ((7, 3), 43), ((8, 3), 7)] [7] [(7, 0), (8, 3)]) [(7, 0), (7, 4), (8, 3)])
  | _ => false

-- The actual runner pays cold then warm for the same slot.
#eval check <| match Runner.run 4 { frame with code := ⟨#[0x54, 0x90, 0x54, 0x00]⟩, pc := 0, gas := 2203, stack := ⟨[3, 3, 11], by decide⟩ } with
  | .stopped t => sameFrame t (expected ⟨#[0x54, 0x90, 0x54, 0x00]⟩ 4 ⟨[42, 42, 11], by decide⟩ 0
      (expectedTracker [((7, 3), 42), ((7, 3), 43), ((8, 3), 7)] [7] [(7, 3), (7, 3), (8, 3)]) [(7, 3), (7, 4), (8, 3)])
  | _ => false

-- Real opcode dispatch has the same exceptional diagnostics.
#eval check <| match Frame.step { frame with code := ⟨#[0x54]⟩, pc := 0, gas := 2099 } with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0x54]⟩ 0 ⟨[11], by decide⟩ 2099
      (expectedTracker [((7, 3), 42), ((7, 3), 43), ((8, 3), 7)] [7] [(8, 3)]) [(7, 3), (7, 4), (8, 3)])
  | _ => false

#eval check <| match Frame.step { frame with code := ⟨#[0x54]⟩, pc := 0, gas := 0, stack := Stack.empty } with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0x54]⟩ 0 Stack.empty 0
      (expectedTracker [((7, 3), 42), ((7, 3), 43), ((8, 3), 7)] [7] [(8, 3)]) [(7, 4), (8, 3)])
  | _ => false

-- With no clear, a missing key falls back to the parent's zero default.
#eval check <| match Frame.sload { frame with stack := ⟨[9, 11], by decide⟩, tracker := { tracker with writes := { tracker.writes with storageClears := [] } } } with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 ⟨[0, 11], by decide⟩ 0
      (expectedTracker [((7, 3), 42), ((7, 3), 43), ((8, 3), 7)] [] [(7, 9), (8, 3)]) [(7, 9), (7, 4), (8, 3)])
  | _ => false

-- Warm-slot opcode dispatch fails without changing the existing warm list.
#eval check <| match Frame.step { frame with code := ⟨#[0x54]⟩, pc := 0, gas := 99, warmSlots := [(7, 3), (7, 4), (7, 3), (8, 3)] } with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0x54]⟩ 0 ⟨[11], by decide⟩ 99
      (expectedTracker [((7, 3), 42), ((7, 3), 43), ((8, 3), 7)] [7] [(8, 3)]) [(7, 3), (7, 4), (7, 3), (8, 3)])
  | _ => false
