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

private def account : World.Account := ⟨3, 42, 9⟩
private def parentAccount : World.Account := ⟨1, 99, 8⟩
private def tracker : TransactionState.State :=
  ⟨⟨[(7, parentAccount), (8, parentAccount)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(7, some account), (7, none)], [((7, 1), 2)], [(9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩,
    [8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩

private def trackerAfterRead : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩), (8, ⟨1, 99, 8⟩)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(7, some ⟨3, 42, 9⟩), (7, none)], [((7, 1), 2)], [(9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩,
    [7, 8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩

private def tombstoneRead : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩), (8, ⟨1, 99, 8⟩)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(7, none)], [((7, 1), 2)], [(9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩,
    [7, 8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩

private def parentRead : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩), (8, ⟨1, 99, 8⟩)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[], [((7, 1), 2)], [(9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩,
    [7, 8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩

private def absentRead : TransactionState.State :=
  ⟨⟨[], [], []⟩,
    ⟨[], [((7, 1), 2)], [(9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩,
    [7, 8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩

private def initialMemory : Memory.Allocation.State :=
  Memory.Allocation.write Memory.Allocation.empty 2 [0xa1, 0xb2]

private theorem memoryValid : Memory.Allocation.Valid initialMemory :=
  Memory.Allocation.write_valid_for_frame _ _ _ (by intro a _; rfl)

private def frame : Frame.State :=
  ⟨⟨#[0xfe]⟩, 99, ⟨[11], by decide⟩, 8, initialMemory,
    memoryValid, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩, tracker, [41, 42], [(43, 44), (45, 46)]⟩

-- Expected memory and environment are written out independently of the operation.
private def expected (code : ByteArray) (pc : Nat) (stack : Stack) (gas : Nat)
    (tx : TransactionState.State) : Frame.State :=
  ⟨code, pc, stack, gas, ⟨[(2, 0xa1), (3, 0xb2)], 1⟩,
    (by change Memory.Allocation.Valid initialMemory; exact memoryValid),
    ⟨⟨#[4]⟩, ⟨7, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
      [25, 26], [27, 28], ⟨⟨11684671, by decide⟩⟩⟩⟩, ⟨#[6]⟩, tx, [41, 42], [(43, 44), (45, 46)]⟩

-- Validity proofs are propositions; all data fields are compared exactly.
private def sameFrame (actual expected : Frame.State) : Bool :=
  decide (actual.code = expected.code ∧ actual.pc = expected.pc ∧
    actual.stack.val = expected.stack.val ∧ actual.gas = expected.gas ∧
    actual.memory = expected.memory ∧ actual.context = expected.context ∧
    actual.returnData = expected.returnData ∧ actual.tracker = expected.tracker ∧
    actual.warmAddresses = expected.warmAddresses ∧ actual.warmSlots = expected.warmSlots)

private def check (ok : Bool) : IO Unit :=
  if ok then pure () else throw (IO.userError "SELFBALANCE full-frame assertion failed")

private def fullStack : Stack :=
  ⟨List.replicate 1024 0, by simp only [List.length_replicate, Nat.le_refl]⟩

-- Direct helper with unrelated code and program counter.
#eval check <| match Frame.selfBalance frame with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 ⟨[42, 11], by decide⟩ 3 trackerAfterRead)
  | _ => false

-- Low gas with stack space also leaves the whole diagnostic frame unchanged.
#eval check <| match Frame.selfBalance { frame with gas := 4 } with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfe]⟩ 99 ⟨[11], by decide⟩ 4 tracker)
  | _ => false

-- Low gas takes priority over a full stack and leaves every field unchanged.
#eval check <| match Frame.selfBalance { frame with gas := 4, stack := fullStack } with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfe]⟩ 99 fullStack 4 tracker)
  | _ => false

-- The overflow diagnostic retains the account read and every other field.
#eval check <| match Frame.selfBalance { frame with gas := 5, stack := fullStack } with
  | .exception t .stackOverflow => sameFrame t (expected ⟨#[0xfe]⟩ 99 fullStack 5 trackerAfterRead)
  | _ => false

-- The actual mixed runner executes SELFBALANCE, PC and STOP.
#eval check <| match Runner.run 3 { frame with code := ⟨#[0x47, 0x58, 0x00]⟩, pc := 0 } with
  | .stopped t => sameFrame t (expected ⟨#[0x47, 0x58, 0x00]⟩ 3 ⟨[1, 42, 11], by decide⟩ 1 trackerAfterRead)
  | _ => false

-- Tombstones shadow the parent, an absent write falls back, and an absent account reads zero.
#eval check <| match Frame.selfBalance { frame with tracker := { tracker with writes := { tracker.writes with accountWrites := [(7, none)] } } } with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 ⟨[0, 11], by decide⟩ 3 tombstoneRead)
  | _ => false

#eval check <| match Frame.selfBalance { frame with tracker := { tracker with writes := { tracker.writes with accountWrites := [] } } } with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 ⟨[99, 11], by decide⟩ 3 parentRead)
  | _ => false

#eval check <| match Frame.selfBalance { frame with tracker := { tracker with parent := {}, writes := { tracker.writes with accountWrites := [] } } } with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 ⟨[0, 11], by decide⟩ 3 absentRead)
  | _ => false

-- PC leaves the full tracker and all other non-execution fields unchanged.
#eval check <| match Frame.step { frame with code := ⟨#[0x58]⟩, pc := 0 } with
  | .continue t => sameFrame t (expected ⟨#[0x58]⟩ 1 ⟨[0, 11], by decide⟩ 6 tracker)
  | _ => false

-- Dispatch preserves gas-first priority and records the read before overflow.
#eval check <| match Frame.step { frame with code := ⟨#[0x47]⟩, pc := 0, gas := 4, stack := fullStack } with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0x47]⟩ 0 fullStack 4 tracker)
  | _ => false

#eval check <| match Frame.step { frame with code := ⟨#[0x47]⟩, pc := 0, gas := 5, stack := fullStack } with
  | .exception t .stackOverflow => sameFrame t (expected ⟨#[0x47]⟩ 0 fullStack 5 trackerAfterRead)
  | _ => false

-- BALANCE and SELFBALANCE record account reads while retaining storage reads.
#eval check <| match Runner.run 3 { frame with code := ⟨#[0x31, 0x47, 0x00]⟩, pc := 0, gas := 3005, stack := ⟨[7, 11], by decide⟩ } with
  | .stopped t => sameFrame t
      { (expected ⟨#[0x31, 0x47, 0x00]⟩ 3 ⟨[42, 42, 11], by decide⟩ 0
        ⟨⟨[(7, ⟨1, 99, 8⟩), (8, ⟨1, 99, 8⟩)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
          ⟨[(7, some ⟨3, 42, 9⟩), (7, none)], [((7, 1), 2)], [(9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩,
          [7, 7, 8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩)
        with warmAddresses := [7, 41, 42] }
  | _ => false
