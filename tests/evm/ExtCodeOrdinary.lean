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

private def zeroRead : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩), (8, ⟨1, 99, 8⟩)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(7, some ⟨3, 42, 9⟩), (7, none)], [((7, 1), 2)], [(9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩,
    [0, 8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩

private def twiceRead : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩), (8, ⟨1, 99, 8⟩)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(7, some ⟨3, 42, 9⟩), (7, none)], [((7, 1), 2)], [(9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩,
    [7, 7, 8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩

private def initialMemory : Memory.Allocation.State :=
  Memory.Allocation.write Memory.Allocation.empty 2 [0xa1, 0xb2]

private theorem memoryValid : Memory.Allocation.Valid initialMemory :=
  Memory.Allocation.write_valid_for_frame _ _ _ (by intro a _; rfl)

private def frame : Frame.State :=
  ⟨⟨#[0xfe]⟩, 99, ⟨[7, 11], by decide⟩, 3000, initialMemory,
    memoryValid, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩, tracker, [41, 42], [(43, 44), (45, 46)], false, {}⟩

-- Expected memory and environment are written out independently of the operation.
private def expected (code : ByteArray) (pc : Nat) (stack : Stack) (gas : Nat)
    (tx : TransactionState.State) (warm : List World.Address) : Frame.State :=
  ⟨code, pc, stack, gas, ⟨[(2, 0xa1), (3, 0xb2)], 1⟩,
    (by change Memory.Allocation.Valid initialMemory; exact memoryValid),
    ⟨⟨#[4]⟩, ⟨7, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
      [25, 26], [27, 28], ⟨⟨11684671, by decide⟩⟩⟩⟩, ⟨#[6]⟩, tx, warm, [(43, 44), (45, 46)], false, {}⟩

-- Validity proofs are propositions; all data fields are compared exactly.
private def sameFrame (actual expected : Frame.State) : Bool :=
  decide (actual.code = expected.code ∧ actual.pc = expected.pc ∧
    actual.stack.val = expected.stack.val ∧ actual.gas = expected.gas ∧
    actual.memory = expected.memory ∧ actual.context = expected.context ∧
    actual.returnData = expected.returnData ∧ actual.tracker = expected.tracker ∧
    actual.warmAddresses = expected.warmAddresses ∧ actual.warmSlots = expected.warmSlots ∧
    actual.isStatic = expected.isStatic ∧ actual.stateGas = expected.stateGas)

private def check (ok : Bool) : IO Unit :=
  if ok then pure () else throw (IO.userError "BALANCE full-frame assertion failed")

-- Amsterdam charges a separate 100 gas for code reading.
#eval check <| match Frame.extCodeSize { frame with gas := 3100 } with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 ⟨[1, 11], by decide⟩ 0 trackerAfterRead [7, 41, 42])
  | _ => false
#eval check <| match Frame.extCodeSize { frame with gas := 200, warmAddresses := [7, 41, 7] } with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 ⟨[1, 11], by decide⟩ 0 trackerAfterRead [7, 41, 7])
  | _ => false
#eval check <| match Frame.extCodeSize { frame with gas := 3099 } with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfe]⟩ 99 ⟨[11], by decide⟩ 3099 tracker [7, 41, 42])
  | _ => false
#eval check <| match Frame.extCodeHash frame with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 ⟨[9, 11], by decide⟩ 0 trackerAfterRead [7, 41, 42])
  | _ => false
#eval check <| match Frame.extCodeHash { frame with gas := 100, warmAddresses := [7, 41, 7] } with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 ⟨[9, 11], by decide⟩ 0 trackerAfterRead [7, 41, 7])
  | _ => false
#eval check <| match Frame.extCodeHash { frame with gas := 2999 } with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfe]⟩ 99 ⟨[11], by decide⟩ 2999 tracker [7, 41, 42])
  | _ => false
#eval check <| match Frame.step { frame with code := ⟨#[0x3b]⟩, pc := 0, gas := 3100 } with
  | .continue t => sameFrame t (expected ⟨#[0x3b]⟩ 1 ⟨[1, 11], by decide⟩ 0 trackerAfterRead [7, 41, 42])
  | _ => false
#eval check <| match Frame.step { frame with code := ⟨#[0x3f]⟩, pc := 0 } with
  | .continue t => sameFrame t (expected ⟨#[0x3f]⟩ 1 ⟨[9, 11], by decide⟩ 0 trackerAfterRead [7, 41, 42])
  | _ => false

-- Missing nonempty code is a typed extension after the charged account read.
private def missingTracker : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩), (8, ⟨1, 99, 8⟩)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(7, some ⟨3, 42, 9⟩), (7, none)], [((7, 1), 2)], [], [8], [((7, 2), 3)]⟩,
    [8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩
private def missingRead : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩), (8, ⟨1, 99, 8⟩)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(7, some ⟨3, 42, 9⟩), (7, none)], [((7, 1), 2)], [], [8], [((7, 2), 3)]⟩,
    [7, 8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩
#eval check <| match Frame.extCodeSize { frame with tracker := missingTracker, gas := 3100 } with
  | .exception t .missingCode => sameFrame t (expected ⟨#[0xfe]⟩ 99 ⟨[11], by decide⟩ 0 missingRead [7, 41, 42])
  | _ => false
#eval check <| match Frame.step { frame with tracker := missingTracker, gas := 3100, code := ⟨#[0x3b]⟩, pc := 0 } with
  | .exception t .missingCode => sameFrame t (expected ⟨#[0x3b]⟩ 0 ⟨[11], by decide⟩ 0 missingRead [7, 41, 42])
  | _ => false
#eval check <| match Frame.extCodeHash { frame with tracker := { tracker with writes := { tracker.writes with accountWrites := [(7, none)] } } } with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 ⟨[0, 11], by decide⟩ 0 tombstoneRead [7, 41, 42])
  | _ => false
#eval check <| match Frame.extCodeSize { frame with gas := 3100, tracker := { tracker with writes := { tracker.writes with accountWrites := [] } } } with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 ⟨[1, 11], by decide⟩ 0 parentRead [7, 41, 42])
  | _ => false
#eval check <| match Frame.extCodeHash { frame with stack := Stack.empty, gas := 0 } with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xfe]⟩ 99 Stack.empty 0 tracker [41, 42])
  | _ => false
#eval check <| match Frame.extCodeSize { frame with stack := Stack.empty, gas := 0 } with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xfe]⟩ 99 Stack.empty 0 tracker [41, 42])
  | _ => false
-- A high word addresses the low 160 bits, without changing the source stack below it.
#eval check <| match Frame.extCodeHash { frame with stack := ⟨[2^200 + 7, 11], by decide⟩ } with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 ⟨[9, 11], by decide⟩ 0 trackerAfterRead [7, 41, 42])
  | _ => false

#eval check <| match Runner.run 4 { frame with code := ⟨#[0x3b, 0x50, 0x3f, 0x00]⟩, pc := 0, gas := 3202, stack := ⟨[7, 7, 11], by decide⟩ } with
  | .stopped t => sameFrame t (expected ⟨#[0x3b, 0x50, 0x3f, 0x00]⟩ 4 ⟨[9, 11], by decide⟩ 0 twiceRead [7, 41, 42])
  | _ => false
#eval check <| match Frame.step { frame with code := ⟨#[0x3b]⟩, pc := 0, gas := 3099 } with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0x3b]⟩ 0 ⟨[11], by decide⟩ 3099 tracker [7, 41, 42])
  | _ => false
#eval check <| match Frame.step { frame with code := ⟨#[0x3f]⟩, pc := 0, gas := 0, stack := Stack.empty } with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0x3f]⟩ 0 Stack.empty 0 tracker [41, 42])
  | _ => false

-- A delegation designator is observed as the account's own code bytes.
private def designator : ByteArray := ⟨#[0xef, 0x01, 0x00, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7]⟩
private def delegTracker : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩), (8, ⟨1, 99, 8⟩)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(7, some ⟨3, 42, 9⟩), (7, none)], [((7, 1), 2)], [(9, designator), (9, ⟨#[1]⟩)], [8], [((7, 2), 3)]⟩,
    [8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩
private def delegRead : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩), (8, ⟨1, 99, 8⟩)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(7, some ⟨3, 42, 9⟩), (7, none)], [((7, 1), 2)], [(9, designator), (9, ⟨#[1]⟩)], [8], [((7, 2), 3)]⟩,
    [7, 8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩
#eval check <| match Frame.step { frame with code := ⟨#[0x3b]⟩, pc := 0, gas := 3100, tracker := delegTracker } with
  | .continue t => sameFrame t (expected ⟨#[0x3b]⟩ 1 ⟨[23, 11], by decide⟩ 0 delegRead [7, 41, 42])
  | _ => false
#eval check <| match Frame.extCodeHash { frame with tracker := delegTracker } with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 ⟨[9, 11], by decide⟩ 0 delegRead [7, 41, 42])
  | _ => false
#eval check <| match Frame.step { frame with code := ⟨#[0x3b]⟩, pc := 0, gas := 0, stack := Stack.empty } with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0x3b]⟩ 0 Stack.empty 0 tracker [41, 42])
  | _ => false
#eval check <| match Frame.step { frame with code := ⟨#[0x3f]⟩, pc := 0, gas := 2999 } with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0x3f]⟩ 0 ⟨[11], by decide⟩ 2999 tracker [7, 41, 42])
  | _ => false
-- An absent account defaults to empty; a stored empty account has the same hash result.
#eval check <| match Frame.extCodeSize { frame with gas := 3100, tracker := { tracker with parent := {}, writes := { tracker.writes with accountWrites := [] } } } with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 ⟨[0, 11], by decide⟩ 0 absentRead [7, 41, 42])
  | _ => false
private def emptyTracker : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩), (8, ⟨1, 99, 8⟩)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(7, some ⟨0, 0, World.emptyCodeHash⟩)], [((7, 1), 2)], [(9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩,
    [8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩
private def emptyRead : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩), (8, ⟨1, 99, 8⟩)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(7, some ⟨0, 0, World.emptyCodeHash⟩)], [((7, 1), 2)], [(9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩,
    [7, 8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩
#eval check <| match Frame.extCodeHash { frame with tracker := emptyTracker } with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 ⟨[0, 11], by decide⟩ 0 emptyRead [7, 41, 42])
  | _ => false

-- Warm gas boundaries and account default branches also execute through dispatch.
#eval check <| match Frame.extCodeSize { frame with gas := 199, warmAddresses := [7, 41, 7] } with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfe]⟩ 99 ⟨[11], by decide⟩ 199 tracker [7, 41, 7])
  | _ => false
#eval check <| match Frame.step { frame with code := ⟨#[0x3b]⟩, pc := 0, gas := 199, warmAddresses := [7, 41, 7] } with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0x3b]⟩ 0 ⟨[11], by decide⟩ 199 tracker [7, 41, 7])
  | _ => false
#eval check <| match Frame.extCodeHash { frame with gas := 99, warmAddresses := [7, 41, 7] } with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfe]⟩ 99 ⟨[11], by decide⟩ 99 tracker [7, 41, 7])
  | _ => false
#eval check <| match Frame.step { frame with code := ⟨#[0x3f]⟩, pc := 0, gas := 99, warmAddresses := [7, 41, 7] } with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0x3f]⟩ 0 ⟨[11], by decide⟩ 99 tracker [7, 41, 7])
  | _ => false
#eval check <| match Frame.step { frame with code := ⟨#[0x3b]⟩, pc := 0, gas := 3100, tracker := emptyTracker } with
  | .continue t => sameFrame t (expected ⟨#[0x3b]⟩ 1 ⟨[0, 11], by decide⟩ 0 emptyRead [7, 41, 42])
  | _ => false
#eval check <| match Frame.step { frame with code := ⟨#[0x3f]⟩, pc := 0, tracker := { tracker with parent := {}, writes := { tracker.writes with accountWrites := [] } } } with
  | .continue t => sameFrame t (expected ⟨#[0x3f]⟩ 1 ⟨[0, 11], by decide⟩ 0 absentRead [7, 41, 42])
  | _ => false
#eval check <| match Frame.step { frame with code := ⟨#[0x3b]⟩, pc := 0, gas := 3100, tracker := { tracker with writes := { tracker.writes with accountWrites := [(7, none)] } } } with
  | .continue t => sameFrame t (expected ⟨#[0x3b]⟩ 1 ⟨[0, 11], by decide⟩ 0 tombstoneRead [7, 41, 42])
  | _ => false
#eval check <| match Frame.step { frame with code := ⟨#[0x3b]⟩, pc := 0, gas := 3100, tracker := { tracker with writes := { tracker.writes with accountWrites := [] } } } with
  | .continue t => sameFrame t (expected ⟨#[0x3b]⟩ 1 ⟨[1, 11], by decide⟩ 0 parentRead [7, 41, 42])
  | _ => false
