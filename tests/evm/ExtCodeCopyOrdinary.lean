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
    memoryValid, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩, tracker, [41, 42], [(43, 44), (45, 46)], false, ⟨123, 456, -9, 7, 8⟩⟩

-- Expected memory and environment are written out independently of the operation.
private def expected (code : ByteArray) (pc : Nat) (stack : Stack) (gas : Nat)
    (tx : TransactionState.State) (warm : List World.Address) : Frame.State :=
  ⟨code, pc, stack, gas, ⟨[(2, 0xa1), (3, 0xb2)], 1⟩,
    (by change Memory.Allocation.Valid initialMemory; exact memoryValid),
    ⟨⟨#[4]⟩, ⟨7, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
      [25, 26], [27, 28], ⟨⟨11684671, by decide⟩⟩⟩⟩, ⟨#[6]⟩, tx, warm, [(43, 44), (45, 46)], false, ⟨123, 456, -9, 7, 8⟩⟩

-- Validity proofs are propositions; all data fields are compared exactly.
private def sameFrame (actual expected : Frame.State) : Bool :=
  decide (actual.code = expected.code ∧ actual.pc = expected.pc ∧
    actual.stack.val = expected.stack.val ∧ actual.gas = expected.gas ∧
    actual.memory = expected.memory ∧ actual.context = expected.context ∧
    actual.returnData = expected.returnData ∧ actual.tracker = expected.tracker ∧
    actual.warmAddresses = expected.warmAddresses ∧ actual.warmSlots = expected.warmSlots ∧
    actual.isStatic = expected.isStatic ∧ actual.stateGas = expected.stateGas)

private def check (ok : Bool) : IO Unit :=
  if ok then pure () else throw (IO.userError "EXTCODECOPY full-frame assertion failed")

-- Cold access copies one code byte and zero-pads beyond the source.
private theorem copiedValid : Memory.Allocation.Valid ⟨[(2, 2), (3, 0), (4, 0), (2, 0xa1), (3, 0xb2)], 1⟩ := by
  change Memory.Allocation.Valid (Memory.Allocation.write initialMemory 2 [2, 0, 0])
  exact Memory.Allocation.write_valid_for_frame _ _ _ memoryValid
private def copyExpected (code : ByteArray) (pc : Nat) (gas : Nat) : Frame.State :=
  ⟨code, pc, ⟨[11], by decide⟩, gas, ⟨[(2, 2), (3, 0), (4, 0), (2, 0xa1), (3, 0xb2)], 1⟩,
    copiedValid, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩, trackerAfterRead, [7, 41, 42], [(43, 44), (45, 46)], false, ⟨123, 456, -9, 7, 8⟩⟩
#eval check <| match Frame.extCodeCopy { frame with stack := ⟨[7, 2, 0, 3, 11], by decide⟩, gas := 3103 } with
  | .continue t => sameFrame t (copyExpected ⟨#[0xfe]⟩ 100 0)
  | _ => false
#eval check <| match Frame.step { frame with code := ⟨#[0x3c]⟩, pc := 0, stack := ⟨[7, 2, 0, 3, 11], by decide⟩, gas := 3103 } with
  | .continue t => sameFrame t (copyExpected ⟨#[0x3c]⟩ 1 0)
  | _ => false
#eval check <| match Frame.extCodeCopy { frame with stack := ⟨[7, 2, 0, 3, 11], by decide⟩, gas := 3102 } with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfe]⟩ 99 ⟨[11], by decide⟩ 3102 tracker [7, 41, 42])
  | _ => false
#eval check <| match Frame.extCodeCopy { frame with stack := Stack.empty, gas := 0 } with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xfe]⟩ 99 Stack.empty 0 tracker [41, 42])
  | _ => false

-- Each failed pop retains all earlier pops and occurs before access or gas checks.
#eval check <| match Frame.extCodeCopy { frame with stack := ⟨[7], by decide⟩, gas := 0 } with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xfe]⟩ 99 Stack.empty 0 tracker [41, 42])
  | _ => false
#eval check <| match Frame.extCodeCopy { frame with stack := ⟨[7, 2], by decide⟩, gas := 0 } with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xfe]⟩ 99 Stack.empty 0 tracker [41, 42])
  | _ => false
#eval check <| match Frame.extCodeCopy { frame with stack := ⟨[7, 2, 0], by decide⟩, gas := 0 } with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xfe]⟩ 99 Stack.empty 0 tracker [41, 42])
  | _ => false
#eval check <| match Frame.step { frame with code := ⟨#[0x3c]⟩, pc := 0, stack := ⟨[7, 2], by decide⟩, gas := 0 } with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0x3c]⟩ 0 Stack.empty 0 tracker [41, 42])
  | _ => false
#eval check <| match Frame.step { frame with code := ⟨#[0x3c]⟩, pc := 0, stack := ⟨[7, 2, 0, 3, 11], by decide⟩, gas := 3102 } with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0x3c]⟩ 0 ⟨[11], by decide⟩ 3102 tracker [7, 41, 42])
  | _ => false
-- Zero length ignores huge offsets for allocation and still charges and reads the account.
#eval check <| match Frame.extCodeCopy { frame with stack := ⟨[7, 2^255, 2^255, 0, 11], by decide⟩, gas := 3100 } with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 ⟨[11], by decide⟩ 0 trackerAfterRead [7, 41, 42])
  | _ => false
private def missingTracker : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩), (8, ⟨1, 99, 8⟩)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(7, some ⟨3, 42, 9⟩), (7, none)], [((7, 1), 2)], [], [8], [((7, 2), 3)]⟩,
    [8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩
-- Missing code is not consulted when a huge range cannot be charged.
#eval check <| match Frame.extCodeCopy { frame with tracker := missingTracker, stack := ⟨[7, 2^255, 2^254, 2^255, 11], by decide⟩, gas := 1 } with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfe]⟩ 99 ⟨[11], by decide⟩ 1 missingTracker [7, 41, 42])
  | _ => false
#eval check <| match Frame.step { frame with tracker := missingTracker, code := ⟨#[0x3c]⟩, pc := 0, stack := ⟨[7, 2^255, 2^254, 2^255, 11], by decide⟩, gas := 1 } with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0x3c]⟩ 0 ⟨[11], by decide⟩ 1 missingTracker [7, 41, 42])
  | _ => false
private def missingRead : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩), (8, ⟨1, 99, 8⟩)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(7, some ⟨3, 42, 9⟩), (7, none)], [((7, 1), 2)], [], [8], [((7, 2), 3)]⟩,
    [7, 8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩
private theorem expandedValid : Memory.Allocation.Valid ⟨[(2, 0xa1), (3, 0xb2)], 2⟩ := by
  change Memory.Allocation.Valid (Memory.Allocation.expand initialMemory 33 1)
  exact Memory.Allocation.expand_valid_for_frame _ _ _ memoryValid
private def missingExpected (code : ByteArray) (pc : Nat) : Frame.State :=
  ⟨code, pc, ⟨[11], by decide⟩, 0, ⟨[(2, 0xa1), (3, 0xb2)], 2⟩, expandedValid,
    ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩, missingRead, [7, 41, 42], [(43, 44), (45, 46)], false, ⟨123, 456, -9, 7, 8⟩⟩
#eval check <| match Frame.extCodeCopy { frame with tracker := missingTracker, stack := ⟨[7, 33, 0, 1, 11], by decide⟩, gas := 3106 } with
  | .exception t .missingCode => sameFrame t (missingExpected ⟨#[0xfe]⟩ 99)
  | _ => false
#eval check <| match Frame.step { frame with tracker := missingTracker, code := ⟨#[0x3c]⟩, pc := 0, stack := ⟨[7, 33, 0, 1, 11], by decide⟩, gas := 3106 } with
  | .exception t .missingCode => sameFrame t (missingExpected ⟨#[0x3c]⟩ 0)
  | _ => false

-- The real runner queries code, copies 32 bytes and loads the resulting word.
private theorem mixedMemoryValid : Memory.Allocation.Valid ⟨[(0, 2), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0), (8, 0), (9, 0), (10, 0), (11, 0), (12, 0), (13, 0), (14, 0), (15, 0), (16, 0), (17, 0), (18, 0), (19, 0), (20, 0), (21, 0), (22, 0), (23, 0), (24, 0), (25, 0), (26, 0), (27, 0), (28, 0), (29, 0), (30, 0), (31, 0), (2, 0xa1), (3, 0xb2)], 1⟩ := by
  change Memory.Allocation.Valid (Memory.Allocation.write (Memory.Allocation.expand initialMemory 0 32) 0 ([2] ++ List.replicate 31 0))
  exact Memory.Allocation.write_valid_for_frame _ _ _ (Memory.Allocation.expand_valid_for_frame _ _ _ memoryValid)
private def mixedExpected : Frame.State :=
  ⟨⟨#[0x3f, 0x50, 0x3c, 0x51, 0x00]⟩, 5, ⟨[2 * 2^248, 11], by decide⟩, 0,
    ⟨[(0, 2), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0), (8, 0), (9, 0), (10, 0), (11, 0), (12, 0), (13, 0), (14, 0), (15, 0), (16, 0), (17, 0), (18, 0), (19, 0), (20, 0), (21, 0), (22, 0), (23, 0), (24, 0), (25, 0), (26, 0), (27, 0), (28, 0), (29, 0), (30, 0), (31, 0), (2, 0xa1), (3, 0xb2)], 1⟩, mixedMemoryValid,
    ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩, twiceRead, [7, 41, 42], [(43, 44), (45, 46)], false, ⟨123, 456, -9, 7, 8⟩⟩
#eval check <| match Runner.run 5 { frame with code := ⟨#[0x3f, 0x50, 0x3c, 0x51, 0x00]⟩, pc := 0, stack := ⟨[7, 7, 0, 0, 32, 0, 11], by decide⟩, gas := 3208 } with
  | .stopped t => sameFrame t mixedExpected
  | _ => false

#eval check <| match Frame.step { frame with code := ⟨#[0x3c]⟩, pc := 0, stack := Stack.empty, gas := 0 } with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0x3c]⟩ 0 Stack.empty 0 tracker [41, 42])
  | _ => false
#eval check <| match Frame.step { frame with code := ⟨#[0x3c]⟩, pc := 0, stack := ⟨[7], by decide⟩, gas := 0 } with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0x3c]⟩ 0 Stack.empty 0 tracker [41, 42])
  | _ => false
#eval check <| match Frame.step { frame with code := ⟨#[0x3c]⟩, pc := 0, stack := ⟨[7, 2, 0], by decide⟩, gas := 0 } with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0x3c]⟩ 0 Stack.empty 0 tracker [41, 42])
  | _ => false
#eval check <| match Frame.step { frame with code := ⟨#[0x3c]⟩, pc := 0, stack := ⟨[7, 2^255, 2^255, 0, 11], by decide⟩, gas := 3100 } with
  | .continue t => sameFrame t (expected ⟨#[0x3c]⟩ 1 ⟨[11], by decide⟩ 0 trackerAfterRead [7, 41, 42])
  | _ => false
private def warmExpected : Frame.State :=
  ⟨⟨#[0x3c]⟩, 1, ⟨[11], by decide⟩, 0, ⟨[(2, 2), (3, 0), (4, 0), (2, 0xa1), (3, 0xb2)], 1⟩,
    copiedValid, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩, trackerAfterRead, [7, 41, 7], [(43, 44), (45, 46)], false, ⟨123, 456, -9, 7, 8⟩⟩
#eval check <| match Frame.step { frame with code := ⟨#[0x3c]⟩, pc := 0, stack := ⟨[7, 2, 0, 3, 11], by decide⟩, gas := 203, warmAddresses := [7, 41, 7] } with
  | .continue t => sameFrame t warmExpected
  | _ => false
#eval check <| match Frame.extCodeCopy { frame with stack := ⟨[7, 2, 0, 3, 11], by decide⟩, gas := 202, warmAddresses := [7, 41, 7] } with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfe]⟩ 99 ⟨[11], by decide⟩ 202 tracker [7, 41, 7])
  | _ => false
private theorem zeroValid : Memory.Allocation.Valid ⟨[(2, 0), (3, 0), (4, 0), (2, 0xa1), (3, 0xb2)], 1⟩ := by
  change Memory.Allocation.Valid (Memory.Allocation.write initialMemory 2 [0, 0, 0])
  exact Memory.Allocation.write_valid_for_frame _ _ _ memoryValid
private def zeroExpected : Frame.State :=
  ⟨⟨#[0x3c]⟩, 1, ⟨[11], by decide⟩, 0, ⟨[(2, 0), (3, 0), (4, 0), (2, 0xa1), (3, 0xb2)], 1⟩,
    zeroValid, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩, trackerAfterRead, [7, 41, 42], [(43, 44), (45, 46)], false, ⟨123, 456, -9, 7, 8⟩⟩
#eval check <| match Frame.step { frame with code := ⟨#[0x3c]⟩, pc := 0, stack := ⟨[7, 2, 2^255, 3, 11], by decide⟩, gas := 3103 } with
  | .continue t => sameFrame t zeroExpected
  | _ => false

-- EXTCODECOPY reads the delegation designator itself, not its target's code.
private def designator : ByteArray := ⟨#[0xef, 0x01, 0x00, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7]⟩
private def delegTracker : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩), (8, ⟨1, 99, 8⟩)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(7, some ⟨3, 42, 9⟩), (7, none)], [((7, 1), 2)], [(9, designator), (9, ⟨#[1]⟩)], [8], [((7, 2), 3)]⟩,
    [8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩
private def delegRead : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩), (8, ⟨1, 99, 8⟩)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(7, some ⟨3, 42, 9⟩), (7, none)], [((7, 1), 2)], [(9, designator), (9, ⟨#[1]⟩)], [8], [((7, 2), 3)]⟩,
    [7, 8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩
private theorem delegValid : Memory.Allocation.Valid ⟨[(2, 0xef), (3, 1), (4, 0), (2, 0xa1), (3, 0xb2)], 1⟩ := by
  change Memory.Allocation.Valid (Memory.Allocation.write initialMemory 2 [0xef, 1, 0])
  exact Memory.Allocation.write_valid_for_frame _ _ _ memoryValid
private def delegExpected : Frame.State :=
  ⟨⟨#[0x3c]⟩, 1, ⟨[11], by decide⟩, 0, ⟨[(2, 0xef), (3, 1), (4, 0), (2, 0xa1), (3, 0xb2)], 1⟩,
    delegValid, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩, delegRead, [7, 41, 42], [(43, 44), (45, 46)], false, ⟨123, 456, -9, 7, 8⟩⟩
#eval check <| match Frame.step { frame with code := ⟨#[0x3c]⟩, pc := 0, stack := ⟨[7, 2, 0, 3, 11], by decide⟩, gas := 3103, tracker := delegTracker } with
  | .continue t => sameFrame t delegExpected
  | _ => false

private theorem parentCopyValid : Memory.Allocation.Valid ⟨[(2, 1), (3, 0), (4, 0), (2, 0xa1), (3, 0xb2)], 1⟩ := by
  change Memory.Allocation.Valid (Memory.Allocation.write initialMemory 2 [1, 0, 0])
  exact Memory.Allocation.write_valid_for_frame _ _ _ memoryValid
private def parentCopyExpected : Frame.State :=
  ⟨⟨#[0x3c]⟩, 1, ⟨[11], by decide⟩, 0, ⟨[(2, 1), (3, 0), (4, 0), (2, 0xa1), (3, 0xb2)], 1⟩,
    parentCopyValid, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩, parentRead, [7, 41, 42], [(43, 44), (45, 46)], false, ⟨123, 456, -9, 7, 8⟩⟩
#eval check <| match Frame.step { frame with code := ⟨#[0x3c]⟩, pc := 0, stack := ⟨[7, 2, 0, 3, 11], by decide⟩, gas := 3103, tracker := { tracker with writes := { tracker.writes with accountWrites := [] } } } with
  | .continue t => sameFrame t parentCopyExpected
  | _ => false
#eval check <| match Frame.step { frame with code := ⟨#[0x3c]⟩, pc := 0, stack := ⟨[7, 2, 0, 3, 11], by decide⟩, gas := 3103, tracker := { tracker with writes := { tracker.writes with accountWrites := [(7, none)] } } } with
  | .continue t => sameFrame t { zeroExpected with tracker := tombstoneRead }
  | _ => false
#eval check <| match Frame.step { frame with code := ⟨#[0x3c]⟩, pc := 0, stack := ⟨[7, 2, 0, 3, 11], by decide⟩, gas := 3103, tracker := { tracker with parent := {}, writes := { tracker.writes with accountWrites := [] } } } with
  | .continue t => sameFrame t { zeroExpected with tracker := absentRead }
  | _ => false

private def emptyTracker : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩), (8, ⟨1, 99, 8⟩)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(7, some ⟨0, 0, World.emptyCodeHash⟩)], [((7, 1), 2)], [(9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩,
    [8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩
private def emptyRead : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩), (8, ⟨1, 99, 8⟩)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(7, some ⟨0, 0, World.emptyCodeHash⟩)], [((7, 1), 2)], [(9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩,
    [7, 8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩
#eval check <| match Frame.step { frame with code := ⟨#[0x3c]⟩, pc := 0, stack := ⟨[7, 2, 0, 3, 11], by decide⟩, gas := 3103, tracker := emptyTracker } with
  | .continue t => sameFrame t { zeroExpected with tracker := emptyRead }
  | _ => false

-- Address masking does not truncate either memory or code offsets.
#eval check <| match Frame.step { frame with code := ⟨#[0x3c]⟩, pc := 0, stack := ⟨[2^200 + 7, 2, 0, 3, 11], by decide⟩, gas := 3103 } with
  | .continue t => sameFrame t (copyExpected ⟨#[0x3c]⟩ 1 0)
  | _ => false
-- Zero length still performs the code lookup after charging.
#eval check <| match Frame.extCodeCopy { frame with tracker := missingTracker, stack := ⟨[7, 2^255, 2^255, 0, 11], by decide⟩, gas := 3100 } with
  | .exception t .missingCode => sameFrame t (expected ⟨#[0xfe]⟩ 99 ⟨[11], by decide⟩ 0 missingRead [7, 41, 42])
  | _ => false
-- A successful write across the first 32-byte boundary expands memory once.
private theorem crossingValid : Memory.Allocation.Valid ⟨[(33, 2), (34, 0), (35, 0), (2, 0xa1), (3, 0xb2)], 2⟩ := by
  change Memory.Allocation.Valid (Memory.Allocation.write (Memory.Allocation.expand initialMemory 33 3) 33 [2, 0, 0])
  exact Memory.Allocation.write_valid_for_frame _ _ _ (Memory.Allocation.expand_valid_for_frame _ _ _ memoryValid)
private def crossingExpected : Frame.State :=
  ⟨⟨#[0x3c]⟩, 1, ⟨[11], by decide⟩, 0, ⟨[(33, 2), (34, 0), (35, 0), (2, 0xa1), (3, 0xb2)], 2⟩,
    crossingValid, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩, trackerAfterRead, [7, 41, 42], [(43, 44), (45, 46)], false, ⟨123, 456, -9, 7, 8⟩⟩
#eval check <| match Frame.step { frame with code := ⟨#[0x3c]⟩, pc := 0, stack := ⟨[7, 33, 0, 3, 11], by decide⟩, gas := 3106 } with
  | .continue t => sameFrame t crossingExpected
  | _ => false
