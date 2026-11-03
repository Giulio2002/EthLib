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


private def initialMemory : Memory.Allocation.State :=
  Memory.Allocation.write Memory.Allocation.empty 2 [0xa1, 0xb2]
private theorem memoryValid : Memory.Allocation.Valid initialMemory :=
  Memory.Allocation.write_valid_for_frame _ _ _ (by intro a _; rfl)
private def oldLog : Frame.LogEntry := ⟨8, [⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9]⟩, by decide⟩], ⟨#[4, 5]⟩⟩
private def fixture (code : ByteArray) (pc gas : Nat) (stack : Stack) : Frame.State :=
  ⟨code, pc, stack, gas, initialMemory, memoryValid, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩, tracker,
    [41, 42], [(43, 44), (45, 46)], false, ⟨123, 456, -9, 7, 8⟩, [oldLog]⟩
private def expected (code : ByteArray) (pc gas : Nat) (stack : Stack)
    (logs : List Frame.LogEntry) : Frame.State :=
  ⟨code, pc, stack, gas, ⟨[(2, 0xa1), (3, 0xb2)], 1⟩,
    (by change Memory.Allocation.Valid initialMemory; exact memoryValid),
    ⟨⟨#[4]⟩, ⟨7, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
      [25, 26], [27, 28], ⟨⟨11684671, by decide⟩⟩⟩⟩, ⟨#[6]⟩, tracker,
    [41, 42], [(43, 44), (45, 46)], false, ⟨123, 456, -9, 7, 8⟩, logs⟩
private def sameFrame (a b : Frame.State) : Bool :=
  decide (a.code = b.code ∧ a.pc = b.pc ∧ a.stack.val = b.stack.val ∧ a.gas = b.gas ∧
    a.memory = b.memory ∧ a.context = b.context ∧ a.returnData = b.returnData ∧
    a.tracker = b.tracker ∧ a.warmAddresses = b.warmAddresses ∧ a.warmSlots = b.warmSlots ∧
    a.isStatic = b.isStatic ∧ a.stateGas = b.stateGas ∧ a.logs = b.logs)
private def check (ok : Bool) : IO Unit :=
  if ok then pure () else throw (IO.userError "LOG full-frame assertion failed")

#eval check <| match Frame.logN (fixture ⟨#[0xfe]⟩ 99 391 ⟨[2, 2, 11], by decide⟩) ⟨0, by decide⟩ with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [], ⟨#[0xa1, 0xb2]⟩⟩])
  | _ => false
#eval check <| match Frame.step (fixture ⟨#[0xa0]⟩ 0 391 ⟨[2, 2, 11], by decide⟩) with
  | .continue t => sameFrame t (expected ⟨#[0xa0]⟩ 1 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [], ⟨#[0xa1, 0xb2]⟩⟩])
  | _ => false

#eval check <| match Frame.logN (fixture ⟨#[0xfe]⟩ 99 766 ⟨[2, 2, 1, 11], by decide⟩) ⟨1, by decide⟩ with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩], ⟨#[0xa1, 0xb2]⟩⟩])
  | _ => false
#eval check <| match Frame.step (fixture ⟨#[0xa1]⟩ 0 766 ⟨[2, 2, 1, 11], by decide⟩) with
  | .continue t => sameFrame t (expected ⟨#[0xa1]⟩ 1 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩], ⟨#[0xa1, 0xb2]⟩⟩])
  | _ => false

#eval check <| match Frame.logN (fixture ⟨#[0xfe]⟩ 99 1141 ⟨[2, 2, 1, 2, 11], by decide⟩) ⟨2, by decide⟩ with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]⟩, by decide⟩], ⟨#[0xa1, 0xb2]⟩⟩])
  | _ => false
#eval check <| match Frame.step (fixture ⟨#[0xa2]⟩ 0 1141 ⟨[2, 2, 1, 2, 11], by decide⟩) with
  | .continue t => sameFrame t (expected ⟨#[0xa2]⟩ 1 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]⟩, by decide⟩], ⟨#[0xa1, 0xb2]⟩⟩])
  | _ => false

#eval check <| match Frame.logN (fixture ⟨#[0xfe]⟩ 99 1516 ⟨[2, 2, 1, 2, 3, 11], by decide⟩) ⟨3, by decide⟩ with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3]⟩, by decide⟩], ⟨#[0xa1, 0xb2]⟩⟩])
  | _ => false
#eval check <| match Frame.step (fixture ⟨#[0xa3]⟩ 0 1516 ⟨[2, 2, 1, 2, 3, 11], by decide⟩) with
  | .continue t => sameFrame t (expected ⟨#[0xa3]⟩ 1 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3]⟩, by decide⟩], ⟨#[0xa1, 0xb2]⟩⟩])
  | _ => false

#eval check <| match Frame.logN (fixture ⟨#[0xfe]⟩ 99 1891 ⟨[2, 2, 1, 2, 3, 4, 11], by decide⟩) ⟨4, by decide⟩ with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4]⟩, by decide⟩], ⟨#[0xa1, 0xb2]⟩⟩])
  | _ => false
#eval check <| match Frame.step (fixture ⟨#[0xa4]⟩ 0 1891 ⟨[2, 2, 1, 2, 3, 4, 11], by decide⟩) with
  | .continue t => sameFrame t (expected ⟨#[0xa4]⟩ 1 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4]⟩, by decide⟩], ⟨#[0xa1, 0xb2]⟩⟩])
  | _ => false

-- Missing topics take priority over static mode and gas.
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 0 ⟨[2, 2, 1, 2], by decide⟩ with isStatic := true } ⟨4, by decide⟩ with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.step { fixture ⟨#[0xa4]⟩ 0 0 ⟨[2, 2, 1, 2], by decide⟩ with isStatic := true } with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xa4]⟩ 0 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false

-- Insufficient gas takes priority over static mode and materializing huge ranges.
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 1 ⟨[2^255, 2^255, 11], by decide⟩ with isStatic := true } ⟨0, by decide⟩ with
  | .exception t .outOfGas => sameFrame t { expected ⟨#[0xfe]⟩ 99 1 ⟨[11], by decide⟩ [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.step { fixture ⟨#[0xa0]⟩ 0 1 ⟨[2^255, 2^255, 11], by decide⟩ with isStatic := true } with
  | .exception t .outOfGas => sameFrame t { expected ⟨#[0xa0]⟩ 0 1 ⟨[11], by decide⟩ [oldLog] with isStatic := true }
  | _ => false

-- A zero-size read ignores its large offset and still emits a log.
#eval check <| match Frame.logN (fixture ⟨#[0xfe]⟩ 99 375 ⟨[2^255, 0, 11], by decide⟩) ⟨0, by decide⟩ with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [], ⟨#[]⟩⟩])
  | _ => false
#eval check <| match Frame.step (fixture ⟨#[0xa0]⟩ 0 375 ⟨[2^255, 0, 11], by decide⟩) with
  | .continue t => sameFrame t (expected ⟨#[0xa0]⟩ 1 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [], ⟨#[]⟩⟩])
  | _ => false

-- Static protection is checked after charging.
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 391 ⟨[2, 2, 11], by decide⟩ with isStatic := true } ⟨0, by decide⟩ with
  | .exception t .writeInStaticContext => sameFrame t { expected ⟨#[0xfe]⟩ 99 0 ⟨[11], by decide⟩ [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.step { fixture ⟨#[0xa0]⟩ 0 391 ⟨[2, 2, 11], by decide⟩ with isStatic := true } with
  | .exception t .writeInStaticContext => sameFrame t { expected ⟨#[0xa0]⟩ 0 0 ⟨[11], by decide⟩ [oldLog] with isStatic := true }
  | _ => false

-- Two executions append in program order and keep the preexisting log.
#eval check <| match Runner.run 3 (fixture ⟨#[0xa0, 0xa0, 0x00]⟩ 0 782 ⟨[2, 2, 2, 2, 11], by decide⟩) with
  | .stopped t => sameFrame t (expected ⟨#[0xa0, 0xa0, 0x00]⟩ 3 0 ⟨[11], by decide⟩
      [oldLog, ⟨7, [], ⟨#[0xa1, 0xb2]⟩⟩, ⟨7, [], ⟨#[0xa1, 0xb2]⟩⟩])
  | _ => false

-- Each family member rejects a one-gas-short input before reading memory.
#eval check <| match Frame.logN (fixture ⟨#[0xfe]⟩ 99 390 ⟨[2, 2, 11], by decide⟩) ⟨0, by decide⟩ with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfe]⟩ 99 390 ⟨[11], by decide⟩ [oldLog])
  | _ => false
#eval check <| match Frame.step (fixture ⟨#[0xa0]⟩ 0 390 ⟨[2, 2, 11], by decide⟩) with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xa0]⟩ 0 390 ⟨[11], by decide⟩ [oldLog])
  | _ => false
#eval check <| match Frame.logN (fixture ⟨#[0xfe]⟩ 99 765 ⟨[2, 2, 1, 11], by decide⟩) ⟨1, by decide⟩ with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfe]⟩ 99 765 ⟨[11], by decide⟩ [oldLog])
  | _ => false
#eval check <| match Frame.step (fixture ⟨#[0xa1]⟩ 0 765 ⟨[2, 2, 1, 11], by decide⟩) with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xa1]⟩ 0 765 ⟨[11], by decide⟩ [oldLog])
  | _ => false
#eval check <| match Frame.logN (fixture ⟨#[0xfe]⟩ 99 1140 ⟨[2, 2, 1, 2, 11], by decide⟩) ⟨2, by decide⟩ with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfe]⟩ 99 1140 ⟨[11], by decide⟩ [oldLog])
  | _ => false
#eval check <| match Frame.step (fixture ⟨#[0xa2]⟩ 0 1140 ⟨[2, 2, 1, 2, 11], by decide⟩) with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xa2]⟩ 0 1140 ⟨[11], by decide⟩ [oldLog])
  | _ => false
#eval check <| match Frame.logN (fixture ⟨#[0xfe]⟩ 99 1515 ⟨[2, 2, 1, 2, 3, 11], by decide⟩) ⟨3, by decide⟩ with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfe]⟩ 99 1515 ⟨[11], by decide⟩ [oldLog])
  | _ => false
#eval check <| match Frame.step (fixture ⟨#[0xa3]⟩ 0 1515 ⟨[2, 2, 1, 2, 3, 11], by decide⟩) with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xa3]⟩ 0 1515 ⟨[11], by decide⟩ [oldLog])
  | _ => false
#eval check <| match Frame.logN (fixture ⟨#[0xfe]⟩ 99 1890 ⟨[2, 2, 1, 2, 3, 4, 11], by decide⟩) ⟨4, by decide⟩ with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfe]⟩ 99 1890 ⟨[11], by decide⟩ [oldLog])
  | _ => false
#eval check <| match Frame.step (fixture ⟨#[0xa4]⟩ 0 1890 ⟨[2, 2, 1, 2, 3, 4, 11], by decide⟩) with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xa4]⟩ 0 1890 ⟨[11], by decide⟩ [oldLog])
  | _ => false

-- Each nonzero topic count fails after consuming all available topics.
#eval check <| match Frame.logN (fixture ⟨#[0xfe]⟩ 99 0 ⟨[2, 2], by decide⟩) ⟨1, by decide⟩ with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog])
  | _ => false
#eval check <| match Frame.step (fixture ⟨#[0xa1]⟩ 0 0 ⟨[2, 2], by decide⟩) with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xa1]⟩ 0 0 Stack.empty [oldLog])
  | _ => false
#eval check <| match Frame.logN (fixture ⟨#[0xfe]⟩ 99 0 ⟨[2, 2, 1], by decide⟩) ⟨2, by decide⟩ with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog])
  | _ => false
#eval check <| match Frame.step (fixture ⟨#[0xa2]⟩ 0 0 ⟨[2, 2, 1], by decide⟩) with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xa2]⟩ 0 0 Stack.empty [oldLog])
  | _ => false
#eval check <| match Frame.logN (fixture ⟨#[0xfe]⟩ 99 0 ⟨[2, 2, 1, 2], by decide⟩) ⟨3, by decide⟩ with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog])
  | _ => false
#eval check <| match Frame.step (fixture ⟨#[0xa3]⟩ 0 0 ⟨[2, 2, 1, 2], by decide⟩) with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xa3]⟩ 0 0 Stack.empty [oldLog])
  | _ => false
#eval check <| match Frame.logN (fixture ⟨#[0xfe]⟩ 99 0 ⟨[2, 2, 1, 2, 3], by decide⟩) ⟨4, by decide⟩ with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog])
  | _ => false
#eval check <| match Frame.step (fixture ⟨#[0xa4]⟩ 0 0 ⟨[2, 2, 1, 2, 3], by decide⟩) with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xa4]⟩ 0 0 Stack.empty [oldLog])
  | _ => false

-- The static error retains memory expansion that occurs after charging.
private theorem expandedValid : Memory.Allocation.Valid ⟨[(2, 0xa1), (3, 0xb2)], 2⟩ := by
  change Memory.Allocation.Valid (Memory.Allocation.expand initialMemory 33 1)
  exact Memory.Allocation.expand_valid_for_frame _ _ _ memoryValid
private def expandedExpected (code : ByteArray) (pc : Nat) : Frame.State :=
  ⟨code, pc, ⟨[11], by decide⟩, 0, ⟨[(2, 0xa1), (3, 0xb2)], 2⟩, expandedValid,
    ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩, tracker, [41, 42], [(43, 44), (45, 46)], true,
    ⟨123, 456, -9, 7, 8⟩, [oldLog]⟩
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 386 ⟨[33, 1, 11], by decide⟩ with isStatic := true } ⟨0, by decide⟩ with
  | .exception t .writeInStaticContext => sameFrame t (expandedExpected ⟨#[0xfe]⟩ 99)
  | _ => false
#eval check <| match Frame.step { fixture ⟨#[0xa0]⟩ 0 386 ⟨[33, 1, 11], by decide⟩ with isStatic := true } with
  | .exception t .writeInStaticContext => sameFrame t (expandedExpected ⟨#[0xa0]⟩ 0)
  | _ => false

-- The first and second pops fail before gas and static checks.
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 0 Stack.empty with isStatic := true } ⟨0, by decide⟩ with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.step { fixture ⟨#[0xa0]⟩ 0 0 Stack.empty with isStatic := true } with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xa0]⟩ 0 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 0 ⟨[2], by decide⟩ with isStatic := true } ⟨0, by decide⟩ with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.step { fixture ⟨#[0xa0]⟩ 0 0 ⟨[2], by decide⟩ with isStatic := true } with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xa0]⟩ 0 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false

-- Every topic count observes the same first-pop, second-pop and static ordering.
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 0 Stack.empty with isStatic := true } ⟨1, by decide⟩ with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 0 ⟨[2], by decide⟩ with isStatic := true } ⟨1, by decide⟩ with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 766 ⟨[2, 2, 1, 11], by decide⟩ with isStatic := true } ⟨1, by decide⟩ with
  | .exception t .writeInStaticContext => sameFrame t { expected ⟨#[0xfe]⟩ 99 0 ⟨[11], by decide⟩ [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.step { fixture ⟨#[0xa1]⟩ 0 0 Stack.empty with isStatic := true } with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xa1]⟩ 0 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.step { fixture ⟨#[0xa1]⟩ 0 0 ⟨[2], by decide⟩ with isStatic := true } with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xa1]⟩ 0 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.step { fixture ⟨#[0xa1]⟩ 0 766 ⟨[2, 2, 1, 11], by decide⟩ with isStatic := true } with
  | .exception t .writeInStaticContext => sameFrame t { expected ⟨#[0xa1]⟩ 0 0 ⟨[11], by decide⟩ [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 0 Stack.empty with isStatic := true } ⟨2, by decide⟩ with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 0 ⟨[2], by decide⟩ with isStatic := true } ⟨2, by decide⟩ with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 1141 ⟨[2, 2, 1, 2, 11], by decide⟩ with isStatic := true } ⟨2, by decide⟩ with
  | .exception t .writeInStaticContext => sameFrame t { expected ⟨#[0xfe]⟩ 99 0 ⟨[11], by decide⟩ [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.step { fixture ⟨#[0xa2]⟩ 0 0 Stack.empty with isStatic := true } with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xa2]⟩ 0 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.step { fixture ⟨#[0xa2]⟩ 0 0 ⟨[2], by decide⟩ with isStatic := true } with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xa2]⟩ 0 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.step { fixture ⟨#[0xa2]⟩ 0 1141 ⟨[2, 2, 1, 2, 11], by decide⟩ with isStatic := true } with
  | .exception t .writeInStaticContext => sameFrame t { expected ⟨#[0xa2]⟩ 0 0 ⟨[11], by decide⟩ [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 0 Stack.empty with isStatic := true } ⟨3, by decide⟩ with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 0 ⟨[2], by decide⟩ with isStatic := true } ⟨3, by decide⟩ with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 1516 ⟨[2, 2, 1, 2, 3, 11], by decide⟩ with isStatic := true } ⟨3, by decide⟩ with
  | .exception t .writeInStaticContext => sameFrame t { expected ⟨#[0xfe]⟩ 99 0 ⟨[11], by decide⟩ [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.step { fixture ⟨#[0xa3]⟩ 0 0 Stack.empty with isStatic := true } with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xa3]⟩ 0 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.step { fixture ⟨#[0xa3]⟩ 0 0 ⟨[2], by decide⟩ with isStatic := true } with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xa3]⟩ 0 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.step { fixture ⟨#[0xa3]⟩ 0 1516 ⟨[2, 2, 1, 2, 3, 11], by decide⟩ with isStatic := true } with
  | .exception t .writeInStaticContext => sameFrame t { expected ⟨#[0xa3]⟩ 0 0 ⟨[11], by decide⟩ [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 0 Stack.empty with isStatic := true } ⟨4, by decide⟩ with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 0 ⟨[2], by decide⟩ with isStatic := true } ⟨4, by decide⟩ with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 1891 ⟨[2, 2, 1, 2, 3, 4, 11], by decide⟩ with isStatic := true } ⟨4, by decide⟩ with
  | .exception t .writeInStaticContext => sameFrame t { expected ⟨#[0xfe]⟩ 99 0 ⟨[11], by decide⟩ [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.step { fixture ⟨#[0xa4]⟩ 0 0 Stack.empty with isStatic := true } with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xa4]⟩ 0 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.step { fixture ⟨#[0xa4]⟩ 0 0 ⟨[2], by decide⟩ with isStatic := true } with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xa4]⟩ 0 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.step { fixture ⟨#[0xa4]⟩ 0 1891 ⟨[2, 2, 1, 2, 3, 4, 11], by decide⟩ with isStatic := true } with
  | .exception t .writeInStaticContext => sameFrame t { expected ⟨#[0xa4]⟩ 0 0 ⟨[11], by decide⟩ [oldLog] with isStatic := true }
  | _ => false

-- The high bit and low byte of a 256-bit topic both survive big-endian encoding.
#eval check <| match Frame.logN (fixture ⟨#[0xfe]⟩ 99 766 ⟨[2, 2, 2^255 + 1, 11], by decide⟩) ⟨1, by decide⟩ with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩], ⟨#[0xa1, 0xb2]⟩⟩])
  | _ => false
#eval check <| match Frame.step (fixture ⟨#[0xa1]⟩ 0 766 ⟨[2, 2, 2^255 + 1, 11], by decide⟩) with
  | .continue t => sameFrame t (expected ⟨#[0xa1]⟩ 1 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩], ⟨#[0xa1, 0xb2]⟩⟩])
  | _ => false

-- Per-opcode boundary regressions: all frames retain rich non-log state.

-- huge LOG1 helper.
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 1 ⟨[2^255, 2^255, 1, 11], by decide⟩ with isStatic := true } ⟨1, by decide⟩ with
  | .exception t .outOfGas => sameFrame t { expected ⟨#[0xfe]⟩ 99 1 ⟨[11], by decide⟩ [oldLog] with isStatic := true }
  | _ => false

-- huge LOG1 dispatch.
#eval check <| match Frame.step { fixture ⟨#[0xa1]⟩ 0 1 ⟨[2^255, 2^255, 1, 11], by decide⟩ with isStatic := true } with
  | .exception t .outOfGas => sameFrame t { expected ⟨#[0xa1]⟩ 0 1 ⟨[11], by decide⟩ [oldLog] with isStatic := true }
  | _ => false

-- huge LOG2 helper.
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 1 ⟨[2^255, 2^255, 1, 2, 11], by decide⟩ with isStatic := true } ⟨2, by decide⟩ with
  | .exception t .outOfGas => sameFrame t { expected ⟨#[0xfe]⟩ 99 1 ⟨[11], by decide⟩ [oldLog] with isStatic := true }
  | _ => false

-- huge LOG2 dispatch.
#eval check <| match Frame.step { fixture ⟨#[0xa2]⟩ 0 1 ⟨[2^255, 2^255, 1, 2, 11], by decide⟩ with isStatic := true } with
  | .exception t .outOfGas => sameFrame t { expected ⟨#[0xa2]⟩ 0 1 ⟨[11], by decide⟩ [oldLog] with isStatic := true }
  | _ => false

-- huge LOG3 helper.
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 1 ⟨[2^255, 2^255, 1, 2, 3, 11], by decide⟩ with isStatic := true } ⟨3, by decide⟩ with
  | .exception t .outOfGas => sameFrame t { expected ⟨#[0xfe]⟩ 99 1 ⟨[11], by decide⟩ [oldLog] with isStatic := true }
  | _ => false

-- huge LOG3 dispatch.
#eval check <| match Frame.step { fixture ⟨#[0xa3]⟩ 0 1 ⟨[2^255, 2^255, 1, 2, 3, 11], by decide⟩ with isStatic := true } with
  | .exception t .outOfGas => sameFrame t { expected ⟨#[0xa3]⟩ 0 1 ⟨[11], by decide⟩ [oldLog] with isStatic := true }
  | _ => false

-- huge LOG4 helper.
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 1 ⟨[2^255, 2^255, 1, 2, 3, 4, 11], by decide⟩ with isStatic := true } ⟨4, by decide⟩ with
  | .exception t .outOfGas => sameFrame t { expected ⟨#[0xfe]⟩ 99 1 ⟨[11], by decide⟩ [oldLog] with isStatic := true }
  | _ => false

-- huge LOG4 dispatch.
#eval check <| match Frame.step { fixture ⟨#[0xa4]⟩ 0 1 ⟨[2^255, 2^255, 1, 2, 3, 4, 11], by decide⟩ with isStatic := true } with
  | .exception t .outOfGas => sameFrame t { expected ⟨#[0xa4]⟩ 0 1 ⟨[11], by decide⟩ [oldLog] with isStatic := true }
  | _ => false

-- zero LOG1 helper.
#eval check <| match Frame.logN (fixture ⟨#[0xfe]⟩ 99 750 ⟨[2^255, 0, 1, 11], by decide⟩) ⟨1, by decide⟩ with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩], ⟨#[]⟩⟩])
  | _ => false

-- zero LOG1 dispatch.
#eval check <| match Frame.step (fixture ⟨#[0xa1]⟩ 0 750 ⟨[2^255, 0, 1, 11], by decide⟩) with
  | .continue t => sameFrame t (expected ⟨#[0xa1]⟩ 1 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩], ⟨#[]⟩⟩])
  | _ => false

-- zero LOG2 helper.
#eval check <| match Frame.logN (fixture ⟨#[0xfe]⟩ 99 1125 ⟨[2^255, 0, 1, 2, 11], by decide⟩) ⟨2, by decide⟩ with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]⟩, by decide⟩], ⟨#[]⟩⟩])
  | _ => false

-- zero LOG2 dispatch.
#eval check <| match Frame.step (fixture ⟨#[0xa2]⟩ 0 1125 ⟨[2^255, 0, 1, 2, 11], by decide⟩) with
  | .continue t => sameFrame t (expected ⟨#[0xa2]⟩ 1 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]⟩, by decide⟩], ⟨#[]⟩⟩])
  | _ => false

-- zero LOG3 helper.
#eval check <| match Frame.logN (fixture ⟨#[0xfe]⟩ 99 1500 ⟨[2^255, 0, 1, 2, 3, 11], by decide⟩) ⟨3, by decide⟩ with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3]⟩, by decide⟩], ⟨#[]⟩⟩])
  | _ => false

-- zero LOG3 dispatch.
#eval check <| match Frame.step (fixture ⟨#[0xa3]⟩ 0 1500 ⟨[2^255, 0, 1, 2, 3, 11], by decide⟩) with
  | .continue t => sameFrame t (expected ⟨#[0xa3]⟩ 1 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3]⟩, by decide⟩], ⟨#[]⟩⟩])
  | _ => false

-- zero LOG4 helper.
#eval check <| match Frame.logN (fixture ⟨#[0xfe]⟩ 99 1875 ⟨[2^255, 0, 1, 2, 3, 4, 11], by decide⟩) ⟨4, by decide⟩ with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4]⟩, by decide⟩], ⟨#[]⟩⟩])
  | _ => false

-- zero LOG4 dispatch.
#eval check <| match Frame.step (fixture ⟨#[0xa4]⟩ 0 1875 ⟨[2^255, 0, 1, 2, 3, 4, 11], by decide⟩) with
  | .continue t => sameFrame t (expected ⟨#[0xa4]⟩ 1 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3]⟩, by decide⟩, ⟨⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4]⟩, by decide⟩], ⟨#[]⟩⟩])
  | _ => false

-- high LOG2 helper.
#eval check <| match Frame.logN (fixture ⟨#[0xfe]⟩ 99 1141 ⟨[2, 2, 2^255 + 1, 2^255 + 2, 11], by decide⟩) ⟨2, by decide⟩ with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩, ⟨⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]⟩, by decide⟩], ⟨#[0xa1, 0xb2]⟩⟩])
  | _ => false

-- high LOG2 dispatch.
#eval check <| match Frame.step (fixture ⟨#[0xa2]⟩ 0 1141 ⟨[2, 2, 2^255 + 1, 2^255 + 2, 11], by decide⟩) with
  | .continue t => sameFrame t (expected ⟨#[0xa2]⟩ 1 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩, ⟨⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]⟩, by decide⟩], ⟨#[0xa1, 0xb2]⟩⟩])
  | _ => false

-- high LOG3 helper.
#eval check <| match Frame.logN (fixture ⟨#[0xfe]⟩ 99 1516 ⟨[2, 2, 2^255 + 1, 2^255 + 2, 2^255 + 3, 11], by decide⟩) ⟨3, by decide⟩ with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩, ⟨⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]⟩, by decide⟩, ⟨⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3]⟩, by decide⟩], ⟨#[0xa1, 0xb2]⟩⟩])
  | _ => false

-- high LOG3 dispatch.
#eval check <| match Frame.step (fixture ⟨#[0xa3]⟩ 0 1516 ⟨[2, 2, 2^255 + 1, 2^255 + 2, 2^255 + 3, 11], by decide⟩) with
  | .continue t => sameFrame t (expected ⟨#[0xa3]⟩ 1 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩, ⟨⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]⟩, by decide⟩, ⟨⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3]⟩, by decide⟩], ⟨#[0xa1, 0xb2]⟩⟩])
  | _ => false

-- high LOG4 helper.
#eval check <| match Frame.logN (fixture ⟨#[0xfe]⟩ 99 1891 ⟨[2, 2, 2^255 + 1, 2^255 + 2, 2^255 + 3, 2^255 + 4, 11], by decide⟩) ⟨4, by decide⟩ with
  | .continue t => sameFrame t (expected ⟨#[0xfe]⟩ 100 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩, ⟨⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]⟩, by decide⟩, ⟨⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3]⟩, by decide⟩, ⟨⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4]⟩, by decide⟩], ⟨#[0xa1, 0xb2]⟩⟩])
  | _ => false

-- high LOG4 dispatch.
#eval check <| match Frame.step (fixture ⟨#[0xa4]⟩ 0 1891 ⟨[2, 2, 2^255 + 1, 2^255 + 2, 2^255 + 3, 2^255 + 4, 11], by decide⟩) with
  | .continue t => sameFrame t (expected ⟨#[0xa4]⟩ 1 0 ⟨[11], by decide⟩ [oldLog, ⟨7, [⟨⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, by decide⟩, ⟨⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]⟩, by decide⟩, ⟨⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3]⟩, by decide⟩, ⟨⟨#[128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4]⟩, by decide⟩], ⟨#[0xa1, 0xb2]⟩⟩])
  | _ => false

-- missing LOG1 helper.
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 0 ⟨[2, 2], by decide⟩ with isStatic := true } ⟨1, by decide⟩ with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false

-- missing LOG1 dispatch.
#eval check <| match Frame.step { fixture ⟨#[0xa1]⟩ 0 0 ⟨[2, 2], by decide⟩ with isStatic := true } with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xa1]⟩ 0 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false

-- missing LOG2 helper.
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 0 ⟨[2, 2, 1], by decide⟩ with isStatic := true } ⟨2, by decide⟩ with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false

-- missing LOG2 dispatch.
#eval check <| match Frame.step { fixture ⟨#[0xa2]⟩ 0 0 ⟨[2, 2, 1], by decide⟩ with isStatic := true } with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xa2]⟩ 0 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false

-- missing LOG3 helper.
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 0 ⟨[2, 2, 1, 2], by decide⟩ with isStatic := true } ⟨3, by decide⟩ with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false

-- missing LOG3 dispatch.
#eval check <| match Frame.step { fixture ⟨#[0xa3]⟩ 0 0 ⟨[2, 2, 1, 2], by decide⟩ with isStatic := true } with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xa3]⟩ 0 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false

-- expand LOG1 helper.
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 761 ⟨[33, 1, 1, 11], by decide⟩ with isStatic := true } ⟨1, by decide⟩ with
  | .exception t .writeInStaticContext => sameFrame t (expandedExpected ⟨#[0xfe]⟩ 99)
  | _ => false

-- expand LOG1 dispatch.
#eval check <| match Frame.step { fixture ⟨#[0xa1]⟩ 0 761 ⟨[33, 1, 1, 11], by decide⟩ with isStatic := true } with
  | .exception t .writeInStaticContext => sameFrame t (expandedExpected ⟨#[0xa1]⟩ 0)
  | _ => false

-- expand LOG2 helper.
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 1136 ⟨[33, 1, 1, 2, 11], by decide⟩ with isStatic := true } ⟨2, by decide⟩ with
  | .exception t .writeInStaticContext => sameFrame t (expandedExpected ⟨#[0xfe]⟩ 99)
  | _ => false

-- expand LOG2 dispatch.
#eval check <| match Frame.step { fixture ⟨#[0xa2]⟩ 0 1136 ⟨[33, 1, 1, 2, 11], by decide⟩ with isStatic := true } with
  | .exception t .writeInStaticContext => sameFrame t (expandedExpected ⟨#[0xa2]⟩ 0)
  | _ => false

-- expand LOG3 helper.
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 1511 ⟨[33, 1, 1, 2, 3, 11], by decide⟩ with isStatic := true } ⟨3, by decide⟩ with
  | .exception t .writeInStaticContext => sameFrame t (expandedExpected ⟨#[0xfe]⟩ 99)
  | _ => false

-- expand LOG3 dispatch.
#eval check <| match Frame.step { fixture ⟨#[0xa3]⟩ 0 1511 ⟨[33, 1, 1, 2, 3, 11], by decide⟩ with isStatic := true } with
  | .exception t .writeInStaticContext => sameFrame t (expandedExpected ⟨#[0xa3]⟩ 0)
  | _ => false

-- expand LOG4 helper.
#eval check <| match Frame.logN { fixture ⟨#[0xfe]⟩ 99 1886 ⟨[33, 1, 1, 2, 3, 4, 11], by decide⟩ with isStatic := true } ⟨4, by decide⟩ with
  | .exception t .writeInStaticContext => sameFrame t (expandedExpected ⟨#[0xfe]⟩ 99)
  | _ => false

-- expand LOG4 dispatch.
#eval check <| match Frame.step { fixture ⟨#[0xa4]⟩ 0 1886 ⟨[33, 1, 1, 2, 3, 4, 11], by decide⟩ with isStatic := true } with
  | .exception t .writeInStaticContext => sameFrame t (expandedExpected ⟨#[0xa4]⟩ 0)
  | _ => false
