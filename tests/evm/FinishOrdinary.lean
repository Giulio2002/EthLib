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

private theorem expandedValid : Memory.Allocation.Valid ⟨[(2, 0xa1), (3, 0xb2)], 2⟩ := by
  change Memory.Allocation.Valid (Memory.Allocation.expand initialMemory 33 1)
  exact Memory.Allocation.expand_valid_for_frame _ _ _ memoryValid
private def expandedExpected (code : ByteArray) (pc : Nat) : Frame.State :=
  ⟨code, pc, ⟨[11], by decide⟩, 0, ⟨[(2, 0xa1), (3, 0xb2)], 2⟩, expandedValid,
    ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩, tracker, [41, 42], [(43, 44), (45, 46)], true,
    ⟨123, 456, -9, 7, 8⟩, [oldLog]⟩

-- return first helper.
#eval check <| match Frame.returnOp (fixture ⟨#[0xfe]⟩ 99 0 Stack.empty) with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog])
  | _ => false

-- return first dispatch.
#eval check <| match Frame.step (fixture ⟨#[0xf3]⟩ 0 0 Stack.empty) with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xf3]⟩ 0 0 Stack.empty [oldLog])
  | _ => false

-- return second helper.
#eval check <| match Frame.returnOp (fixture ⟨#[0xfe]⟩ 99 0 ⟨[2], by decide⟩) with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog])
  | _ => false

-- return second dispatch.
#eval check <| match Frame.step (fixture ⟨#[0xf3]⟩ 0 0 ⟨[2], by decide⟩) with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xf3]⟩ 0 0 Stack.empty [oldLog])
  | _ => false

-- return exact helper.
#eval check <| match Frame.returnOp (fixture ⟨#[0xfe]⟩ 99 3 ⟨[33, 1, 11], by decide⟩) with
  | .returned t output => sameFrame t { expandedExpected ⟨#[0xfe]⟩ 99 with isStatic := false } && decide (output = ⟨#[0]⟩)
  | _ => false

-- return exact dispatch.
#eval check <| match Frame.step (fixture ⟨#[0xf3]⟩ 0 3 ⟨[33, 1, 11], by decide⟩) with
  | .returned t output => sameFrame t { expandedExpected ⟨#[0xf3]⟩ 0 with isStatic := false } && decide (output = ⟨#[0]⟩)
  | _ => false

-- return short helper.
#eval check <| match Frame.returnOp (fixture ⟨#[0xfe]⟩ 99 2 ⟨[33, 1, 11], by decide⟩) with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfe]⟩ 99 2 ⟨[11], by decide⟩ [oldLog])
  | _ => false

-- return short dispatch.
#eval check <| match Frame.step (fixture ⟨#[0xf3]⟩ 0 2 ⟨[33, 1, 11], by decide⟩) with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xf3]⟩ 0 2 ⟨[11], by decide⟩ [oldLog])
  | _ => false

-- return hugeoffset helper.
#eval check <| match Frame.returnOp (fixture ⟨#[0xfe]⟩ 99 1 ⟨[2^255, 1, 11], by decide⟩) with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfe]⟩ 99 1 ⟨[11], by decide⟩ [oldLog])
  | _ => false

-- return hugeoffset dispatch.
#eval check <| match Frame.step (fixture ⟨#[0xf3]⟩ 0 1 ⟨[2^255, 1, 11], by decide⟩) with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xf3]⟩ 0 1 ⟨[11], by decide⟩ [oldLog])
  | _ => false

-- return hugelen helper.
#eval check <| match Frame.returnOp (fixture ⟨#[0xfe]⟩ 99 1 ⟨[1, 2^255, 11], by decide⟩) with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfe]⟩ 99 1 ⟨[11], by decide⟩ [oldLog])
  | _ => false

-- return hugelen dispatch.
#eval check <| match Frame.step (fixture ⟨#[0xf3]⟩ 0 1 ⟨[1, 2^255, 11], by decide⟩) with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xf3]⟩ 0 1 ⟨[11], by decide⟩ [oldLog])
  | _ => false

-- return zero helper.
#eval check <| match Frame.returnOp (fixture ⟨#[0xfe]⟩ 99 0 ⟨[2^255, 0, 11], by decide⟩) with
  | .returned t output => sameFrame t (expected ⟨#[0xfe]⟩ 99 0 ⟨[11], by decide⟩ [oldLog]) && decide (output = ⟨#[]⟩)
  | _ => false

-- return zero dispatch.
#eval check <| match Frame.step (fixture ⟨#[0xf3]⟩ 0 0 ⟨[2^255, 0, 11], by decide⟩) with
  | .returned t output => sameFrame t (expected ⟨#[0xf3]⟩ 0 0 ⟨[11], by decide⟩ [oldLog]) && decide (output = ⟨#[]⟩)
  | _ => false

-- return padding helper.
#eval check <| match Frame.returnOp (fixture ⟨#[0xfe]⟩ 99 3 ⟨[31, 3, 11], by decide⟩) with
  | .returned t output => sameFrame t { expandedExpected ⟨#[0xfe]⟩ 99 with isStatic := false } && decide (output = ⟨#[0, 0, 0]⟩)
  | _ => false

-- return padding dispatch.
#eval check <| match Frame.step (fixture ⟨#[0xf3]⟩ 0 3 ⟨[31, 3, 11], by decide⟩) with
  | .returned t output => sameFrame t { expandedExpected ⟨#[0xf3]⟩ 0 with isStatic := false } && decide (output = ⟨#[0, 0, 0]⟩)
  | _ => false

-- return static helper.
#eval check <| match Frame.returnOp { fixture ⟨#[0xfe]⟩ 99 0 ⟨[2, 2, 11], by decide⟩ with isStatic := true } with
  | .returned t output => sameFrame t { expected ⟨#[0xfe]⟩ 99 0 ⟨[11], by decide⟩ [oldLog] with isStatic := true } && decide (output = ⟨#[0xa1, 0xb2]⟩)
  | _ => false

-- return static dispatch.
#eval check <| match Frame.step { fixture ⟨#[0xf3]⟩ 0 0 ⟨[2, 2, 11], by decide⟩ with isStatic := true } with
  | .returned t output => sameFrame t { expected ⟨#[0xf3]⟩ 0 0 ⟨[11], by decide⟩ [oldLog] with isStatic := true } && decide (output = ⟨#[0xa1, 0xb2]⟩)
  | _ => false

-- revert first helper.
#eval check <| match Frame.revertOp (fixture ⟨#[0xfe]⟩ 99 0 Stack.empty) with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog])
  | _ => false

-- revert first dispatch.
#eval check <| match Frame.step (fixture ⟨#[0xfd]⟩ 0 0 Stack.empty) with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xfd]⟩ 0 0 Stack.empty [oldLog])
  | _ => false

-- revert second helper.
#eval check <| match Frame.revertOp (fixture ⟨#[0xfe]⟩ 99 0 ⟨[2], by decide⟩) with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog])
  | _ => false

-- revert second dispatch.
#eval check <| match Frame.step (fixture ⟨#[0xfd]⟩ 0 0 ⟨[2], by decide⟩) with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xfd]⟩ 0 0 Stack.empty [oldLog])
  | _ => false

-- revert exact helper.
#eval check <| match Frame.revertOp (fixture ⟨#[0xfe]⟩ 99 3 ⟨[33, 1, 11], by decide⟩) with
  | .revert t remaining output => sameFrame t { expandedExpected ⟨#[0xfe]⟩ 99 with isStatic := false } && decide (output = ⟨#[0]⟩) && decide (remaining = 0)
  | _ => false

-- revert exact dispatch.
#eval check <| match Frame.step (fixture ⟨#[0xfd]⟩ 0 3 ⟨[33, 1, 11], by decide⟩) with
  | .revert t remaining output => sameFrame t { expandedExpected ⟨#[0xfd]⟩ 0 with isStatic := false } && decide (output = ⟨#[0]⟩) && decide (remaining = 0)
  | _ => false

-- revert short helper.
#eval check <| match Frame.revertOp (fixture ⟨#[0xfe]⟩ 99 2 ⟨[33, 1, 11], by decide⟩) with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfe]⟩ 99 2 ⟨[11], by decide⟩ [oldLog])
  | _ => false

-- revert short dispatch.
#eval check <| match Frame.step (fixture ⟨#[0xfd]⟩ 0 2 ⟨[33, 1, 11], by decide⟩) with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfd]⟩ 0 2 ⟨[11], by decide⟩ [oldLog])
  | _ => false

-- revert hugeoffset helper.
#eval check <| match Frame.revertOp (fixture ⟨#[0xfe]⟩ 99 1 ⟨[2^255, 1, 11], by decide⟩) with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfe]⟩ 99 1 ⟨[11], by decide⟩ [oldLog])
  | _ => false

-- revert hugeoffset dispatch.
#eval check <| match Frame.step (fixture ⟨#[0xfd]⟩ 0 1 ⟨[2^255, 1, 11], by decide⟩) with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfd]⟩ 0 1 ⟨[11], by decide⟩ [oldLog])
  | _ => false

-- revert hugelen helper.
#eval check <| match Frame.revertOp (fixture ⟨#[0xfe]⟩ 99 1 ⟨[1, 2^255, 11], by decide⟩) with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfe]⟩ 99 1 ⟨[11], by decide⟩ [oldLog])
  | _ => false

-- revert hugelen dispatch.
#eval check <| match Frame.step (fixture ⟨#[0xfd]⟩ 0 1 ⟨[1, 2^255, 11], by decide⟩) with
  | .exception t .outOfGas => sameFrame t (expected ⟨#[0xfd]⟩ 0 1 ⟨[11], by decide⟩ [oldLog])
  | _ => false

-- revert zero helper.
#eval check <| match Frame.revertOp (fixture ⟨#[0xfe]⟩ 99 0 ⟨[2^255, 0, 11], by decide⟩) with
  | .revert t remaining output => sameFrame t (expected ⟨#[0xfe]⟩ 99 0 ⟨[11], by decide⟩ [oldLog]) && decide (output = ⟨#[]⟩) && decide (remaining = 0)
  | _ => false

-- revert zero dispatch.
#eval check <| match Frame.step (fixture ⟨#[0xfd]⟩ 0 0 ⟨[2^255, 0, 11], by decide⟩) with
  | .revert t remaining output => sameFrame t (expected ⟨#[0xfd]⟩ 0 0 ⟨[11], by decide⟩ [oldLog]) && decide (output = ⟨#[]⟩) && decide (remaining = 0)
  | _ => false

-- revert padding helper.
#eval check <| match Frame.revertOp (fixture ⟨#[0xfe]⟩ 99 3 ⟨[31, 3, 11], by decide⟩) with
  | .revert t remaining output => sameFrame t { expandedExpected ⟨#[0xfe]⟩ 99 with isStatic := false } && decide (output = ⟨#[0, 0, 0]⟩) && decide (remaining = 0)
  | _ => false

-- revert padding dispatch.
#eval check <| match Frame.step (fixture ⟨#[0xfd]⟩ 0 3 ⟨[31, 3, 11], by decide⟩) with
  | .revert t remaining output => sameFrame t { expandedExpected ⟨#[0xfd]⟩ 0 with isStatic := false } && decide (output = ⟨#[0, 0, 0]⟩) && decide (remaining = 0)
  | _ => false

-- revert static helper.
#eval check <| match Frame.revertOp { fixture ⟨#[0xfe]⟩ 99 0 ⟨[2, 2, 11], by decide⟩ with isStatic := true } with
  | .revert t remaining output => sameFrame t { expected ⟨#[0xfe]⟩ 99 0 ⟨[11], by decide⟩ [oldLog] with isStatic := true } && decide (output = ⟨#[0xa1, 0xb2]⟩) && decide (remaining = 0)
  | _ => false

-- revert static dispatch.
#eval check <| match Frame.step { fixture ⟨#[0xfd]⟩ 0 0 ⟨[2, 2, 11], by decide⟩ with isStatic := true } with
  | .revert t remaining output => sameFrame t { expected ⟨#[0xfd]⟩ 0 0 ⟨[11], by decide⟩ [oldLog] with isStatic := true } && decide (output = ⟨#[0xa1, 0xb2]⟩) && decide (remaining = 0)
  | _ => false

-- PC followed by RETURN or REVERT returns four bytes with nonzero gas remaining.
#eval check <| match Runner.run 2 (fixture ⟨#[0x58, 0xf3]⟩ 0 7 ⟨[4, 11], by decide⟩) with
  | .returned t output => sameFrame t (expected ⟨#[0x58, 0xf3]⟩ 1 5 ⟨[11], by decide⟩ [oldLog]) && decide (output = ⟨#[0, 0, 0xa1, 0xb2]⟩)
  | _ => false
#eval check <| match Runner.run 8 (fixture ⟨#[0x58, 0xf3]⟩ 0 7 ⟨[4, 11], by decide⟩) with
  | .returned t output => sameFrame t (expected ⟨#[0x58, 0xf3]⟩ 1 5 ⟨[11], by decide⟩ [oldLog]) && decide (output = ⟨#[0, 0, 0xa1, 0xb2]⟩)
  | _ => false
#eval check <| match Runner.run 2 (fixture ⟨#[0x58, 0xfd]⟩ 0 7 ⟨[4, 11], by decide⟩) with
  | .reverted t gas output => sameFrame t (expected ⟨#[0x58, 0xfd]⟩ 1 5 ⟨[11], by decide⟩ [oldLog]) && decide (gas = 5 ∧ output = ⟨#[0, 0, 0xa1, 0xb2]⟩)
  | _ => false
#eval check <| match Runner.run 8 (fixture ⟨#[0x58, 0xfd]⟩ 0 7 ⟨[4, 11], by decide⟩) with
  | .reverted t gas output => sameFrame t (expected ⟨#[0x58, 0xfd]⟩ 1 5 ⟨[11], by decide⟩ [oldLog]) && decide (gas = 5 ∧ output = ⟨#[0, 0, 0xa1, 0xb2]⟩)
  | _ => false
#eval check <| match Runner.run 0 (fixture ⟨#[0x58, 0xf3]⟩ 0 7 ⟨[4, 11], by decide⟩) with
  | .exhausted t => sameFrame t (expected ⟨#[0x58, 0xf3]⟩ 0 7 ⟨[4, 11], by decide⟩ [oldLog])
  | _ => false
#eval check <| match Runner.run 0 (fixture ⟨#[0x58, 0xfd]⟩ 0 7 ⟨[4, 11], by decide⟩) with
  | .exhausted t => sameFrame t (expected ⟨#[0x58, 0xfd]⟩ 0 7 ⟨[4, 11], by decide⟩ [oldLog])
  | _ => false

-- Underflow takes priority over gas even in a static frame.
#eval check <| match Frame.returnOp { fixture ⟨#[0xfe]⟩ 99 0 ⟨[2^255], by decide⟩ with isStatic := true } with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.step { fixture ⟨#[0xf3]⟩ 0 0 ⟨[2^255], by decide⟩ with isStatic := true } with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xf3]⟩ 0 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.revertOp { fixture ⟨#[0xfe]⟩ 99 0 ⟨[2^255], by decide⟩ with isStatic := true } with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xfe]⟩ 99 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
#eval check <| match Frame.step { fixture ⟨#[0xfd]⟩ 0 0 ⟨[2^255], by decide⟩ with isStatic := true } with
  | .exception t .stackUnderflow => sameFrame t { expected ⟨#[0xfd]⟩ 0 0 Stack.empty [oldLog] with isStatic := true }
  | _ => false
