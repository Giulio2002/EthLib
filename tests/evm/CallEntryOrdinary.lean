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


-- CALL now suspends after seven pops, retaining every non-stack field.
#eval check <| match Frame.step (fixture ⟨#[0xf1]⟩ 0 100 ⟨[1, 2, 3, 4, 5, 6, 7, 8], by decide⟩) with
  | .callRequest t r => sameFrame t (expected ⟨#[0xf1]⟩ 0 100 ⟨[8], by decide⟩ [oldLog]) &&
      decide (r.gas = 1 ∧ r.address = 2 ∧ r.value = 3 ∧ r.inputOffset = 4 ∧
        r.inputSize = 5 ∧ r.outputOffset = 6 ∧ r.outputSize = 7)
  | _ => false

-- A static value call fails after all seven pops.
#eval check <| match Frame.step { fixture ⟨#[0xf1]⟩ 0 100 ⟨[1, 2, 3, 4, 5, 6, 7, 8], by decide⟩ with isStatic := true } with
  | .exception t .writeInStaticContext => sameFrame t { expected ⟨#[0xf1]⟩ 0 100 ⟨[8], by decide⟩ [oldLog] with isStatic := true }
  | _ => false

-- The failed seventh pop leaves the diagnostic stack empty.
#eval check <| match Frame.step (fixture ⟨#[0xf1]⟩ 0 100 ⟨[1, 2, 3, 4, 5, 6], by decide⟩) with
  | .exception t .stackUnderflow => sameFrame t (expected ⟨#[0xf1]⟩ 0 100 Stack.empty [oldLog])
  | _ => false

-- Runner currently exposes the suspension as a tooling result.
#eval check <| match Runner.run 1 (fixture ⟨#[0xf1]⟩ 0 100 ⟨[1, 2, 3, 4, 5, 6, 7, 8], by decide⟩) with
  | .unsupported t .call => sameFrame t (expected ⟨#[0xf1]⟩ 0 100 ⟨[8], by decide⟩ [oldLog])
  | _ => false
