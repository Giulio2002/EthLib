import EthLib.EVM

open EthLib.EVM

deriving instance DecidableEq for World.State
deriving instance DecidableEq for TransactionState.Snapshot
deriving instance DecidableEq for TransactionState.State
deriving instance DecidableEq for BlobFee.Schedule
deriving instance DecidableEq for Environment.Context
deriving instance DecidableEq for CallData.Context
deriving instance DecidableEq for Frame.CallRequest

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



private def childCode (opcode : UInt8) : ByteArray := ⟨#[0x60, 42, 0x60, 0, 0x53, 0x60, 1, 0x60, 0, opcode]⟩
private def initialCall (code : ByteArray) : Frame.State :=
  let hash := World.codeHash code
  let tx : TransactionState.State := { tracker with writes := { tracker.writes with
    accountWrites := (32, some ⟨1, 1, hash⟩) :: tracker.writes.accountWrites,
    codeWrites := (hash, code) :: tracker.writes.codeWrites } }
  { fixture ⟨#[0xf1, 0x00]⟩ 0 10000 ⟨[5000, 32, 0, 0, 0, 8, 1], by decide⟩ with tracker := tx }


private def observedTracker (code : ByteArray) : TransactionState.State :=
  let hash := World.codeHash code
  ⟨⟨[(7, parentAccount), (8, parentAccount)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(32, some ⟨1, 1, hash⟩), (7, some account), (7, none)], [((7, 1), 2)],
      [(hash, code), (9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩,
    [7, 32, 32, 8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩

private theorem resultMemoryValid : Memory.Allocation.Valid ⟨[(8, 42), (2, 0xa1), (3, 0xb2)], 1⟩ := by
  change Memory.Allocation.Valid (Memory.Allocation.write initialMemory 8 [42])
  exact Memory.Allocation.write_valid_for_frame _ _ _ memoryValid

-- Exact source charges: 3000 cold access and 18 execution gas in the child.
-- A successful child repays 7 units of the parent's outstanding spill.
#eval check <| match NestedRunner.run 20 ⟨initialCall (childCode 0xf3), 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected ⟨#[0xf1, 0x00]⟩ 2 6989 ⟨[1], by decide⟩ [oldLog] with
      memory := ⟨[(8, 42), (2, 0xa1), (3, 0xb2)], 1⟩, memoryValid := resultMemoryValid,
      tracker := observedTracker (childCode 0xf3), returnData := ⟨#[42]⟩,
      warmAddresses := [32, 41, 42, 32, 41, 42], warmSlots := [(43, 44), (45, 46), (43, 44), (45, 46)],
      stateGas := ⟨116, 456, -9, 0, 8⟩ }
  | _ => false

-- REVERT returns the same bytes without merging child warmth or repaying parent spill.
#eval check <| match NestedRunner.run 20 ⟨initialCall (childCode 0xfd), 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected ⟨#[0xf1, 0x00]⟩ 2 6982 ⟨[0], by decide⟩ [oldLog] with
      memory := ⟨[(8, 42), (2, 0xa1), (3, 0xb2)], 1⟩, memoryValid := resultMemoryValid,
      tracker := observedTracker (childCode 0xfd), returnData := ⟨#[42]⟩,
      warmAddresses := [32, 41, 42], stateGas := ⟨123, 456, -9, 7, 8⟩ }
  | _ => false

-- An invalid child opcode burns the child grant and preserves the parent memory.
#eval check <| match NestedRunner.run 20 ⟨initialCall ⟨#[0xfe]⟩, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected ⟨#[0xf1, 0x00]⟩ 2 2000 ⟨[0], by decide⟩ [oldLog] with
      tracker := observedTracker ⟨#[0xfe]⟩, returnData := ⟨#[]⟩,
      warmAddresses := [32, 41, 42], stateGas := ⟨123, 456, -9, 7, 8⟩ }
  | _ => false

-- A child STOP resumes the parent and preserves the full child execution grant.
#eval check <| match NestedRunner.run 20 ⟨initialCall ⟨#[0x00]⟩, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected ⟨#[0xf1, 0x00]⟩ 2 7007 ⟨[1], by decide⟩ [oldLog] with
      tracker := observedTracker ⟨#[0x00]⟩, returnData := ⟨#[]⟩,
      warmAddresses := [32, 41, 42, 32, 41, 42], warmSlots := [(43, 44), (45, 46), (43, 44), (45, 46)],
      stateGas := ⟨116, 456, -9, 0, 8⟩ }
  | _ => false

private def transientRevertCode : ByteArray :=
  ⟨#[0x60, 6, 0x60, 2, 0x5d, 0x60, 42, 0x60, 0, 0x53, 0x60, 1, 0x60, 0, 0xfd]⟩
private def transientFaultCode : ByteArray := ⟨#[0x60, 6, 0x60, 2, 0x5d, 0xfe]⟩

-- A real transient write is rolled back after the child's REVERT.
#eval check <| match NestedRunner.run 30 ⟨initialCall transientRevertCode, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected ⟨#[0xf1, 0x00]⟩ 2 6876 ⟨[0], by decide⟩ [oldLog] with
      memory := ⟨[(8, 42), (2, 0xa1), (3, 0xb2)], 1⟩, memoryValid := resultMemoryValid,
      tracker := observedTracker transientRevertCode, returnData := ⟨#[42]⟩,
      warmAddresses := [32, 41, 42], stateGas := ⟨123, 456, -9, 7, 8⟩ }
  | _ => false

-- A transient write is also rolled back on an exceptional child halt.
#eval check <| match NestedRunner.run 30 ⟨initialCall transientFaultCode, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected ⟨#[0xf1, 0x00]⟩ 2 2000 ⟨[0], by decide⟩ [oldLog] with
      tracker := observedTracker transientFaultCode, returnData := ⟨#[]⟩,
      warmAddresses := [32, 41, 42], stateGas := ⟨123, 456, -9, 7, 8⟩ }
  | _ => false

-- At the depth limit the child is not entered and its grants return untouched.
#eval check <| match NestedRunner.run 10 ⟨initialCall ⟨#[0x00]⟩, 1024, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected ⟨#[0xf1, 0x00]⟩ 2 7000 ⟨[0], by decide⟩ [oldLog] with
      tracker := observedTracker ⟨#[0x00]⟩, returnData := ⟨#[]⟩,
      warmAddresses := [32, 41, 42], stateGas := ⟨123, 456, -9, 7, 8⟩ }
  | _ => false

-- Fuel exhaustion is a tooling boundary, not a successful child call.
#eval check <| match NestedRunner.run 1 ⟨initialCall ⟨#[0x00]⟩, 0, []⟩ with
  | .exhausted _ => true
  | _ => false

-- Precompiles are not interpreted as empty bytecode by the partial runner.
#eval check <| match NestedRunner.run 2 ⟨{ initialCall ⟨#[0x00]⟩ with
    stack := ⟨[5000, 1, 0, 0, 0, 8, 1], by decide⟩ }, 0, []⟩ with
  | .tooling _ .precompile => true
  | _ => false

-- Delegation remains an explicit unavailable operation.
private def delegationCode : ByteArray := ⟨#[0xef, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩
#eval check <| match NestedRunner.run 2 ⟨initialCall delegationCode, 0, []⟩ with
  | .tooling _ (.preparation .delegation) => true
  | _ => false

private def valueCall (code : ByteArray) : Frame.State :=
  { initialCall code with gas := 500000, stack := ⟨[5000, 32, 3, 0, 0, 8, 1], by decide⟩ }
private def absentValueCall : Frame.State :=
  { valueCall ⟨#[0]⟩ with tracker := { (valueCall ⟨#[0]⟩).tracker with
      writes := { (valueCall ⟨#[0]⟩).tracker.writes with
        accountWrites := (32, none) :: tracker.writes.accountWrites } } }
private def valueReads : List World.Address := [32, 32, 7, 7, 7, 32, 32, 32, 8]
private def valueTracker (code : ByteArray) (commit : Bool) : TransactionState.State :=
  let original := observedTracker code
  let hash := World.codeHash code
  { original with accountReads := valueReads, writes := { original.writes with accountWrites :=
      (if commit then [(32, some ⟨1, 4, hash⟩), (7, some ⟨3, 39, 9⟩),
        (32, some ⟨1, 1, hash⟩), (7, some account), (7, none)]
      else [(32, some ⟨1, 1, hash⟩), (7, some account), (7, none)]) } }
private def transferEvent : Frame.LogEntry :=
  ⟨⟨2^160 - 2, by decide⟩,
    [Frame.logTopic (World.codeHash "Transfer(address,address,uint256)".toUTF8),
     Frame.logTopic (Environment.addressWord 7), Frame.logTopic (Environment.addressWord 32)],
    (3 : Word).toBytesBE⟩

-- Value transfer commits both balances and appends the EIP-7708 event on STOP.
#eval check <| match NestedRunner.run 20 ⟨valueCall ⟨#[0]⟩, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected ⟨#[0xf1, 0x00]⟩ 2 488007 ⟨[1], by decide⟩ [oldLog, transferEvent] with
      tracker := valueTracker ⟨#[0]⟩ true, returnData := ⟨#[]⟩,
      warmAddresses := [32, 41, 42, 32, 41, 42], warmSlots := [(43, 44), (45, 46), (43, 44), (45, 46)],
      stateGas := ⟨116, 456, -9, 0, 8⟩ }
  | _ => false

-- RETURN commits the transfer and copies the child's byte to the requested output.
#eval check <| match NestedRunner.run 20 ⟨valueCall (childCode 0xf3), 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected ⟨#[0xf1, 0x00]⟩ 2 487989 ⟨[1], by decide⟩ [oldLog, transferEvent] with
      memory := ⟨[(8, 42), (2, 0xa1), (3, 0xb2)], 1⟩, memoryValid := resultMemoryValid,
      tracker := valueTracker (childCode 0xf3) true, returnData := ⟨#[42]⟩,
      warmAddresses := [32, 41, 42, 32, 41, 42], warmSlots := [(43, 44), (45, 46), (43, 44), (45, 46)],
      stateGas := ⟨116, 456, -9, 0, 8⟩ }
  | _ => false

-- A REVERT retains transfer reads but rolls back both account writes and the event.
#eval check <| match NestedRunner.run 20 ⟨valueCall (childCode 0xfd), 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected ⟨#[0xf1, 0x00]⟩ 2 487982 ⟨[0], by decide⟩ [oldLog] with
      memory := ⟨[(8, 42), (2, 0xa1), (3, 0xb2)], 1⟩, memoryValid := resultMemoryValid,
      tracker := valueTracker (childCode 0xfd) false, returnData := ⟨#[42]⟩,
      warmAddresses := [32, 41, 42], stateGas := ⟨123, 456, -9, 7, 8⟩ }
  | _ => false

-- An exceptional child also rolls back the transfer, and burns the child grant.
#eval check <| match NestedRunner.run 20 ⟨valueCall ⟨#[0xfe]⟩, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected ⟨#[0xf1, 0x00]⟩ 2 480700 ⟨[0], by decide⟩ [oldLog] with
      tracker := valueTracker ⟨#[0xfe]⟩ false, returnData := ⟨#[]⟩,
      warmAddresses := [32, 41, 42], stateGas := ⟨123, 456, -9, 7, 8⟩ }
  | _ => false

private def absentObserved (commit : Bool) (reads : List World.Address) : TransactionState.State :=
  let original := (absentValueCall).tracker
  { original with accountReads := reads, writes := { original.writes with accountWrites :=
    (if commit then [(32, some ⟨0, 3, World.emptyCodeHash⟩), (7, some ⟨3, 39, 9⟩),
      (32, none), (7, some account), (7, none)]
    else [(32, none), (7, some account), (7, none)]) } }

-- A tombstoned target incurs the new-account state charge and receives the value.
#eval check <| match NestedRunner.run 20 ⟨absentValueCall, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected ⟨#[0xf1, 0x00]⟩ 2 304523 ⟨[1], by decide⟩ [oldLog, transferEvent] with
      tracker := absentObserved true valueReads, returnData := ⟨#[]⟩,
      warmAddresses := [32, 41, 42, 32, 41, 42], warmSlots := [(43, 44), (45, 46), (43, 44), (45, 46)],
      stateGas := ⟨0, 456, -9, 183484, 8⟩ }
  | _ => false

-- Insufficient funds and depth rejection restore the charged new-account state gas.
#eval check <| match NestedRunner.run 20 ⟨{ absentValueCall with stack := ⟨[5000, 32, 50, 0, 0, 8, 1], by decide⟩ }, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected ⟨#[0xf1, 0x00]⟩ 2 488007 ⟨[0], by decide⟩ [oldLog] with
      tracker := absentObserved false [7, 32, 32, 32, 8], returnData := ⟨#[]⟩,
      warmAddresses := [32, 41, 42], stateGas := ⟨116, 456, -9, 0, 8⟩ }
  | _ => false
#eval check <| match NestedRunner.run 20 ⟨absentValueCall, 1024, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected ⟨#[0xf1, 0x00]⟩ 2 488007 ⟨[0], by decide⟩ [oldLog] with
      tracker := absentObserved false [7, 32, 32, 32, 8], returnData := ⟨#[]⟩,
      warmAddresses := [32, 41, 42], stateGas := ⟨116, 456, -9, 0, 8⟩ }
  | _ => false

-- Execution gas is checked before warming or any account lookup, even with value.
#eval check <| match NestedRunner.run 4 ⟨{ absentValueCall with gas := 14299 }, 0, []⟩ with
  | .terminal (.exception s .outOfGas) => sameFrame s { absentValueCall with gas := 14299, stack := Stack.empty }
  | _ => false

-- A later new-account state-gas failure retains the access and account reads.
#eval check <| match NestedRunner.run 4 ⟨{ absentValueCall with gas := 14300 }, 0, []⟩ with
  | .terminal (.exception s .outOfGas) => sameFrame s { absentValueCall with
      gas := 0, stack := Stack.empty, warmAddresses := [32, 41, 42],
      tracker := { absentValueCall.tracker with accountReads := [32, 32, 32, 8] } }
  | _ => false

private def selfValueCall : Frame.State :=
  let hash := World.codeHash ⟨#[0]⟩
  let tx := { tracker with writes := { tracker.writes with
    accountWrites := [(50, some ⟨3, 42, hash⟩), (50, none)],
    codeWrites := [(hash, ⟨#[0]⟩), (9, ⟨#[2]⟩)] } }
  let f := fixture ⟨#[0xf1, 0]⟩ 0 500000 ⟨[5000, 50, 3, 0, 0, 8, 1], by decide⟩
  { f with tracker := tx, context := { f.context with environment := { f.context.environment with currentTarget := 50 } } }

-- A self-transfer performs both balance updates but emits no transfer event.
#eval check <| match NestedRunner.run 20 ⟨selfValueCall, 0, []⟩ with
  | .terminal (.stopped s) =>
    let hash := World.codeHash ⟨#[0]⟩
    let expectedTracker : TransactionState.State :=
      ⟨⟨[(7, parentAccount), (8, parentAccount)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
        ⟨[(50, some ⟨3, 42, hash⟩), (50, some ⟨3, 39, hash⟩),
          (50, some ⟨3, 42, hash⟩), (50, none)], [((7, 1), 2)],
          [(hash, ⟨#[0]⟩), (9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩,
        [50, 50, 50, 50, 50, 50, 50, 50, 8], [(8, 3)], [9],
        [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩
    let base := expected ⟨#[0xf1, 0]⟩ 2 488007 ⟨[1], by decide⟩ [oldLog]
    let targetContext := { base.context with environment := { base.context.environment with currentTarget := 50 } }
    sameFrame s { base with tracker := expectedTracker, returnData := ⟨#[]⟩, context := targetContext, warmAddresses := [50, 41, 42, 50, 41, 42], warmSlots := [(43, 44), (45, 46), (43, 44), (45, 46)], stateGas := ⟨116, 456, -9, 0, 8⟩ }
  | _ => false

private def emptyValueCall : Frame.State :=
  let tx := { tracker with writes := { tracker.writes with
    accountWrites := (32, some World.emptyAccount) :: tracker.writes.accountWrites } }
  { fixture ⟨#[0xf1, 0]⟩ 0 500000 ⟨[5000, 32, 3, 0, 0, 8, 1], by decide⟩ with tracker := tx }

-- An existing empty account incurs the same state charge as an absent account.
#eval check <| match NestedRunner.run 20 ⟨emptyValueCall, 0, []⟩ with
  | .terminal (.stopped s) =>
    let expectedTracker : TransactionState.State :=
      ⟨⟨[(7, parentAccount), (8, parentAccount)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
        ⟨[(32, some ⟨0, 3, World.emptyCodeHash⟩), (7, some ⟨3, 39, 9⟩),
          (32, some World.emptyAccount), (7, some account), (7, none)],
          [((7, 1), 2)], [(9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩,
        [32, 32, 7, 7, 7, 32, 32, 32, 8], [(8, 3)], [9],
        [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩
    sameFrame s { expected ⟨#[0xf1, 0]⟩ 2 304523 ⟨[1], by decide⟩ [oldLog, transferEvent] with
      tracker := expectedTracker, returnData := ⟨#[]⟩, warmAddresses := [32, 41, 42, 32, 41, 42],
      warmSlots := [(43, 44), (45, 46), (43, 44), (45, 46)], stateGas := ⟨0, 456, -9, 183484, 8⟩ }
  | _ => false

private def overflowValueCall : Frame.State :=
  let code : ByteArray := ⟨#[0]⟩
  let hash := World.codeHash code
  let tx := { tracker with writes := { tracker.writes with
    accountWrites := (32, some ⟨1, BitVec.allOnes 256, hash⟩) :: tracker.writes.accountWrites,
    codeWrites := (hash, code) :: tracker.writes.codeWrites } }
  { fixture ⟨#[0xf1, 0]⟩ 0 500000 ⟨[5000, 32, 3, 0, 0, 8, 1], by decide⟩ with tracker := tx }

-- Overflow is a tooling result after checkpoint and debit, not protocol success.
#eval check <| match NestedRunner.run 2 ⟨overflowValueCall, 0, []⟩ with
  | .tooling s (.transfer .recipientOverflow) =>
    let hash := World.codeHash ⟨#[0]⟩
    let originalWrites : TransactionState.Snapshot :=
      ⟨[(32, some ⟨1, BitVec.allOnes 256, hash⟩), (7, some account), (7, none)],
        [((7, 1), 2)], [(hash, ⟨#[0]⟩), (9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩
    let expectedTracker : TransactionState.State :=
      ⟨⟨[(7, parentAccount), (8, parentAccount)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
        ⟨[(7, some ⟨3, 39, 9⟩), (32, some ⟨1, BitVec.allOnes 256, hash⟩),
          (7, some account), (7, none)], [((7, 1), 2)],
          [(hash, ⟨#[0]⟩), (9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩,
        [32, 7, 7, 7, 32, 32, 32, 8], [(8, 3)], [9],
        [originalWrites, ⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩
    let expectedChild : Frame.State :=
      ⟨⟨#[0]⟩, 0, Stack.empty, 7300, Memory.Allocation.empty, (by intro a _; rfl),
        ⟨⟨#[]⟩, { env with currentTarget := 32, caller := 7, value := 3 }⟩, ⟨#[]⟩,
        expectedTracker, [32, 41, 42], [(43, 44), (45, 46)], false, ⟨123, 123, 0, 0, 0⟩, []⟩
    sameFrame s expectedChild
  | _ => false

-- Static protection wins over insufficient execution gas after operand popping.
#eval check <| match NestedRunner.run 4 ⟨{ absentValueCall with gas := 0, isStatic := true }, 0, []⟩ with
  | .terminal (.exception s .writeInStaticContext) =>
    sameFrame s { absentValueCall with gas := 0, stack := Stack.empty, isStatic := true }
  | _ => false

-- Initial execution-gas failure wins over both depth and insufficient balance.
#eval check <| match NestedRunner.run 4 ⟨{ absentValueCall with gas := 14299, stack := ⟨[5000, 32, 50, 0, 0, 8, 1], by decide⟩ }, 1024, []⟩ with
  | .terminal (.exception s .outOfGas) => sameFrame s { absentValueCall with gas := 14299, stack := Stack.empty }
  | _ => false

-- Total API case: a failed-new-account credit repays spill before the reservoir.
-- This checks the credit in isolation and does not assert a reachable child call.
#eval check <| sameFrame (NestedRunner.refundNewAccount (fixture ⟨#[0xf1, 0]⟩ 0 10000 ⟨[], by decide⟩) true)
  { expected ⟨#[0xf1, 0]⟩ 0 10007 ⟨[], by decide⟩ [oldLog] with stateGas := ⟨183716, 456, -9, 0, 8⟩ }

private def directRequest : Frame.CallRequest := ⟨5000, 32, 3, 0, 0, 8, 1⟩
private def zeroRequest : Frame.CallRequest := ⟨5000, 32, 0, 0, 0, 8, 1⟩

-- Direct preparation retains arbitrary code, PC, stack and all other fields on early gas failure.
#eval check <| match CallPreparation.prepare { absentValueCall with code := ⟨#[0xaa]⟩, pc := 19, gas := 14299 } directRequest with
  | .outOfGas s => sameFrame s { absentValueCall with code := ⟨#[0xaa]⟩, pc := 19, gas := 14299 }
  | _ => false

-- A missing code hash reports the target read and access warming before charging.
#eval check <| match CallPreparation.prepare { valueCall ⟨#[0]⟩ with tracker :=
    { tracker with writes := { tracker.writes with accountWrites := (32, some ⟨1, 1, 123⟩) :: tracker.writes.accountWrites } } } directRequest with
  | .tooling s .missingCode =>
    let expectedTracker : TransactionState.State :=
      ⟨⟨[(7, parentAccount), (8, parentAccount)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
        ⟨[(32, some ⟨1, 1, 123⟩), (7, some account), (7, none)], [((7, 1), 2)],
          [(9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩,
        [32, 8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩
    sameFrame s { expected ⟨#[0xf1, 0]⟩ 0 500000 ⟨[5000, 32, 3, 0, 0, 8, 1], by decide⟩ [oldLog] with
      tracker := expectedTracker, warmAddresses := [32, 41, 42] }
  | _ => false

-- Delegation is reported by preparation before execution gas is deducted.
#eval check <| match CallPreparation.prepare { initialCall delegationCode with gas := 500000 } zeroRequest with
  | .tooling s .delegation => sameFrame s { expected ⟨#[0xf1, 0]⟩ 0 500000 ⟨[5000, 32, 0, 0, 0, 8, 1], by decide⟩ [oldLog] with
      tracker := { (observedTracker delegationCode) with accountReads := [32, 8] }, warmAddresses := [32, 41, 42] }
  | _ => false

-- State-gas failure occurs after execution charge and three target reads.
#eval check <| match CallPreparation.prepare { absentValueCall with gas := 14300 } directRequest with
  | .outOfGas s => sameFrame s { absentValueCall with gas := 0, warmAddresses := [32, 41, 42], tracker :=
      { absentValueCall.tracker with accountReads := [32, 32, 32, 8] } }
  | _ => false

-- Successful preparation exposes the retained parent and both gas grants.
#eval check <| match CallPreparation.prepare (valueCall ⟨#[0]⟩) directRequest with
  | .ready p => sameFrame p.parent { expected ⟨#[0xf1, 0]⟩ 0 480700 ⟨[5000, 32, 3, 0, 0, 8, 1], by decide⟩ [oldLog] with
      tracker := { (observedTracker ⟨#[0]⟩) with accountReads := [7, 32, 32, 32, 8] },
      returnData := ⟨#[]⟩, warmAddresses := [32, 41, 42], stateGas := ⟨0, 456, -9, 7, 8⟩ } &&
      decide (p.request.gas = 5000 ∧ p.request.address = 32 ∧ p.request.value = 3 ∧
        p.request.inputOffset = 0 ∧ p.request.inputSize = 0 ∧ p.request.outputOffset = 8 ∧
        p.request.outputSize = 1 ∧ p.address = 32 ∧ p.code = ⟨#[0]⟩ ∧ p.childGas = 7300 ∧
        p.stateGrant = 123 ∧ p.newAccountCharged = false ∧ p.insufficientBalance = false)
  | _ => false

-- Preparation returns a request for a precompile address; the nested runner owns that boundary.
#eval check <| match CallPreparation.prepare (initialCall ⟨#[0]⟩) ⟨5000, 1, 0, 0, 0, 8, 1⟩ with
  | .ready p => sameFrame p.parent { expected ⟨#[0xf1, 0]⟩ 0 2000 ⟨[5000, 32, 0, 0, 0, 8, 1], by decide⟩ [oldLog] with
      tracker := { (observedTracker ⟨#[0]⟩) with accountReads := [7, 1, 1, 8] }, returnData := ⟨#[]⟩,
      warmAddresses := [1, 41, 42], stateGas := ⟨0, 456, -9, 7, 8⟩ } &&
      decide (p.request.gas = 5000 ∧ p.request.address = 1 ∧ p.request.value = 0 ∧
        p.request.inputOffset = 0 ∧ p.request.inputSize = 0 ∧ p.request.outputOffset = 8 ∧
        p.request.outputSize = 1 ∧ p.address = 1 ∧ p.code = ⟨#[]⟩ ∧ p.childGas = 5000 ∧
        p.stateGrant = 123 ∧ p.newAccountCharged = false ∧ p.insufficientBalance = false)
  | _ => false

private def directPrepared : CallPreparation.Prepared :=
  ⟨fixture ⟨#[0xaa]⟩ 9 10000 ⟨[99], by decide⟩, ⟨5000, 32, 0, 2, 2, 8, 1⟩,
    32, ⟨#[0]⟩, 5000, 123, false, false⟩

-- Direct zero-value entry reads the parent's two input bytes and saves all writes.
#eval check <| match NestedRunner.enterChild directPrepared with
  | .ok child =>
    let expectedChild : Frame.State :=
      ⟨⟨#[0]⟩, 0, Stack.empty, 5000, Memory.Allocation.empty, (by intro a _; rfl),
        ⟨⟨#[0xa1, 0xb2]⟩, { env with currentTarget := 32, caller := 7, value := 0 }⟩,
        ⟨#[]⟩, { tracker with snapshots := tracker.writes :: tracker.snapshots },
        [41, 42], [(43, 44), (45, 46)], false, ⟨123, 123, 0, 0, 0⟩, []⟩
    sameFrame child expectedChild
  | _ => false

private def directContinuation : NestedRunner.Continuation :=
  ⟨fixture ⟨#[0xaa]⟩ 5 10000 ⟨[99], by decide⟩, ⟨5000, 32, 3, 0, 0, 8, 1⟩, 4, false⟩
private def directChild : Frame.State :=
  { fixture ⟨#[0xbb]⟩ 7 321 ⟨[88], by decide⟩ with
    tracker := { tracker with snapshots := tracker.writes :: tracker.snapshots },
    stateGas := ⟨20, 21, 5, 2, 0⟩ }

-- Direct successful continuation merges child state and copies only one output byte.
#eval check <| match NestedRunner.resume directContinuation directChild true 100 ⟨#[42, 43]⟩ [] with
  | .next next => sameFrame next.frame { expected ⟨#[0xaa]⟩ 6 10109 ⟨[1, 99], by decide⟩ [oldLog, oldLog] with
      memory := ⟨[(8, 42), (2, 0xa1), (3, 0xb2)], 1⟩, memoryValid := resultMemoryValid,
      returnData := ⟨#[42, 43]⟩, warmAddresses := [41, 42, 41, 42],
      warmSlots := [(43, 44), (45, 46), (43, 44), (45, 46)], stateGas := ⟨134, 456, -4, 0, 8⟩ } &&
      decide (next.depth = 4 ∧ next.callers.length = 0)
  | _ => false

-- A simultaneous committed spill and missing snapshot reports the unmodified child.
#eval check <| match NestedRunner.resume directContinuation { directChild with
    tracker := { directChild.tracker with snapshots := [] }, stateGas := ⟨20, 21, 5, 2, 1⟩ } false 100 ⟨#[42]⟩ [] with
  | .done (.tooling diagnostic .invalidContinuation) =>
    sameFrame diagnostic { directChild with tracker := { directChild.tracker with snapshots := [] }, stateGas := ⟨20, 21, 5, 2, 1⟩ }
  | _ => false

-- Direct nonzero entry commits exact debit/credit histories inside the saved scope.
#eval check <| match NestedRunner.enterChild { directPrepared with request := { directPrepared.request with value := 3 } } with
  | .ok child =>
    let expectedTracker : TransactionState.State :=
      ⟨⟨[(7, parentAccount), (8, parentAccount)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
        ⟨[(32, some ⟨0, 3, World.emptyCodeHash⟩), (7, some ⟨3, 39, 9⟩), (7, some account), (7, none)],
          [((7, 1), 2)], [(9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩,
        [32, 32, 7, 7, 8], [(8, 3)], [9], tracker.writes :: tracker.snapshots⟩
    let expectedChild : Frame.State :=
      ⟨⟨#[0]⟩, 0, Stack.empty, 5000, Memory.Allocation.empty, (by intro a _; rfl),
        ⟨⟨#[0xa1, 0xb2]⟩, { env with currentTarget := 32, caller := 7, value := 3 }⟩,
        ⟨#[]⟩, expectedTracker, [41, 42], [(43, 44), (45, 46)], false, ⟨123, 123, 0, 0, 0⟩, [transferEvent]⟩
    sameFrame child expectedChild
  | _ => false

-- Direct failed continuation rolls back, retains output, and does not merge warmth or logs.
#eval check <| match NestedRunner.resume directContinuation directChild false 100 ⟨#[42, 43]⟩ [] with
  | .next next => sameFrame next.frame { expected ⟨#[0xaa]⟩ 6 10100 ⟨[0, 99], by decide⟩ [oldLog] with
      memory := ⟨[(8, 42), (2, 0xa1), (3, 0xb2)], 1⟩, memoryValid := resultMemoryValid,
      returnData := ⟨#[42, 43]⟩, stateGas := ⟨144, 456, -9, 7, 8⟩ } &&
      decide (next.depth = 4 ∧ next.callers.length = 0)
  | _ => false

-- Total continuation API case: credit after failure repays spill and fills the reservoir.
#eval check <| match NestedRunner.resume { directContinuation with newAccountCharged := true } directChild false 100 ⟨#[42, 43]⟩ [] with
  | .next next => sameFrame next.frame { expected ⟨#[0xaa]⟩ 6 10107 ⟨[0, 99], by decide⟩ [oldLog] with
      memory := ⟨[(8, 42), (2, 0xa1), (3, 0xb2)], 1⟩, memoryValid := resultMemoryValid,
      returnData := ⟨#[42, 43]⟩, stateGas := ⟨183737, 456, -9, 0, 8⟩ } &&
      decide (next.depth = 4 ∧ next.callers.length = 0)
  | _ => false

-- A full stack returns the credited frame without copying the output.
#eval check <| match NestedRunner.resume { directContinuation with parent := { directContinuation.parent with
    stack := ⟨List.replicate 1024 0, by simp only [List.length_replicate]; exact Nat.le_refl _⟩ } } directChild true 100 ⟨#[42, 43]⟩ [] with
  | .done (.tooling diagnostic .invalidContinuation) =>
    sameFrame diagnostic { expected ⟨#[0xaa]⟩ 5 10109 ⟨List.replicate 1024 0, by simp only [List.length_replicate]; exact Nat.le_refl _⟩ [oldLog, oldLog] with
      returnData := ⟨#[42, 43]⟩, warmAddresses := [41, 42, 41, 42],
      warmSlots := [(43, 44), (45, 46), (43, 44), (45, 46)], stateGas := ⟨134, 456, -4, 0, 8⟩ }
  | _ => false

-- A direct self-transfer performs the debit and credit without an event.
#eval check <| match NestedRunner.enterChild { directPrepared with address := 7, request := { directPrepared.request with value := 3 } } with
  | .ok child =>
    let expectedTracker : TransactionState.State :=
      ⟨⟨[(7, parentAccount), (8, parentAccount)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
        ⟨[(7, some account), (7, some ⟨3, 39, 9⟩), (7, some account), (7, none)],
          [((7, 1), 2)], [(9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩,
        [7, 7, 7, 7, 8], [(8, 3)], [9], tracker.writes :: tracker.snapshots⟩
    let expectedChild : Frame.State :=
      ⟨⟨#[0]⟩, 0, Stack.empty, 5000, Memory.Allocation.empty, (by intro a _; rfl),
        ⟨⟨#[0xa1, 0xb2]⟩, { env with currentTarget := 7, caller := 7, value := 3 }⟩,
        ⟨#[]⟩, expectedTracker, [41, 42], [(43, 44), (45, 46)], false, ⟨123, 123, 0, 0, 0⟩, []⟩
    sameFrame child expectedChild
  | _ => false

-- Insufficient direct entry returns the post-read checkpoint without changing writes.
#eval check <| match NestedRunner.enterChild { directPrepared with request := { directPrepared.request with value := 50 } } with
  | .error (.insufficientBalance, child) =>
    let expectedChild : Frame.State :=
      ⟨⟨#[0]⟩, 0, Stack.empty, 5000, Memory.Allocation.empty, (by intro a _; rfl),
        ⟨⟨#[0xa1, 0xb2]⟩, { env with currentTarget := 32, caller := 7, value := 50 }⟩,
        ⟨#[]⟩, { tracker with accountReads := [7, 8], snapshots := tracker.writes :: tracker.snapshots },
        [41, 42], [(43, 44), (45, 46)], false, ⟨123, 123, 0, 0, 0⟩, []⟩
    sameFrame child expectedChild
  | _ => false

-- Direct recipient overflow retains the debited account and the saved pre-transfer writes.
#eval check <| match NestedRunner.enterChild { directPrepared with parent := { directPrepared.parent with tracker := overflowValueCall.tracker }, request := { directPrepared.request with value := 3 } } with
  | .error (.recipientOverflow, child) =>
    let hash := World.codeHash ⟨#[0]⟩
    let originalWrites : TransactionState.Snapshot :=
      ⟨[(32, some ⟨1, BitVec.allOnes 256, hash⟩), (7, some account), (7, none)],
        [((7, 1), 2)], [(hash, ⟨#[0]⟩), (9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩
    let expectedTracker : TransactionState.State :=
      ⟨⟨[(7, parentAccount), (8, parentAccount)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
        ⟨[(7, some ⟨3, 39, 9⟩), (32, some ⟨1, BitVec.allOnes 256, hash⟩), (7, some account), (7, none)],
          [((7, 1), 2)], [(hash, ⟨#[0]⟩), (9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩,
        [32, 7, 7, 8], [(8, 3)], [9], originalWrites :: tracker.snapshots⟩
    let expectedChild : Frame.State :=
      ⟨⟨#[0]⟩, 0, Stack.empty, 5000, Memory.Allocation.empty, (by intro a _; rfl),
        ⟨⟨#[0xa1, 0xb2]⟩, { env with currentTarget := 32, caller := 7, value := 3 }⟩,
        ⟨#[]⟩, expectedTracker, [41, 42], [(43, 44), (45, 46)], false, ⟨123, 123, 0, 0, 0⟩, []⟩
    sameFrame child expectedChild
  | _ => false

-- A missing child snapshot reports the child diagnostic when committed spill is zero.
#eval check <| match NestedRunner.resume directContinuation { directChild with
    tracker := { directChild.tracker with snapshots := [] } } true 100 ⟨#[42]⟩ [] with
  | .done (.tooling diagnostic .invalidContinuation) =>
    sameFrame diagnostic { directChild with tracker := { directChild.tracker with snapshots := [] } }
  | _ => false

-- The exceptional-child wrapper burns child execution gas and resumes with empty output.
#eval check <| match NestedRunner.exceptional directChild .invalidOpcode [directContinuation] with
  | .next next => sameFrame next.frame { expected ⟨#[0xaa]⟩ 6 10000 ⟨[0, 99], by decide⟩ [oldLog] with
      returnData := ⟨#[]⟩, stateGas := ⟨144, 456, -9, 7, 8⟩ } &&
      decide (next.depth = 4 ∧ next.callers.length = 0)
  | _ => false

private def recursiveCode : ByteArray :=
  ⟨#[0x60, 0, 0x60, 0, 0x60, 0, 0x60, 0, 0x60, 0, 0x60, 33, 0x61, 19, 136, 0xf1, 0]⟩
private def recursiveInitial : Frame.State :=
  let s := initialCall recursiveCode
  let code : ByteArray := ⟨#[0]⟩
  let hash := World.codeHash code
  { s with tracker := { s.tracker with writes := { s.tracker.writes with accountWrites := (33, some ⟨1, 1, hash⟩) :: s.tracker.writes.accountWrites, codeWrites := (hash, code) :: s.tracker.writes.codeWrites } } }
private def recursiveTracker : TransactionState.State :=
  let hash := World.codeHash recursiveCode
  let stopHash := World.codeHash ⟨#[0]⟩
  ⟨⟨[(7, parentAccount), (8, parentAccount)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(33, some ⟨1, 1, stopHash⟩), (32, some ⟨1, 1, hash⟩), (7, some account), (7, none)],
      [((7, 1), 2)], [(stopHash, ⟨#[0]⟩), (hash, recursiveCode), (9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩,
    [32, 33, 33, 7, 32, 32, 8], [(8, 3)], [9],
    [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩
private def recursiveExpected : Frame.State :=
  { expected ⟨#[0xf1, 0]⟩ 2 3986 ⟨[1], by decide⟩ [oldLog] with
    tracker := recursiveTracker, returnData := ⟨#[]⟩,
    warmAddresses := [33, 32, 41, 42, 33, 32, 41, 42, 32, 41, 42],
    warmSlots := [(43, 44), (45, 46), (43, 44), (45, 46), (43, 44), (45, 46)],
    stateGas := ⟨116, 456, -9, 0, 8⟩ }

-- Two nested CALLs execute a grandchild STOP and return to the original parent.
#eval check <| match NestedRunner.run 60 ⟨recursiveInitial, 0, []⟩ with
  | .terminal (.stopped out) => sameFrame out recursiveExpected
  | _ => false

-- Fuel exhaustion at depth two retains both callers and resumes to the same full frame.
#eval check <| match NestedRunner.run 9 ⟨recursiveInitial, 0, []⟩ with
  | .exhausted machine =>
    let expectedGrandchild : Frame.State :=
      ⟨⟨#[0]⟩, 0, Stack.empty, 1949, Memory.Allocation.empty, (by intro a _; rfl),
        ⟨⟨#[]⟩, { env with currentTarget := 33, caller := 32, value := 0 }⟩, ⟨#[]⟩,
        { recursiveTracker with snapshots := recursiveTracker.writes :: recursiveTracker.writes :: recursiveTracker.snapshots },
        [33, 32, 41, 42], [(43, 44), (45, 46)], false, ⟨123, 123, 0, 0, 0⟩, []⟩
    let childParent : Frame.State :=
      ⟨recursiveCode, 15, Stack.empty, 30, Memory.Allocation.empty, (by intro a _; rfl),
        ⟨⟨#[]⟩, { env with currentTarget := 32, caller := 7, value := 0 }⟩, ⟨#[]⟩,
        { recursiveTracker with snapshots := recursiveTracker.writes :: recursiveTracker.snapshots },
        [33, 32, 41, 42], [(43, 44), (45, 46)], false, ⟨0, 123, 0, 0, 0⟩, []⟩
    let originalParent : Frame.State :=
      { expected ⟨#[0xf1, 0]⟩ 0 2000 Stack.empty [oldLog] with
        tracker := { recursiveTracker with accountReads := [7, 32, 32, 8] },
        returnData := ⟨#[]⟩, warmAddresses := [32, 41, 42], stateGas := ⟨0, 456, -9, 7, 8⟩ }
    sameFrame machine.frame expectedGrandchild && decide (machine.depth = 2) &&
      (match machine.callers with
      | [inner, outer] =>
        sameFrame inner.parent childParent && sameFrame outer.parent originalParent &&
        decide (inner.request = ⟨5000, 33, 0, 0, 0, 0, 0⟩ ∧ inner.depth = 1 ∧ inner.newAccountCharged = false ∧
          outer.request = ⟨5000, 32, 0, 0, 0, 8, 1⟩ ∧ outer.depth = 0 ∧ outer.newAccountCharged = false)
      | _ => false) &&
      match NestedRunner.run 51 machine with
      | .terminal (.stopped out) => sameFrame out recursiveExpected
      | _ => false
  | _ => false

-- Address 3 executes RIPEMD-160 with the Amsterdam precompile charge.
private def ripemdInitial (gas grant value inputSize : Nat) : Frame.State :=
  { fixture ⟨#[0xf1, 0]⟩ 0 gas ⟨[BitVec.ofNat 256 grant, 3, BitVec.ofNat 256 value, 0,
      BitVec.ofNat 256 inputSize, 8, 1], by simp⟩ with
    warmAddresses := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 256, 41, 42] }

private def ripemdEmpty : ByteArray :=
  ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x9c, 0x11, 0x85, 0xa5,
      0xc5, 0xe9, 0xfc, 0x54, 0x61, 0x28, 0x08, 0x97, 0x7e, 0xe8, 0xf5, 0x48,
      0xb2, 0x25, 0x8d, 0x31]⟩

private theorem zeroOutputMemoryValid : Memory.Allocation.Valid ⟨[(8, 0), (2, 0xa1), (3, 0xb2)], 1⟩ := by
  change Memory.Allocation.Valid (Memory.Allocation.write initialMemory 8 [0])
  exact Memory.Allocation.write_valid_for_frame _ _ _ memoryValid

-- Exact-gas success returns the known empty-input digest and copies its first byte.
#eval check <| match NestedRunner.run 3 ⟨ripemdInitial 10000 600 0 0, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected ⟨#[0xf1, 0]⟩ 2 9307 ⟨[1], by decide⟩ [oldLog] with
      memory := ⟨[(8, 0), (2, 0xa1), (3, 0xb2)], 1⟩, memoryValid := zeroOutputMemoryValid,
      tracker := { tracker with accountReads := [7, 3, 3, 8] }, returnData := ripemdEmpty,
      warmAddresses := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 256, 41, 42, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 256, 41, 42],
      warmSlots := [(43, 44), (45, 46), (43, 44), (45, 46)],
      stateGas := ⟨116, 456, -9, 0, 8⟩ }
  | _ => false

-- An insufficient precompile grant burns that child grant and leaves no return data.
#eval check <| match NestedRunner.run 3 ⟨ripemdInitial 10000 500 0 0, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected ⟨#[0xf1, 0]⟩ 2 9400 ⟨[0], by decide⟩ [oldLog] with
      tracker := { tracker with accountReads := [7, 3, 3, 8] }, returnData := ⟨#[]⟩,
      warmAddresses := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 256, 41, 42] }
  | _ => false

private theorem largeMemoryValid : Memory.Allocation.Valid ⟨[(2, 0xa1), (3, 0xb2)], 44⟩ := by
  intro a h
  have hsmall : initialMemory.words * 32 ≤ a := by
    change 32 ≤ a
    change 1408 ≤ a at h
    omega
  exact memoryValid a hsmall

-- A value call to the absent precompile pays the new-account charge.
-- The 1400-byte input costs 5880 gas, above the 2300 stipend.
-- The failed child rolls back its transfer and refunds the new-account charge.
#eval check <| match NestedRunner.run 3 ⟨ripemdInitial 500000 0 3 1400, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected ⟨#[0xf1, 0]⟩ 2 488475 ⟨[0], by decide⟩ [oldLog] with
      memory := ⟨[(2, 0xa1), (3, 0xb2)], 44⟩, memoryValid := largeMemoryValid,
      tracker := { tracker with accountReads := [3, 3, 7, 7, 7, 3, 3, 3, 8] },
      returnData := ⟨#[]⟩, warmAddresses := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 256, 41, 42],
      stateGas := ⟨116, 456, -9, 0, 8⟩ }
  | _ => false

private def ripemdTransferEvent : Frame.LogEntry :=
  ⟨⟨2^160 - 2, by decide⟩,
    [Frame.logTopic (World.codeHash "Transfer(address,address,uint256)".toUTF8),
     Frame.logTopic (Environment.addressWord 7), Frame.logTopic (Environment.addressWord 3)],
    (3 : Word).toBytesBE⟩

-- A successful value call creates the absent precompile account and commits its transfer.
#eval check <| match NestedRunner.run 3 ⟨ripemdInitial 500000 5000 3 0, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected ⟨#[0xf1, 0]⟩ 2 306823 ⟨[1], by decide⟩ [oldLog, ripemdTransferEvent] with
      memory := ⟨[(8, 0), (2, 0xa1), (3, 0xb2)], 1⟩, memoryValid := zeroOutputMemoryValid,
      tracker := { tracker with accountReads := [3, 3, 7, 7, 7, 3, 3, 3, 8], writes := { tracker.writes with
        accountWrites := [(3, some ⟨0, 3, World.emptyCodeHash⟩), (7, some ⟨3, 39, 9⟩), (7, some account), (7, none)] } },
      returnData := ripemdEmpty,
      warmAddresses := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 256, 41, 42, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 256, 41, 42],
      warmSlots := [(43, 44), (45, 46), (43, 44), (45, 46)], stateGas := ⟨0, 456, -9, 183484, 8⟩ }
  | _ => false
