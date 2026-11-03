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


private def child (terminal : UInt8) : Frame.State :=
  checkpointInput terminal
where
  checkpointInput (terminal : UInt8) : Frame.State :=
    ChildSettlement.checkpoint { fixture ⟨#[0x55, 0x5d, 0xa0, terminal]⟩ 0 1000000
      ⟨[3, 5, 2, 6, 2, 2, 2, 2], by decide⟩ with
        stateGas := ⟨123, 123, 0, 0, 0⟩, logs := [] }


private def committedTracker : TransactionState.State :=
  ⟨⟨[(7, parentAccount), (8, parentAccount)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(7, some account), (7, none)], [((7, 3), 5), ((7, 1), 2)], [(9, ⟨#[2]⟩)], [8], [((7, 2), 6)]⟩,
    [7, 8], [(7, 3), (8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩
private def revertedTracker : TransactionState.State :=
  ⟨⟨[(7, parentAccount), (8, parentAccount)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(7, some account), (7, none)], [((7, 1), 2)], [(9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩,
    [7, 8], [(7, 3), (8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩

-- A child with a fresh meter writes storage and transient storage, then emits a log.
-- RETURN commits the effects, and REVERT restores the checkpoint while retaining reads.
-- SSTORE uses 12100 execution gas and 97920 state gas; 97797 spills.
-- TSTORE costs 100 and LOG0 costs 391, leaving 889612 execution gas.
-- REVERT restores 97797 of spill before the parent recovers it.
#eval check <| match ChildSettlement.settle { fixture ⟨#[0]⟩ 9 100 ⟨[33, 44], by decide⟩ with isStatic := true, stateGas := ⟨0, 456, -9, 7, 8⟩ } (Runner.run 4 (child 0xf3)) with
  | .ok s => sameFrame s { expected ⟨#[0]⟩ 9 889712 ⟨[33, 44], by decide⟩
      [oldLog, ⟨7, [], ⟨#[0xa1, 0xb2]⟩⟩] with
      isStatic := true, tracker := committedTracker, returnData := ⟨#[0xa1, 0xb2]⟩,
      warmAddresses := [41, 42, 41, 42],
      warmSlots := [(7, 3), (43, 44), (45, 46), (43, 44), (45, 46)],
      stateGas := ⟨0, 456, -9, 97804, 8⟩ }
  | _ => false

#eval check <| match ChildSettlement.settle { fixture ⟨#[0]⟩ 9 100 ⟨[33, 44], by decide⟩ with isStatic := true, stateGas := ⟨0, 456, -9, 7, 8⟩ } (Runner.run 4 (child 0xfd)) with
  | .ok s => sameFrame s { expected ⟨#[0]⟩ 9 987509 ⟨[33, 44], by decide⟩ [oldLog] with
      isStatic := true, tracker := revertedTracker, returnData := ⟨#[0xa1, 0xb2]⟩,
      stateGas := ⟨123, 456, -9, 7, 8⟩ }
  | _ => false

#eval check <| match ChildSettlement.settle (fixture ⟨#[0]⟩ 9 100 ⟨[33, 44], by decide⟩) (Runner.run 0 (child 0xf3)) with
  | .error .toolingOutcome => true
  | _ => false

private def directChild : Frame.State :=
  ChildSettlement.checkpoint { fixture ⟨#[0xaa]⟩ 7 50 Stack.empty with
    stateGas := ⟨123, 456, -9, 7, 0⟩ }
private def caller : Frame.State := { fixture ⟨#[0]⟩ 9 100 ⟨[33, 44], by decide⟩ with isStatic := true }
private def successExpected (data : ByteArray) : Frame.State :=
  { expected ⟨#[0]⟩ 9 164 ⟨[33, 44], by decide⟩ [oldLog, oldLog] with
    isStatic := true, returnData := data, warmAddresses := [41, 42, 41, 42],
    warmSlots := [(43, 44), (45, 46), (43, 44), (45, 46)],
    stateGas := ⟨232, 456, -18, 0, 8⟩ }
private def failureExpected (gas : Nat) (data : ByteArray) : Frame.State :=
  { expected ⟨#[0]⟩ 9 gas ⟨[33, 44], by decide⟩ [oldLog] with
    isStatic := true, returnData := data, stateGas := ⟨579, 456, -9, 7, 8⟩ }

#eval check <| match ChildSettlement.settle caller (.stopped directChild) with
  | .ok s => sameFrame s (successExpected ⟨#[]⟩)
  | _ => false
#eval check <| match ChildSettlement.settle caller (.returned directChild ⟨#[99]⟩) with
  | .ok s => sameFrame s (successExpected ⟨#[99]⟩)
  | _ => false
#eval check <| match ChildSettlement.settle caller (.reverted directChild 40 ⟨#[99]⟩) with
  | .ok s => sameFrame s (failureExpected 147 ⟨#[99]⟩)
  | _ => false
#eval check <| match ChildSettlement.settle caller (.exception directChild .outOfGas) with
  | .ok s => sameFrame s (failureExpected 100 ⟨#[]⟩)
  | _ => false
#eval check <| match ChildSettlement.settle caller (.unsupported directChild .stop) with
  | .error .toolingOutcome => true
  | _ => false
#eval check <| match ChildSettlement.settle caller (.stopped { directChild with
    tracker := { directChild.tracker with snapshots := [] } }) with
  | .error .missingSnapshot => true
  | _ => false
#eval check <| match ChildSettlement.settle caller (.stopped { directChild with
    tracker := { directChild.tracker with snapshots := [] },
    stateGas := ⟨123, 456, -9, 7, 1⟩ }) with
  | .error .committedChildSpill => true
  | _ => false

#eval check <| match ChildSettlement.settle caller (.exception directChild .missingCode) with
  | .error .toolingOutcome => true
  | _ => false
#eval check <| match ChildSettlement.settle caller (.exception directChild .missingStorageAccount) with
  | .error .toolingOutcome => true
  | _ => false

-- Direct terminal incorporation has the same explicit full-frame observations.
#eval check <| match ChildSettlement.settleChild caller directChild true 50 ⟨#[]⟩ with
  | .ok s => sameFrame s (successExpected ⟨#[]⟩)
  | _ => false
#eval check <| match ChildSettlement.settleChild caller directChild true 50 ⟨#[99]⟩ with
  | .ok s => sameFrame s (successExpected ⟨#[99]⟩)
  | _ => false
#eval check <| match ChildSettlement.settleChild caller directChild false 47 ⟨#[99]⟩ with
  | .ok s => sameFrame s (failureExpected 147 ⟨#[99]⟩)
  | _ => false
#eval check <| match ChildSettlement.settleChild caller directChild false 0 ⟨#[]⟩ with
  | .ok s => sameFrame s (failureExpected 100 ⟨#[]⟩)
  | _ => false
#eval check <| match ChildSettlement.settleChild caller
    { directChild with tracker := { directChild.tracker with snapshots := [] } } true 50 ⟨#[]⟩ with
  | .error .missingSnapshot => true
  | _ => false
#eval check <| match ChildSettlement.settleChild caller
    { directChild with tracker := { directChild.tracker with snapshots := [] } } false 0 ⟨#[]⟩ with
  | .error .missingSnapshot => true
  | _ => false
#eval check <| match ChildSettlement.settleChild caller
    { directChild with tracker := { directChild.tracker with snapshots := [] }, stateGas := ⟨123, 456, -9, 7, 1⟩ } true 50 ⟨#[]⟩ with
  | .error .committedChildSpill => true
  | _ => false

-- Duplicate entries are retained as lists and their first entries remain observable.
private def duplicateWrites : TransactionState.Snapshot :=
  ⟨[(7, some account), (7, none), (8, some parentAccount)],
   [((7, 3), 5), ((7, 3), 6), ((8, 3), 9)],
   [(9, ⟨#[2]⟩), (9, ⟨#[3]⟩)], [8, 8, 9],
   [((7, 2), 3), ((7, 2), 4), ((8, 2), 5)]⟩
private def duplicateSaved : TransactionState.Snapshot :=
  ⟨[(8, none), (8, some account)], [((8, 4), 6), ((8, 4), 7)],
    [(10, ⟨#[3]⟩), (10, ⟨#[4]⟩)], [10, 10], [((8, 5), 7), ((8, 5), 8)]⟩
private def duplicateTracker : TransactionState.State :=
  ⟨⟨[(7, parentAccount), (7, account)], [((8, 3), 5), ((8, 3), 6)],
      [(8, ⟨#[1]⟩), (8, ⟨#[2]⟩)]⟩,
   duplicateWrites, [8, 8, 7], [(8, 3), (8, 3), (7, 3)], [9, 9, 8],
   [duplicateSaved, duplicateSaved]⟩
private def duplicateInitial : Frame.State :=
  { fixture ⟨#[0xaa]⟩ 7 50 Stack.empty with
    tracker := duplicateTracker,
    warmAddresses := [41, 41, 42], warmSlots := [(43, 44), (43, 44), (45, 46)],
    stateGas := ⟨123, 456, -9, 7, 0⟩ }
private def duplicateCheckpoint : Frame.State := ChildSettlement.checkpoint duplicateInitial

#eval check <| sameFrame duplicateCheckpoint
  { expected ⟨#[0xaa]⟩ 7 50 Stack.empty [oldLog] with
    tracker := { duplicateTracker with snapshots := [duplicateWrites, duplicateSaved, duplicateSaved] },
    warmAddresses := [41, 41, 42], warmSlots := [(43, 44), (43, 44), (45, 46)],
    stateGas := ⟨123, 456, -9, 7, 0⟩ }

#eval check <| match ChildSettlement.settle caller (.returned duplicateCheckpoint ⟨#[99]⟩) with
  | .ok s => sameFrame s { successExpected ⟨#[99]⟩ with
      tracker := duplicateTracker, warmAddresses := [41, 41, 42, 41, 42],
      warmSlots := [(43, 44), (43, 44), (45, 46), (43, 44), (45, 46)] }
  | _ => false

private def duplicateChanged : Frame.State :=
  { duplicateCheckpoint with tracker := { duplicateCheckpoint.tracker with
      writes := ⟨[(7, none), (7, some account)], [((7, 3), 11), ((7, 3), 12)],
        [(9, ⟨#[7]⟩), (9, ⟨#[8]⟩)], [7, 7], [((7, 2), 13), ((7, 2), 14)]⟩,
      accountReads := [7, 7, 8, 8, 7], storageReads := [(7, 3), (7, 3), (8, 3), (8, 3), (7, 3)],
      createdAccounts := [7, 9, 9, 8] } }

#eval check <| match ChildSettlement.settle caller (.reverted duplicateChanged 40 ⟨#[99]⟩) with
  | .ok s => sameFrame s { failureExpected 147 ⟨#[99]⟩ with
      tracker := { duplicateTracker with
        accountReads := [7, 7, 8, 8, 7],
        storageReads := [(7, 3), (7, 3), (8, 3), (8, 3), (7, 3)], createdAccounts := [7, 9, 9, 8] } }
  | _ => false

-- Nonzero committed spill takes priority over an empty checkpoint on failure too.
#eval check <| match ChildSettlement.settleChild caller
    { directChild with tracker := { directChild.tracker with snapshots := [] }, stateGas := ⟨123, 456, -9, 7, 1⟩ } false 0 ⟨#[]⟩ with
  | .error .committedChildSpill => true
  | _ => false
