import EthLib.EVM

open EthLib.EVM

/-!
Known answers for STATICCALL through the nested runner.

Every expected value is worked out by hand from Amsterdam `vm/instructions/system.py` `staticcall` and `generic_call`.
The parent pays 3000 for a cold callee and no memory expansion unless stated.
With 10000 gas and a 5000 request the child receives 5000 and the parent keeps 2000.
A successful child returns its gas and repays the parent's 7 units of outstanding spill from the reservoir.
-/

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

/-- The parent runs `STATICCALL; STOP`. -/
private def parentCode : ByteArray := ⟨#[0xfa, 0x00]⟩

private def fixture (gas : Nat) (stack : Stack) : Frame.State :=
  ⟨parentCode, 0, stack, gas, initialMemory, memoryValid, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩, tracker,
    [41, 42], [(43, 44), (45, 46)], false, ⟨123, 456, -9, 7, 8⟩, [oldLog]⟩
private def expected (pc gas : Nat) (stack : Stack) : Frame.State :=
  ⟨parentCode, pc, stack, gas, ⟨[(2, 0xa1), (3, 0xb2)], 1⟩,
    (by change Memory.Allocation.Valid initialMemory; exact memoryValid),
    ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩, tracker,
    [41, 42], [(43, 44), (45, 46)], false, ⟨123, 456, -9, 7, 8⟩, [oldLog]⟩
private def sameFrame (a b : Frame.State) : Bool :=
  decide (a.code = b.code ∧ a.pc = b.pc ∧ a.stack.val = b.stack.val ∧ a.gas = b.gas ∧
    a.memory = b.memory ∧ a.context = b.context ∧ a.returnData = b.returnData ∧
    a.tracker = b.tracker ∧ a.warmAddresses = b.warmAddresses ∧ a.warmSlots = b.warmSlots ∧
    a.isStatic = b.isStatic ∧ a.stateGas = b.stateGas ∧ a.logs = b.logs)
private def check (ok : Bool) : IO Unit :=
  if ok then pure () else throw (IO.userError "STATICCALL full-frame assertion failed")

/-- Install `code` at address 32 and call it with a 5000 request and a one-byte output at 8. -/
private def staticCall (code : ByteArray) : Frame.State :=
  let hash := World.codeHash code
  let tx : TransactionState.State := { tracker with writes := { tracker.writes with
    accountWrites := (32, some ⟨1, 1, hash⟩) :: tracker.writes.accountWrites,
    codeWrites := (hash, code) :: tracker.writes.codeWrites } }
  { fixture 10000 ⟨[5000, 32, 0, 0, 8, 1], by decide⟩ with tracker := tx }

/-- Two reads of the callee account and no sender read. -/
private def observedTracker (code : ByteArray) : TransactionState.State :=
  let hash := World.codeHash code
  ⟨⟨[(7, parentAccount), (8, parentAccount)], [((8, 3), 5)], [(8, ⟨#[1]⟩)]⟩,
    ⟨[(32, some ⟨1, 1, hash⟩), (7, some account), (7, none)], [((7, 1), 2)],
      [(hash, code), (9, ⟨#[2]⟩)], [8], [((7, 2), 3)]⟩,
    [32, 32, 8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 6)], [(10, ⟨#[3]⟩)], [10], [((8, 5), 7)]⟩]⟩

private theorem resultMemoryValid : Memory.Allocation.Valid ⟨[(8, 42), (2, 0xa1), (3, 0xb2)], 1⟩ := by
  change Memory.Allocation.Valid (Memory.Allocation.write initialMemory 8 [42])
  exact Memory.Allocation.write_valid_for_frame _ _ _ memoryValid

/-- `PUSH1 42; PUSH1 0; MSTORE8; PUSH1 1; PUSH1 0; op`, which costs 18 gas before `op`. -/
private def childCode (opcode : UInt8) : ByteArray := ⟨#[0x60, 42, 0x60, 0, 0x53, 0x60, 1, 0x60, 0, opcode]⟩

-- RETURN: the child writes its own memory, which a static frame may do.
-- The parent keeps 2000 + (5000 - 18) + 7 = 6989 and copies the byte 42 to offset 8.
#eval check <| match NestedRunner.run 20 ⟨staticCall (childCode 0xf3), 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected 2 6989 ⟨[1], by decide⟩ with
      memory := ⟨[(8, 42), (2, 0xa1), (3, 0xb2)], 1⟩, memoryValid := resultMemoryValid,
      tracker := observedTracker (childCode 0xf3), returnData := ⟨#[42]⟩,
      warmAddresses := [32, 41, 42, 32, 41, 42], warmSlots := [(43, 44), (45, 46), (43, 44), (45, 46)],
      stateGas := ⟨116, 456, -9, 0, 8⟩ }
  | _ => false

-- REVERT: status 0, the output is still copied, and no warmth or spill repayment is merged.
-- The parent keeps 2000 + (5000 - 18) = 6982.
#eval check <| match NestedRunner.run 20 ⟨staticCall (childCode 0xfd), 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected 2 6982 ⟨[0], by decide⟩ with
      memory := ⟨[(8, 42), (2, 0xa1), (3, 0xb2)], 1⟩, memoryValid := resultMemoryValid,
      tracker := observedTracker (childCode 0xfd), returnData := ⟨#[42]⟩,
      warmAddresses := [32, 41, 42] }
  | _ => false

-- STOP: status 1 and the whole grant returns, 2000 + 5000 + 7 = 7007.
#eval check <| match NestedRunner.run 20 ⟨staticCall ⟨#[0x00]⟩, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected 2 7007 ⟨[1], by decide⟩ with
      tracker := observedTracker ⟨#[0x00]⟩, returnData := ⟨#[]⟩,
      warmAddresses := [32, 41, 42, 32, 41, 42], warmSlots := [(43, 44), (45, 46), (43, 44), (45, 46)],
      stateGas := ⟨116, 456, -9, 0, 8⟩ }
  | _ => false

/-- The tracker a child sees: the parent's tracker with its current writes saved. -/
private def checkpoint (t : TransactionState.State) : TransactionState.State :=
  { t with snapshots := t.writes :: t.snapshots }

/-- A STATICCALL child of the fixture parent at address `target`, before or during execution.

The input is empty, the caller is 7, the value is 0 and the static flag is set.
The child holds the whole 123 reservoir as both reservoir and baseline.
-/
private def child (code : ByteArray) (target : World.Address) (t : TransactionState.State)
    (warm : List World.Address) (pc gas : Nat) (stack : Stack) : Frame.State :=
  ⟨code, pc, stack, gas, Memory.Allocation.empty, (by intro a _; rfl),
    ⟨⟨#[]⟩, { env with currentTarget := target, caller := 7, value := 0 }⟩, ⟨#[]⟩,
    checkpoint t, warm, [(43, 44), (45, 46)], true, ⟨123, 123, 0, 0, 0⟩, []⟩

/-- The child of `staticCall code` at address 32. -/
private def calleeFrame (code : ByteArray) (pc gas : Nat) (stack : Stack) : Frame.State :=
  child code 32 (observedTracker code) [32, 41, 42] pc gas stack

/-- The suspended parent: 3000 and the 5000 grant withheld, reservoir drained, return data cleared. -/
private def preparedParent (t : TransactionState.State) (warm : List World.Address) : Frame.State :=
  { expected 0 2000 Stack.empty with
    tracker := t, returnData := ⟨#[]⟩, warmAddresses := warm, stateGas := ⟨0, 456, -9, 7, 8⟩ }

private def sameContinuation (c : NestedRunner.Continuation) (parent : Frame.State)
    (request : Frame.CallRequest) (depth : Nat) (charged : Bool) : Bool :=
  sameFrame c.parent parent && decide (c.request = request ∧ c.depth = depth ∧ c.newAccountCharged = charged)

/-- The only caller of a first-level child: the fixture parent with its source-order request. -/
private def outerCaller (c : NestedRunner.Continuation) (code : ByteArray) : Bool :=
  sameContinuation c (preparedParent (observedTracker code) [32, 41, 42]) ⟨5000, 32, 0, 0, 0, 8, 1⟩ 0 false

/-- An exceptional child burns its grant: the parent keeps 2000, pushes 0 and has empty return data. -/
private def failed (code : ByteArray) : Frame.State :=
  { expected 2 2000 ⟨[0], by decide⟩ with
    tracker := observedTracker code, returnData := ⟨#[]⟩, warmAddresses := [32, 41, 42] }

-- An invalid opcode is an ordinary exceptional halt.
#eval check <| match NestedRunner.run 20 ⟨staticCall ⟨#[0xfe]⟩, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s (failed ⟨#[0xfe]⟩)
  | _ => false

-- The static child rejects SSTORE: `PUSH1 1; PUSH1 0; SSTORE`.
private def sstoreCode : ByteArray := ⟨#[0x60, 1, 0x60, 0, 0x55]⟩
#eval check <| match NestedRunner.run 20 ⟨staticCall sstoreCode, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s (failed sstoreCode)
  | _ => false

-- The static child rejects TSTORE: `PUSH1 6; PUSH1 2; TSTORE`.
private def tstoreCode : ByteArray := ⟨#[0x60, 6, 0x60, 2, 0x5d]⟩
#eval check <| match NestedRunner.run 20 ⟨staticCall tstoreCode, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s (failed tstoreCode)
  | _ => false

-- The static child rejects LOG0: `PUSH1 0; PUSH1 0; LOG0`.
private def logCode : ByteArray := ⟨#[0x60, 0, 0x60, 0, 0xa0]⟩
#eval check <| match NestedRunner.run 20 ⟨staticCall logCode, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s (failed logCode)
  | _ => false

-- The static child rejects a CALL with value 1 to address 33.
private def valueCallCode : ByteArray :=
  ⟨#[0x60, 0, 0x60, 0, 0x60, 0, 0x60, 0, 0x60, 1, 0x60, 33, 0x61, 19, 136, 0xf1]⟩
#eval check <| match NestedRunner.run 20 ⟨staticCall valueCallCode, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s (failed valueCallCode)
  | _ => false

/-- The machine just before a rejected instruction, and the rejection diagnostic. -/
private def rejection (code : ByteArray) (fuel : Nat) (before diagnostic : Frame.State) : Bool :=
  match NestedRunner.run fuel ⟨staticCall code, 0, []⟩ with
  | .exhausted m =>
    sameFrame m.frame before && decide (m.depth = 1) &&
      (match m.callers with
      | [c] => outerCaller c code
      | _ => false) &&
      (match Frame.step m.frame with
      | .exception t .writeInStaticContext => sameFrame t diagnostic
      | _ => false)
  | _ => false

-- SSTORE: two pushes cost 6, and the static check precedes the pops, so the diagnostic is the frame itself.
#eval check <| rejection sstoreCode 3 (calleeFrame sstoreCode 4 4994 ⟨[0, 1], by decide⟩)
  (calleeFrame sstoreCode 4 4994 ⟨[0, 1], by decide⟩)

-- TSTORE: the static check also precedes both pops and the 100 charge.
#eval check <| rejection tstoreCode 3 (calleeFrame tstoreCode 4 4994 ⟨[2, 6], by decide⟩)
  (calleeFrame tstoreCode 4 4994 ⟨[2, 6], by decide⟩)

-- LOG0: the pops and the 375 charge come first, so the diagnostic has an empty stack and 4994 - 375 = 4619 gas.
-- A zero-length range expands no memory, and the PC does not advance.
#eval check <| rejection logCode 3 (calleeFrame logCode 4 4994 ⟨[0, 0], by decide⟩)
  (calleeFrame logCode 4 4619 Stack.empty)

-- CALL with value 1: seven pushes cost 21, and the seven pops precede the static check.
#eval check <| rejection valueCallCode 8
  (calleeFrame valueCallCode 15 4979 ⟨[5000, 33, 1, 0, 0, 0, 0], by decide⟩)
  (calleeFrame valueCallCode 15 4979 Stack.empty)

/-- `PUSH1 0 (x5); PUSH1 33; PUSH2 5000; CALL; STOP`: a zero-value CALL from the static child. -/
private def zeroCallCode : ByteArray :=
  ⟨#[0x60, 0, 0x60, 0, 0x60, 0, 0x60, 0, 0x60, 0, 0x60, 33, 0x61, 19, 136, 0xf1, 0x00]⟩
private def withGrandchild (code : ByteArray) : Frame.State :=
  let s := staticCall zeroCallCode
  let hash := World.codeHash code
  { s with tracker := { s.tracker with writes := { s.tracker.writes with
    accountWrites := (33, some ⟨1, 1, hash⟩) :: s.tracker.writes.accountWrites,
    codeWrites := (hash, code) :: s.tracker.writes.codeWrites } } }

/-- The outer parent's tracker after the STATICCALL reads callee 32 twice. -/
private def outerTracker (code : ByteArray) : TransactionState.State :=
  { (withGrandchild code).tracker with accountReads := [32, 32, 8] }

/-- After the inner CALL: callee 33 is read twice and the child's own account 32 once, as CALL's sender read. -/
private def innerReads (code : ByteArray) : TransactionState.State :=
  { outerTracker code with accountReads := [32, 33, 33, 32, 32, 8] }

/-- The grandchild of `withGrandchild code` at entry.

The child had 5000 - 21 = 4979, paid 3000 for cold 33 and kept 1979.
It forwards min(5000, 1979 - 1979 / 64) = 1949 and keeps 30.
-/
private def grandchildEntry (code : ByteArray) : Frame.State :=
  ⟨code, 0, Stack.empty, 1949, Memory.Allocation.empty, (by intro a _; rfl),
    ⟨⟨#[]⟩, { env with currentTarget := 33, caller := 32, value := 0 }⟩, ⟨#[]⟩,
    checkpoint (checkpoint (innerReads code)), [33, 32, 41, 42], [(43, 44), (45, 46)], true,
    ⟨123, 123, 0, 0, 0⟩, []⟩

/-- The static child suspended at its CALL: PC 15, empty stack, 30 gas and its reservoir drained. -/
private def innerParent (code : ByteArray) : Frame.State :=
  ⟨zeroCallCode, 15, Stack.empty, 30, Memory.Allocation.empty, (by intro a _; rfl),
    ⟨⟨#[]⟩, { env with currentTarget := 32, caller := 7, value := 0 }⟩, ⟨#[]⟩,
    checkpoint (innerReads code), [33, 32, 41, 42], [(43, 44), (45, 46)], true,
    ⟨0, 123, 0, 0, 0⟩, []⟩

-- A zero-value CALL is allowed in the static child, and the grandchild inherits the static flag.
-- Both callers are checked in full: the static child at depth 1 and the fixture parent at depth 0.
#eval check <| match NestedRunner.run 9 ⟨withGrandchild ⟨#[0x00]⟩, 0, []⟩ with
  | .exhausted m => sameFrame m.frame (grandchildEntry ⟨#[0x00]⟩) && decide (m.depth = 2) &&
      (match m.callers with
      | [inner, outer] =>
        sameContinuation inner (innerParent ⟨#[0x00]⟩) ⟨5000, 33, 0, 0, 0, 0, 0⟩ 1 false &&
        sameContinuation outer (preparedParent (outerTracker ⟨#[0x00]⟩) [32, 41, 42]) ⟨5000, 32, 0, 0, 0, 8, 1⟩ 0 false
      | _ => false)
  | _ => false

-- An inherited SSTORE failure in the grandchild fails only the inner CALL, which keeps its 30 gas.
-- The child then stops: the parent gets 2000 + 30 + 7 = 2037 and status 1.
-- The child's 123 reservoir comes back from the failed grandchild's baseline and repays the 7 spill.
-- Warmth merges child-first: [33, 32, 41, 42] ++ [32, 41, 42].
#eval check <| match NestedRunner.run 60 ⟨withGrandchild sstoreCode, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected 2 2037 ⟨[1], by decide⟩ with
      tracker := innerReads sstoreCode, returnData := ⟨#[]⟩,
      warmAddresses := [33, 32, 41, 42, 32, 41, 42], warmSlots := [(43, 44), (45, 46), (43, 44), (45, 46)],
      stateGas := ⟨116, 456, -9, 0, 8⟩ }
  | _ => false

-- A static parent may STATICCALL: there is no static-context check, and the result keeps the parent flag.
#eval check <| match NestedRunner.run 20 ⟨{ staticCall ⟨#[0x00]⟩ with isStatic := true }, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected 2 7007 ⟨[1], by decide⟩ with
      tracker := observedTracker ⟨#[0x00]⟩, returnData := ⟨#[]⟩, isStatic := true,
      warmAddresses := [32, 41, 42, 32, 41, 42], warmSlots := [(43, 44), (45, 46), (43, 44), (45, 46)],
      stateGas := ⟨116, 456, -9, 0, 8⟩ }
  | _ => false

-- At the depth limit both grants return and the parent pushes 0 with 10000 - 3000 = 7000 gas.
-- No new-account refund exists for STATICCALL.
#eval check <| match NestedRunner.run 10 ⟨staticCall ⟨#[0x00]⟩, 1024, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected 2 7000 ⟨[0], by decide⟩ with
      tracker := observedTracker ⟨#[0x00]⟩, returnData := ⟨#[]⟩, warmAddresses := [32, 41, 42] }
  | _ => false

-- Five operands underflow before any gas check or state access.
#eval check <| match NestedRunner.run 4 ⟨{ staticCall ⟨#[0x00]⟩ with gas := 0, stack := ⟨[5000, 32, 0, 0, 8], by decide⟩ }, 1024, []⟩ with
  | .terminal (.exception s .stackUnderflow) =>
    sameFrame s { staticCall ⟨#[0x00]⟩ with gas := 0, stack := Stack.empty }
  | _ => false

-- With 2999 gas the 3000 access cost fails before warming, reading or the depth check.
#eval check <| match NestedRunner.run 4 ⟨{ staticCall ⟨#[0x00]⟩ with gas := 2999 }, 1024, []⟩ with
  | .terminal (.exception s .outOfGas) => sameFrame s { staticCall ⟨#[0x00]⟩ with gas := 2999, stack := Stack.empty }
  | _ => false

-- With exactly 3000 gas the child receives 0 and still stops successfully: 0 + 0 + 7 = 7.
#eval check <| match NestedRunner.run 20 ⟨{ staticCall ⟨#[0x00]⟩ with gas := 3000 }, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected 2 7 ⟨[1], by decide⟩ with
      tracker := observedTracker ⟨#[0x00]⟩, returnData := ⟨#[]⟩,
      warmAddresses := [32, 41, 42, 32, 41, 42], warmSlots := [(43, 44), (45, 46), (43, 44), (45, 46)],
      stateGas := ⟨116, 456, -9, 0, 8⟩ }
  | _ => false

private theorem wideMemoryValid : Memory.Allocation.Valid ⟨[(2, 0xa1), (3, 0xb2)], 3⟩ := by
  intro a h
  have hsmall : initialMemory.words * 32 ≤ a := by
    change 32 ≤ a
    change 96 ≤ a at h
    omega
  exact memoryValid a hsmall

/-- An output range `[64, 96)` grows memory from 1 to 3 words, which costs 9 - 3 = 6. -/
private def wideCall (gas : Nat) : Frame.State :=
  { staticCall ⟨#[0x00]⟩ with gas, stack := ⟨[5000, 32, 0, 0, 64, 32], by decide⟩ }

-- With 5000 gas: 3006 is charged, 1994 is left, and the grant is 1994 - 1994 / 64 = 1963.
-- The parent keeps 31 and ends with 31 + 1963 + 7 = 2001.
#eval check <| match NestedRunner.run 20 ⟨wideCall 5000, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected 2 2001 ⟨[1], by decide⟩ with
      memory := ⟨[(2, 0xa1), (3, 0xb2)], 3⟩, memoryValid := wideMemoryValid,
      tracker := observedTracker ⟨#[0x00]⟩, returnData := ⟨#[]⟩,
      warmAddresses := [32, 41, 42, 32, 41, 42], warmSlots := [(43, 44), (45, 46), (43, 44), (45, 46)],
      stateGas := ⟨116, 456, -9, 0, 8⟩ }
  | _ => false

-- With 3005 gas the access and memory cost of 3006 fails before memory grows.
#eval check <| match NestedRunner.run 4 ⟨wideCall 3005, 0, []⟩ with
  | .terminal (.exception s .outOfGas) => sameFrame s { wideCall 3005 with stack := Stack.empty }
  | _ => false

/-- RIPEMD-160 at warm address 3 with a `grant` request and empty input. -/
private def ripemdCall (grant : Nat) : Frame.State :=
  { fixture 10000 ⟨[BitVec.ofNat 256 grant, 3, 0, 0, 8, 1], by simp⟩ with
    warmAddresses := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 256, 41, 42] }

/-- RIPEMD-160 of the empty string, left-padded to 32 bytes. -/
private def ripemdEmpty : ByteArray :=
  ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x9c, 0x11, 0x85, 0xa5,
      0xc5, 0xe9, 0xfc, 0x54, 0x61, 0x28, 0x08, 0x97, 0x7e, 0xe8, 0xf5, 0x48,
      0xb2, 0x25, 0x8d, 0x31]⟩

private theorem zeroOutputMemoryValid : Memory.Allocation.Valid ⟨[(8, 0), (2, 0xa1), (3, 0xb2)], 1⟩ := by
  change Memory.Allocation.Valid (Memory.Allocation.write initialMemory 8 [0])
  exact Memory.Allocation.write_valid_for_frame _ _ _ memoryValid

-- A 600 grant pays the 600 precompile charge exactly: 10000 - 100 - 600 + 0 + 7 = 9307.
#eval check <| match NestedRunner.run 3 ⟨ripemdCall 600, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected 2 9307 ⟨[1], by decide⟩ with
      memory := ⟨[(8, 0), (2, 0xa1), (3, 0xb2)], 1⟩, memoryValid := zeroOutputMemoryValid,
      tracker := { tracker with accountReads := [3, 3, 8] }, returnData := ripemdEmpty,
      warmAddresses := (ripemdCall 600).warmAddresses ++ (ripemdCall 600).warmAddresses,
      warmSlots := [(43, 44), (45, 46), (43, 44), (45, 46)],
      stateGas := ⟨116, 456, -9, 0, 8⟩ }
  | _ => false

-- A 500 grant is short, so the precompile fails and burns it: 10000 - 100 - 500 = 9400.
#eval check <| match NestedRunner.run 3 ⟨ripemdCall 500, 0, []⟩ with
  | .terminal (.stopped s) => sameFrame s { expected 2 9400 ⟨[0], by decide⟩ with
      tracker := { tracker with accountReads := [3, 3, 8] }, returnData := ⟨#[]⟩,
      warmAddresses := (ripemdCall 500).warmAddresses }
  | _ => false

-- Other precompiles remain a tooling boundary, reported with the entered child.
-- Address 1 is cold and has no account, so its code is empty and it is read twice.
#eval check <| match NestedRunner.run 2 ⟨{ staticCall ⟨#[0x00]⟩ with stack := ⟨[5000, 1, 0, 0, 8, 1], by decide⟩ }, 0, []⟩ with
  | .tooling s .precompile => sameFrame s (child ⟨#[]⟩ 1
      { (staticCall ⟨#[0x00]⟩).tracker with accountReads := [1, 1, 8] } [1, 41, 42] 0 5000 Stack.empty)
  | _ => false

-- Delegation remains a tooling boundary of preparation.
private def delegationCode : ByteArray := ⟨#[0xef, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩
#eval check <| match NestedRunner.run 2 ⟨staticCall delegationCode, 0, []⟩ with
  | .tooling s (.preparation .delegation) => sameFrame s { staticCall delegationCode with
      stack := Stack.empty, warmAddresses := [32, 41, 42],
      tracker := { (observedTracker delegationCode) with accountReads := [32, 8] } }
  | _ => false

-- Fuel exhaustion after one transition retains the entered child and its suspended caller.
#eval check <| match NestedRunner.run 1 ⟨staticCall ⟨#[0x00]⟩, 0, []⟩ with
  | .exhausted m => sameFrame m.frame (calleeFrame ⟨#[0x00]⟩ 0 5000 Stack.empty) && decide (m.depth = 1) &&
      (match m.callers with
      | [c] => outerCaller c ⟨#[0x00]⟩
      | _ => false)
  | _ => false

-- With more fuel the same machine resumes to the STOP result checked above.
#eval check <| match NestedRunner.run 1 ⟨staticCall ⟨#[0x00]⟩, 0, []⟩ with
  | .exhausted m => match NestedRunner.run 19 m with
    | .terminal (.stopped s) => decide (s.gas = 7007 ∧ s.stack.val = [1] ∧ s.pc = 2)
    | _ => false
  | _ => false

-- The legacy runner keeps its suspension boundary.
#eval check <| match Runner.run 5 (staticCall ⟨#[0x00]⟩) with
  | .unsupported s .staticcall => sameFrame s { staticCall ⟨#[0x00]⟩ with stack := Stack.empty }
  | _ => false

-- Direct preparation: two callee reads, both grants and no balance or new-account flag.
#eval check <| match StaticCall.prepare { staticCall ⟨#[0]⟩ with stack := Stack.empty } ⟨5000, 32, 0, 0, 0, 8, 1⟩ with
  | .ready p => sameFrame p.parent { expected 0 2000 Stack.empty with
      tracker := observedTracker ⟨#[0]⟩, returnData := ⟨#[]⟩, warmAddresses := [32, 41, 42],
      stateGas := ⟨0, 456, -9, 7, 8⟩ } &&
      decide (p.request = ⟨5000, 32, 0, 0, 0, 8, 1⟩ ∧ p.address = 32 ∧ p.code = ⟨#[0]⟩ ∧
        p.childGas = 5000 ∧ p.stateGrant = 123 ∧ p.newAccountCharged = false ∧ p.insufficientBalance = false) &&
      (NestedRunner.staticChildFrame p).isStatic &&
      decide ((NestedRunner.staticChildFrame p).context.environment =
        { env with currentTarget := 32, caller := 7, value := 0 })
  | _ => false

-- The same request through CALL preparation also reads the sender, which STATICCALL does not.
#eval check <| match CallPreparation.prepare { staticCall ⟨#[0]⟩ with stack := Stack.empty } ⟨5000, 32, 0, 0, 0, 8, 1⟩ with
  | .ready p => decide (p.parent.tracker.accountReads = [7, 32, 32, 8] ∧ p.parent.gas = 2000)
  | _ => false

/-- A frame unrelated to STATICCALL: other code, a PC past the end, and rich preserved fields. -/
private def unrelated (gas : Nat) (stack : Stack) : Frame.State :=
  { staticCall ⟨#[0x00]⟩ with code := ⟨#[0x01, 0x02]⟩, pc := 9, gas, stack, isStatic := true }

-- Direct entry pops six operands in source order and records value 0; the seventh and eighth stay.
#eval check <| match Frame.staticCallEntry (unrelated 777 ⟨[1, 2, 4, 5, 6, 7, 8, 9], by decide⟩) with
  | .staticCallRequest t r => sameFrame t (unrelated 777 ⟨[8, 9], by decide⟩) &&
      decide (r = ⟨1, 2, 0, 4, 5, 6, 7⟩)
  | _ => false

-- Direct entry with five operands consumes them and underflows; nothing else changes.
#eval check <| match Frame.staticCallEntry (unrelated 777 ⟨[1, 2, 4, 5, 6], by decide⟩) with
  | .exception t .stackUnderflow => sameFrame t (unrelated 777 Stack.empty)
  | _ => false

private def request : Frame.CallRequest := ⟨5000, 32, 0, 0, 0, 8, 1⟩

/-- Account 32 points at code hash 123, which no overlay or parent map holds. -/
private def missingTracker : TransactionState.State :=
  { tracker with writes := { tracker.writes with
    accountWrites := (32, some ⟨1, 1, 123⟩) :: tracker.writes.accountWrites } }

private def delegationTracker : TransactionState.State := (staticCall delegationCode).tracker

-- Direct gas failure returns the unchanged input frame.
#eval check <| match StaticCall.prepare (unrelated 2999 ⟨[99], by decide⟩) request with
  | .outOfGas d => sameFrame d (unrelated 2999 ⟨[99], by decide⟩)
  | _ => false

-- The gas check precedes both the missing-code and the delegation boundaries.
#eval check <| match StaticCall.prepare { unrelated 2999 ⟨[99], by decide⟩ with tracker := missingTracker } request with
  | .outOfGas d => sameFrame d { unrelated 2999 ⟨[99], by decide⟩ with tracker := missingTracker }
  | _ => false
#eval check <| match StaticCall.prepare { unrelated 2999 ⟨[99], by decide⟩ with tracker := delegationTracker } request with
  | .outOfGas d => sameFrame d { unrelated 2999 ⟨[99], by decide⟩ with tracker := delegationTracker }
  | _ => false

-- Missing code: 32 is warmed and read once; gas, memory, stack, PC and code are unchanged.
#eval check <| match StaticCall.prepare { unrelated 3000 ⟨[99], by decide⟩ with tracker := missingTracker } request with
  | .tooling d .missingCode => sameFrame d { unrelated 3000 ⟨[99], by decide⟩ with
      tracker := { missingTracker with accountReads := [32, 8] }, warmAddresses := [32, 41, 42] }
  | _ => false

-- A warm callee costs 100: 99 gas fails, and 100 reaches the missing-code boundary without re-warming.
#eval check <| match StaticCall.prepare { unrelated 99 ⟨[99], by decide⟩ with
    tracker := missingTracker, warmAddresses := [32, 41, 42] } request with
  | .outOfGas d => sameFrame d { unrelated 99 ⟨[99], by decide⟩ with
      tracker := missingTracker, warmAddresses := [32, 41, 42] }
  | _ => false
#eval check <| match StaticCall.prepare { unrelated 100 ⟨[99], by decide⟩ with
    tracker := missingTracker, warmAddresses := [32, 41, 42] } request with
  | .tooling d .missingCode => sameFrame d { unrelated 100 ⟨[99], by decide⟩ with
      tracker := { missingTracker with accountReads := [32, 8] }, warmAddresses := [32, 41, 42] }
  | _ => false

-- Delegation: the same single read and warming, with the designator recognized before the second read.
#eval check <| match StaticCall.prepare { unrelated 3000 ⟨[99], by decide⟩ with tracker := delegationTracker } request with
  | .tooling d .delegation => sameFrame d { unrelated 3000 ⟨[99], by decide⟩ with
      tracker := { delegationTracker with accountReads := [32, 8] }, warmAddresses := [32, 41, 42] }
  | _ => false

-- Nested execution stops at missing code with the popped stack, the warming and one read.
#eval check <| match NestedRunner.run 2 ⟨{ staticCall ⟨#[0x00]⟩ with tracker := missingTracker }, 0, []⟩ with
  | .tooling d (.preparation .missingCode) => sameFrame d { staticCall ⟨#[0x00]⟩ with
      stack := Stack.empty, tracker := { missingTracker with accountReads := [32, 8] }, warmAddresses := [32, 41, 42] }
  | _ => false
