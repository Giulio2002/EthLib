import EthLib.EVM

open EthLib.EVM

deriving instance DecidableEq for World.State
deriving instance DecidableEq for TransactionState.Snapshot
deriving instance DecidableEq for TransactionState.State
deriving instance DecidableEq for BlobFee.Schedule
deriving instance DecidableEq for Environment.Context
deriving instance DecidableEq for CallData.Context

private def mem : Memory.Allocation.State := Memory.Allocation.write Memory.Allocation.empty 2 [0xa1]
private theorem validMem : Memory.Allocation.Valid mem :=
  Memory.Allocation.write_valid_for_frame _ _ _ (by intro a _; rfl)
private def env : Environment.Context :=
  ⟨7, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, [25], [27], BlobFee.amsterdam⟩
private def tx : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], []⟩, {}, [8], [(8, 3)], [9], []⟩
private def frame : Frame.State :=
  ⟨⟨#[0x55]⟩, 0, ⟨[3, 5, 11], by decide⟩, 2301, mem, validMem,
    ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩, tx, [41], [(8, 3)], false, ⟨123, 456, -9, 7, 8⟩⟩
private def same (x y : Frame.State) : Bool :=
  decide (x.code = y.code ∧ x.pc = y.pc ∧ x.stack.val = y.stack.val ∧ x.gas = y.gas ∧
    x.memory = y.memory ∧ x.context = y.context ∧ x.returnData = y.returnData ∧
    x.tracker = y.tracker ∧ x.warmAddresses = y.warmAddresses ∧ x.warmSlots = y.warmSlots ∧
    x.isStatic = y.isStatic ∧ x.stateGas = y.stateGas)
private def check (b : Bool) : IO Unit :=
  if b then pure () else throw (IO.userError "SSTORE initial assertion failed")

-- The static error wins over both underflow and zero gas.
#eval check <| match Frame.step { frame with isStatic := true, stack := Stack.empty, gas := 0 } with
  | .exception t .writeInStaticContext => same t
      ⟨⟨#[0x55]⟩, 0, Stack.empty, 0, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩, tx,
        [41], [(8, 3)], true, ⟨123, 456, -9, 7, 8⟩⟩
  | _ => false

-- The sentry fails after both pops but before warming or recording a read.
#eval check <| match Frame.sstore { frame with gas := 2300 } with
  | .exception t .outOfGas => same t
      ⟨⟨#[0x55]⟩, 0, ⟨[11], by decide⟩, 2300, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        tx, [41], [(8, 3)], false, ⟨123, 456, -9, 7, 8⟩⟩
  | _ => false

-- A cold no-op write reads storage and account, charges access gas, and records the write.
#eval check <| match Frame.step frame with
  | .continue t => same t
      ⟨⟨#[0x55]⟩, 1, ⟨[11], by decide⟩, 201, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], []⟩,
          ⟨[], [((7, 3), 5)], [], [], []⟩, [7, 8], [(7, 3), (8, 3)], [9], []⟩,
        [41], [(7, 3), (8, 3)], false, ⟨123, 456, -9, 7, 8⟩⟩
  | _ => false

-- Clearing a nonzero original slot grants the signed refund and charges the write cost.
#eval check <| match Frame.sstore { frame with stack := ⟨[3, 0, 11], by decide⟩, gas := 20000 } with
  | .continue t => same t
      ⟨⟨#[0x55]⟩, 1, ⟨[11], by decide⟩, 7900, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], []⟩,
          ⟨[], [((7, 3), 0)], [], [], []⟩, [7, 8], [(7, 3), (8, 3)], [9], []⟩,
        [41], [(7, 3), (8, 3)], false, ⟨123, 456, 11607, 7, 8⟩⟩
  | _ => false

-- A warm first set of a zero slot draws 97920 state gas after execution gas.
#eval check <| match Frame.sstore { frame with stack := ⟨[4, 7, 11], by decide⟩, gas := 12000, warmSlots := [(7, 4), (8, 3)], stateGas := ⟨97920, 456, -9, 7, 8⟩ } with
  | .continue t => same t
      ⟨⟨#[0x55]⟩, 1, ⟨[11], by decide⟩, 1900, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], []⟩,
          ⟨[], [((7, 4), 7)], [], [], []⟩, [7, 8], [(7, 4), (8, 3)], [9], []⟩,
        [41], [(7, 4), (8, 3)], false, ⟨0, 456, -9, 7, 8⟩⟩
  | _ => false

-- State-gas failure occurs after execution gas, warming and the storage read.
#eval check <| match Frame.sstore { frame with stack := ⟨[4, 7, 11], by decide⟩, gas := 12100 } with
  | .exception t .outOfGas => same t
      ⟨⟨#[0x55]⟩, 0, ⟨[11], by decide⟩, 0, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], []⟩, {}, [8], [(7, 4), (8, 3)], [9], []⟩,
        [41], [(7, 4), (8, 3)], false, ⟨123, 456, -9, 7, 8⟩⟩
  | _ => false

-- Restoring a zero original slot credits spill first and then the reservoir.
#eval check <| match Frame.sstore { frame with stack := ⟨[4, 0, 11], by decide⟩, tracker := { tx with writes := { tx.writes with storageWrites := [((7, 4), 4)] } } } with
  | .continue t => same t
      ⟨⟨#[0x55]⟩, 1, ⟨[11], by decide⟩, 208, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], []⟩,
          ⟨[], [((7, 4), 0), ((7, 4), 4)], [], [], []⟩, [7, 8], [(7, 4), (8, 3)], [9], []⟩,
        [41], [(7, 4), (8, 3)], false, ⟨98036, 456, 9991, 0, 8⟩⟩
  | _ => false

-- Actual SSTORE then SLOAD reads the overlay and pays the warm-slot charge.
#eval check <| match Runner.run 3 { frame with code := ⟨#[0x55, 0x54, 0x00]⟩, stack := ⟨[3, 5, 3, 11], by decide⟩ } with
  | .stopped t => same t
      ⟨⟨#[0x55, 0x54, 0x00]⟩, 3, ⟨[5, 11], by decide⟩, 101, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], []⟩,
          ⟨[], [((7, 3), 5)], [], [], []⟩, [7, 8], [(7, 3), (7, 3), (8, 3)], [9], []⟩,
        [41], [(7, 3), (8, 3)], false, ⟨123, 456, -9, 7, 8⟩⟩
  | _ => false

-- A single operand is popped before the second pop underflows.
#eval check <| match Frame.sstore { frame with stack := ⟨[3], by decide⟩, gas := 0 } with
  | .exception t .stackUnderflow => same t
      ⟨⟨#[0x55]⟩, 0, Stack.empty, 0, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩, tx,
        [41], [(8, 3)], false, ⟨123, 456, -9, 7, 8⟩⟩
  | _ => false

-- State-dependent execution-gas failure retains warming, reads and the refund update.
#eval check <| match Frame.sstore { frame with stack := ⟨[3, 0, 11], by decide⟩ } with
  | .exception t .outOfGas => same t
      ⟨⟨#[0x55]⟩, 0, ⟨[11], by decide⟩, 2301, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], []⟩, {}, [8], [(7, 3), (8, 3)], [9], []⟩,
        [41], [(7, 3), (8, 3)], false, ⟨123, 456, 11607, 7, 8⟩⟩
  | _ => false

-- A tombstone shadows the parent account, so the write fails after the account read.
#eval check <| match Frame.sstore { frame with tracker := { tx with writes := { tx.writes with accountWrites := [(7, none)] } } } with
  | .exception t .missingStorageAccount => same t
      ⟨⟨#[0x55]⟩, 0, ⟨[11], by decide⟩, 201, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], []⟩,
          ⟨[(7, none)], [], [], [], []⟩, [7, 8], [(7, 3), (8, 3)], [9], []⟩,
        [41], [(7, 3), (8, 3)], false, ⟨123, 456, -9, 7, 8⟩⟩
  | _ => false

-- Restoring a nonzero original slot reverses the clear refund and credits the write refund.
#eval check <| match Frame.sstore { frame with stack := ⟨[3, 5, 11], by decide⟩, warmSlots := [(7, 3), (8, 3)], tracker := { tx with writes := { tx.writes with storageWrites := [((7, 3), 0)] } } } with
  | .continue t => same t
      ⟨⟨#[0x55]⟩, 1, ⟨[11], by decide⟩, 2201, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], []⟩,
          ⟨[], [((7, 3), 5), ((7, 3), 0)], [], [], []⟩, [7, 8], [(7, 3), (8, 3)], [9], []⟩,
        [41], [(7, 3), (8, 3)], false, ⟨123, 456, -1625, 7, 8⟩⟩
  | _ => false

-- An exact combined-pool state charge spills the uncovered amount into execution gas.
#eval check <| match Frame.sstore { frame with stack := ⟨[4, 7, 11], by decide⟩, gas := 109897 } with
  | .continue t => same t
      ⟨⟨#[0x55]⟩, 1, ⟨[11], by decide⟩, 0, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], []⟩,
          ⟨[], [((7, 4), 7)], [], [], []⟩, [7, 8], [(7, 4), (8, 3)], [9], []⟩,
        [41], [(7, 4), (8, 3)], false, ⟨0, 456, -9, 97804, 8⟩⟩
  | _ => false

-- A newly created account has original zero even when the parent slot is nonzero.
#eval check <| match Frame.sstore { frame with stack := ⟨[3, 0, 11], by decide⟩, tracker := { tx with createdAccounts := [7, 9] } } with
  | .continue t => same t
      ⟨⟨#[0x55]⟩, 1, ⟨[11], by decide⟩, 208, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], []⟩,
          ⟨[], [((7, 3), 0)], [], [], []⟩, [7, 8], [(7, 3), (8, 3)], [7, 9], []⟩,
        [41], [(7, 3), (8, 3)], false, ⟨98036, 456, 9991, 0, 8⟩⟩
  | _ => false

-- Repeated writes use a cold slot first and retain duplicate read observations.
#eval check <| match Runner.run 3 { frame with code := ⟨#[0x55, 0x55, 0x00]⟩, stack := ⟨[3, 5, 3, 5, 11], by decide⟩, gas := 4401 } with
  | .stopped t => same t
      ⟨⟨#[0x55, 0x55, 0x00]⟩, 3, ⟨[11], by decide⟩, 2201, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], []⟩,
          ⟨[], [((7, 3), 5), ((7, 3), 5)], [], [], []⟩, [7, 7, 8], [(7, 3), (7, 3), (8, 3)], [9], []⟩,
        [41], [(7, 3), (8, 3)], false, ⟨123, 456, -9, 7, 8⟩⟩
  | _ => false

-- Duplicate write and warm entries use the first write and retain all prior entries.
#eval check <| match Frame.sstore { frame with stack := ⟨[3, 5, 11], by decide⟩, warmSlots := [(7, 3), (7, 3), (8, 3)], tracker := { tx with writes := { tx.writes with storageWrites := [((7, 3), 0), ((7, 3), 88)] } } } with
  | .continue t => same t
      ⟨⟨#[0x55]⟩, 1, ⟨[11], by decide⟩, 2201, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], []⟩,
          ⟨[], [((7, 3), 5), ((7, 3), 0), ((7, 3), 88)], [], [], []⟩, [7, 8], [(7, 3), (8, 3)], [9], []⟩,
        [41], [(7, 3), (7, 3), (8, 3)], false, ⟨123, 456, -1625, 7, 8⟩⟩
  | _ => false

-- An account absent from both overlay and parent fails after recording the read.
#eval check <| match Frame.sstore { frame with tracker := { tx with parent := { tx.parent with accounts := [] } } } with
  | .exception t .missingStorageAccount => same t
      ⟨⟨#[0x55]⟩, 0, ⟨[11], by decide⟩, 201, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[], [((7, 3), 5)], []⟩, {}, [7, 8], [(7, 3), (8, 3)], [9], []⟩,
        [41], [(7, 3), (8, 3)], false, ⟨123, 456, -9, 7, 8⟩⟩
  | _ => false

-- A credit smaller than prior spill goes entirely back to execution gas.
#eval check <| match Frame.sstore { frame with stack := ⟨[4, 0, 11], by decide⟩, stateGas := ⟨123, 456, -9, 100000, 8⟩, tracker := { tx with writes := { tx.writes with storageWrites := [((7, 4), 4)] } } } with
  | .continue t => same t
      ⟨⟨#[0x55]⟩, 1, ⟨[11], by decide⟩, 98121, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], []⟩,
          ⟨[], [((7, 4), 0), ((7, 4), 4)], [], [], []⟩, [7, 8], [(7, 4), (8, 3)], [9], []⟩,
        [41], [(7, 4), (8, 3)], false, ⟨123, 456, 9991, 2080, 8⟩⟩
  | _ => false

-- Dispatch reports the stipend failure after both pops and before warming.
#eval check <| match Frame.step { frame with gas := 2300 } with
  | .exception t .outOfGas => same t
      ⟨⟨#[0x55]⟩, 0, ⟨[11], by decide⟩, 2300, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        tx, [41], [(8, 3)], false, ⟨123, 456, -9, 7, 8⟩⟩
  | _ => false

-- Dispatch preserves the first popped stack on second-pop underflow.
#eval check <| match Frame.step { frame with stack := ⟨[3], by decide⟩, gas := 0 } with
  | .exception t .stackUnderflow => same t
      ⟨⟨#[0x55]⟩, 0, Stack.empty, 0, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩, tx,
        [41], [(8, 3)], false, ⟨123, 456, -9, 7, 8⟩⟩
  | _ => false

-- Dispatch retains the read and refund update when execution gas is insufficient.
#eval check <| match Frame.step { frame with stack := ⟨[3, 0, 11], by decide⟩ } with
  | .exception t .outOfGas => same t
      ⟨⟨#[0x55]⟩, 0, ⟨[11], by decide⟩, 2301, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], []⟩, {}, [8], [(7, 3), (8, 3)], [9], []⟩,
        [41], [(7, 3), (8, 3)], false, ⟨123, 456, 11607, 7, 8⟩⟩
  | _ => false

-- Dispatch retains the paid execution charge when state gas is insufficient.
#eval check <| match Frame.step { frame with stack := ⟨[4, 7, 11], by decide⟩, gas := 12100 } with
  | .exception t .outOfGas => same t
      ⟨⟨#[0x55]⟩, 0, ⟨[11], by decide⟩, 0, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], []⟩, {}, [8], [(7, 4), (8, 3)], [9], []⟩,
        [41], [(7, 4), (8, 3)], false, ⟨123, 456, -9, 7, 8⟩⟩
  | _ => false

-- Dispatch reports a missing account after charging and recording the account read.
#eval check <| match Frame.step { frame with tracker := { tx with writes := { tx.writes with accountWrites := [(7, none)] } } } with
  | .exception t .missingStorageAccount => same t
      ⟨⟨#[0x55]⟩, 0, ⟨[11], by decide⟩, 201, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], []⟩,
          ⟨[(7, none)], [], [], [], []⟩, [7, 8], [(7, 3), (8, 3)], [9], []⟩,
        [41], [(7, 3), (8, 3)], false, ⟨123, 456, -9, 7, 8⟩⟩
  | _ => false

-- Direct execution does not inspect unrelated code or PC, and retains all snapshot fields.
#eval check <| match Frame.sstore { frame with code := ⟨#[0xaa, 0xbb]⟩, pc := 7, tracker := ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], [(8, ⟨#[2]⟩)]⟩, ⟨[(8, none)], [((8, 2), 4)], [(9, ⟨#[3]⟩)], [8], [((8, 1), 6)]⟩, [8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 7)], [(10, ⟨#[5]⟩)], [10], [((8, 5), 9)]⟩]⟩ } with
  | .continue t => same t
      ⟨⟨#[0xaa, 0xbb]⟩, 8, ⟨[11], by decide⟩, 201, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], [(8, ⟨#[2]⟩)]⟩,
          ⟨[(8, none)], [((7, 3), 5), ((8, 2), 4)], [(9, ⟨#[3]⟩)], [8], [((8, 1), 6)]⟩,
          [7, 8], [(7, 3), (8, 3)], [9], [⟨[(8, none)], [((8, 4), 7)], [(10, ⟨#[5]⟩)], [10], [((8, 5), 9)]⟩]⟩,
        [41], [(7, 3), (8, 3)], false, ⟨123, 456, -9, 7, 8⟩⟩
  | _ => false

-- Empty stack takes priority over the stipend sentry at dispatch.
#eval check <| match Frame.step { frame with stack := Stack.empty, gas := 0 } with
  | .exception t .stackUnderflow => same t
      ⟨⟨#[0x55]⟩, 0, Stack.empty, 0, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩, tx,
        [41], [(8, 3)], false, ⟨123, 456, -9, 7, 8⟩⟩
  | _ => false

-- A zero-to-zero write has no write charge, state charge, or refund change.
#eval check <| match Frame.sstore { frame with stack := ⟨[4, 0, 11], by decide⟩ } with
  | .continue t => same t
      ⟨⟨#[0x55]⟩, 1, ⟨[11], by decide⟩, 201, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], []⟩,
          ⟨[], [((7, 4), 0)], [], [], []⟩, [7, 8], [(7, 4), (8, 3)], [9], []⟩,
        [41], [(7, 4), (8, 3)], false, ⟨123, 456, -9, 7, 8⟩⟩
  | _ => false

-- Reversing a prior clear without restoring the original makes the refund negative.
#eval check <| match Frame.sstore { frame with stack := ⟨[3, 7, 11], by decide⟩, warmSlots := [(7, 3), (8, 3)], tracker := { tx with writes := { tx.writes with storageWrites := [((7, 3), 0)] } } } with
  | .continue t => same t
      ⟨⟨#[0x55]⟩, 1, ⟨[11], by decide⟩, 2201, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], []⟩,
          ⟨[], [((7, 3), 7), ((7, 3), 0)], [], [], []⟩, [7, 8], [(7, 3), (8, 3)], [9], []⟩,
        [41], [(7, 3), (8, 3)], false, ⟨123, 456, -11625, 7, 8⟩⟩
  | _ => false

-- Replacing an unchanged nonzero original charges a write without a refund.
#eval check <| match Frame.sstore { frame with stack := ⟨[3, 7, 11], by decide⟩, gas := 20000 } with
  | .continue t => same t
      ⟨⟨#[0x55]⟩, 1, ⟨[11], by decide⟩, 7900, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], []⟩,
          ⟨[], [((7, 3), 7)], [], [], []⟩, [7, 8], [(7, 3), (8, 3)], [9], []⟩,
        [41], [(7, 3), (8, 3)], false, ⟨123, 456, -9, 7, 8⟩⟩
  | _ => false

-- A state charge one below the combined-pool boundary fails without taking either pool.
#eval check <| match Frame.step { frame with stack := ⟨[4, 7, 11], by decide⟩, gas := 109896 } with
  | .exception t .outOfGas => same t
      ⟨⟨#[0x55]⟩, 0, ⟨[11], by decide⟩, 97796, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], []⟩, {}, [8], [(7, 4), (8, 3)], [9], []⟩,
        [41], [(7, 4), (8, 3)], false, ⟨123, 456, -9, 7, 8⟩⟩
  | _ => false

-- The sentry is still 2301 for an already warm slot.
#eval check <| match Frame.step { frame with gas := 2300, warmSlots := [(7, 3), (8, 3)] } with
  | .exception t .outOfGas => same t
      ⟨⟨#[0x55]⟩, 0, ⟨[11], by decide⟩, 2300, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        tx, [41], [(7, 3), (8, 3)], false, ⟨123, 456, -9, 7, 8⟩⟩
  | _ => false

-- A clear hides the parent current value while original storage still reads the parent.
#eval check <| match Frame.sstore { frame with tracker := { tx with writes := { tx.writes with storageClears := [7] } } } with
  | .continue t => same t
      ⟨⟨#[0x55]⟩, 1, ⟨[11], by decide⟩, 201, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], []⟩,
          ⟨[], [((7, 3), 5)], [], [7], []⟩, [7, 8], [(7, 3), (8, 3)], [9], []⟩,
        [41], [(7, 3), (8, 3)], false, ⟨123, 456, -1625, 7, 8⟩⟩
  | _ => false

-- Each helper error below uses unrelated code and an out-of-bounds PC.
private def richTx : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], [(8, ⟨#[2]⟩)]⟩,
    ⟨[(8, none)], [((8, 2), 4)], [(9, ⟨#[3]⟩)], [8], [((8, 1), 6)]⟩,
    [8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 7)], [(10, ⟨#[5]⟩)], [10], [((8, 5), 9)]⟩]⟩

private def richRead3 : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], [(8, ⟨#[2]⟩)]⟩,
    ⟨[(8, none)], [((8, 2), 4)], [(9, ⟨#[3]⟩)], [8], [((8, 1), 6)]⟩,
    [8], [(7, 3), (8, 3)], [9], [⟨[(8, none)], [((8, 4), 7)], [(10, ⟨#[5]⟩)], [10], [((8, 5), 9)]⟩]⟩

private def richRead4 : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], [(8, ⟨#[2]⟩)]⟩,
    ⟨[(8, none)], [((8, 2), 4)], [(9, ⟨#[3]⟩)], [8], [((8, 1), 6)]⟩,
    [8], [(7, 4), (8, 3)], [9], [⟨[(8, none)], [((8, 4), 7)], [(10, ⟨#[5]⟩)], [10], [((8, 5), 9)]⟩]⟩

private def richMissing : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], [(8, ⟨#[2]⟩)]⟩,
    ⟨[(7, none), (8, none)], [((8, 2), 4)], [(9, ⟨#[3]⟩)], [8], [((8, 1), 6)]⟩,
    [8], [(8, 3)], [9], [⟨[(8, none)], [((8, 4), 7)], [(10, ⟨#[5]⟩)], [10], [((8, 5), 9)]⟩]⟩

private def richMissingAfter : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], [(8, ⟨#[2]⟩)]⟩,
    ⟨[(7, none), (8, none)], [((8, 2), 4)], [(9, ⟨#[3]⟩)], [8], [((8, 1), 6)]⟩,
    [7, 8], [(7, 3), (8, 3)], [9], [⟨[(8, none)], [((8, 4), 7)], [(10, ⟨#[5]⟩)], [10], [((8, 5), 9)]⟩]⟩

private def helperFrame (stack : Stack) (gas : Nat) (tracker : TransactionState.State)
    (slots : List (World.Address × Word)) (static : Bool) (meter : Frame.StateGas) : Frame.State :=
  ⟨⟨#[0xaa, 0xbb]⟩, 99, stack, gas, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
    tracker, [41], slots, static, meter⟩

#eval check <| match Frame.sstore (helperFrame Stack.empty 0 richTx [(8, 3)] true ⟨123, 456, -9, 7, 8⟩) with
  | .exception t .writeInStaticContext => same t (helperFrame Stack.empty 0 richTx [(8, 3)] true ⟨123, 456, -9, 7, 8⟩)
  | _ => false
#eval check <| match Frame.sstore (helperFrame Stack.empty 0 richTx [(8, 3)] false ⟨123, 456, -9, 7, 8⟩) with
  | .exception t .stackUnderflow => same t (helperFrame Stack.empty 0 richTx [(8, 3)] false ⟨123, 456, -9, 7, 8⟩)
  | _ => false
#eval check <| match Frame.sstore (helperFrame ⟨[3], by decide⟩ 0 richTx [(8, 3)] false ⟨123, 456, -9, 7, 8⟩) with
  | .exception t .stackUnderflow => same t (helperFrame Stack.empty 0 richTx [(8, 3)] false ⟨123, 456, -9, 7, 8⟩)
  | _ => false
#eval check <| match Frame.sstore (helperFrame ⟨[3, 5, 11], by decide⟩ 2300 richTx [(8, 3)] false ⟨123, 456, -9, 7, 8⟩) with
  | .exception t .outOfGas => same t (helperFrame ⟨[11], by decide⟩ 2300 richTx [(8, 3)] false ⟨123, 456, -9, 7, 8⟩)
  | _ => false
#eval check <| match Frame.sstore (helperFrame ⟨[3, 0, 11], by decide⟩ 2301 richTx [(8, 3)] false ⟨123, 456, -9, 7, 8⟩) with
  | .exception t .outOfGas => same t (helperFrame ⟨[11], by decide⟩ 2301 richRead3 [(7, 3), (8, 3)] false ⟨123, 456, 11607, 7, 8⟩)
  | _ => false
#eval check <| match Frame.sstore (helperFrame ⟨[4, 7, 11], by decide⟩ 109896 richTx [(8, 3)] false ⟨123, 456, -9, 7, 8⟩) with
  | .exception t .outOfGas => same t (helperFrame ⟨[11], by decide⟩ 97796 richRead4 [(7, 4), (8, 3)] false ⟨123, 456, -9, 7, 8⟩)
  | _ => false
#eval check <| match Frame.sstore (helperFrame ⟨[3, 5, 11], by decide⟩ 2301 richMissing [(8, 3)] false ⟨123, 456, -9, 7, 8⟩) with
  | .exception t .missingStorageAccount => same t (helperFrame ⟨[11], by decide⟩ 201 richMissingAfter [(7, 3), (8, 3)] false ⟨123, 456, -9, 7, 8⟩)
  | _ => false


-- Exercise each diagnostic through real dispatch with populated retained fields.
private def dispatchRichFrame (stack : Stack) (gas : Nat) (tracker : TransactionState.State)
    (slots : List (World.Address × Word)) (static : Bool) (meter : Frame.StateGas) : Frame.State :=
  { helperFrame stack gas tracker slots static meter with code := ⟨#[0xaa, 0x55, 0xbb]⟩, pc := 1 }

#eval check <| match Frame.step (dispatchRichFrame Stack.empty 0 richTx [(8, 3)] true ⟨123, 456, -9, 7, 8⟩) with
  | .exception t .writeInStaticContext => same t (dispatchRichFrame Stack.empty 0 richTx [(8, 3)] true ⟨123, 456, -9, 7, 8⟩)
  | _ => false
#eval check <| match Frame.step (dispatchRichFrame Stack.empty 0 richTx [(8, 3)] false ⟨123, 456, -9, 7, 8⟩) with
  | .exception t .stackUnderflow => same t (dispatchRichFrame Stack.empty 0 richTx [(8, 3)] false ⟨123, 456, -9, 7, 8⟩)
  | _ => false
#eval check <| match Frame.step (dispatchRichFrame ⟨[3], by decide⟩ 0 richTx [(8, 3)] false ⟨123, 456, -9, 7, 8⟩) with
  | .exception t .stackUnderflow => same t (dispatchRichFrame Stack.empty 0 richTx [(8, 3)] false ⟨123, 456, -9, 7, 8⟩)
  | _ => false
#eval check <| match Frame.step (dispatchRichFrame ⟨[3, 5, 11], by decide⟩ 2300 richTx [(8, 3)] false ⟨123, 456, -9, 7, 8⟩) with
  | .exception t .outOfGas => same t (dispatchRichFrame ⟨[11], by decide⟩ 2300 richTx [(8, 3)] false ⟨123, 456, -9, 7, 8⟩)
  | _ => false
#eval check <| match Frame.step (dispatchRichFrame ⟨[3, 0, 11], by decide⟩ 2301 richTx [(8, 3)] false ⟨123, 456, -9, 7, 8⟩) with
  | .exception t .outOfGas => same t (dispatchRichFrame ⟨[11], by decide⟩ 2301 richRead3 [(7, 3), (8, 3)] false ⟨123, 456, 11607, 7, 8⟩)
  | _ => false
#eval check <| match Frame.step (dispatchRichFrame ⟨[4, 7, 11], by decide⟩ 109896 richTx [(8, 3)] false ⟨123, 456, -9, 7, 8⟩) with
  | .exception t .outOfGas => same t (dispatchRichFrame ⟨[11], by decide⟩ 97796 richRead4 [(7, 4), (8, 3)] false ⟨123, 456, -9, 7, 8⟩)
  | _ => false
#eval check <| match Frame.step (dispatchRichFrame ⟨[3, 5, 11], by decide⟩ 2301 richMissing [(8, 3)] false ⟨123, 456, -9, 7, 8⟩) with
  | .exception t .missingStorageAccount => same t (dispatchRichFrame ⟨[11], by decide⟩ 201 richMissingAfter [(7, 3), (8, 3)] false ⟨123, 456, -9, 7, 8⟩)
  | _ => false
