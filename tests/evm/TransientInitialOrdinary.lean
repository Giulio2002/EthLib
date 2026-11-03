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
private def snap : TransactionState.Snapshot := ⟨[], [((8, 2), 3)], [], [], [((7, 2), 8)]⟩
private def tx : TransactionState.State :=
  ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], [(8, ⟨#[0x77]⟩)]⟩,
    ⟨[(8, some ⟨2, 3, 4⟩)], [((7, 3), 9)], [(12, ⟨#[0x66]⟩)], [8], [((7, 3), 4), ((7, 3), 6), ((8, 3), 2)]⟩,
    [8], [(8, 3)], [9], [snap]⟩
private def frame (stack : Stack) (gas : Nat) : Frame.State :=
  ⟨⟨#[0xaa]⟩, 99, stack, gas, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
    tx, [41], [(8, 3)], false, ⟨123, 456, -9, 7, 8⟩, []⟩
private def same (x y : Frame.State) : Bool :=
  decide (x.code = y.code ∧ x.pc = y.pc ∧ x.stack.val = y.stack.val ∧ x.gas = y.gas ∧
    x.memory = y.memory ∧ x.context = y.context ∧ x.returnData = y.returnData ∧
    x.tracker = y.tracker ∧ x.warmAddresses = y.warmAddresses ∧ x.warmSlots = y.warmSlots ∧
    x.isStatic = y.isStatic ∧ x.stateGas = y.stateGas)
private def check (b : Bool) : IO Unit :=
  if b then pure () else throw (IO.userError "transient assertion failed")

#eval check <| match Frame.tload (frame Stack.empty 0) with
  | .exception t .stackUnderflow => same t (frame Stack.empty 0)
  | _ => false
#eval check <| match Frame.tload (frame ⟨[3, 11], by decide⟩ 99) with
  | .exception t .outOfGas => same t (frame ⟨[11], by decide⟩ 99)
  | _ => false
#eval check <| match Frame.tload (frame ⟨[3, 11], by decide⟩ 100) with
  | .continue t => same t { frame ⟨[4, 11], by decide⟩ 0 with pc := 100 }
  | _ => false
#eval check <| match Frame.tstore { frame Stack.empty 0 with isStatic := true } with
  | .exception t .writeInStaticContext => same t { frame Stack.empty 0 with isStatic := true }
  | _ => false
#eval check <| match Frame.tstore (frame ⟨[3], by decide⟩ 0) with
  | .exception t .stackUnderflow => same t (frame Stack.empty 0)
  | _ => false
#eval check <| match Frame.tstore (frame ⟨[3, 9, 11], by decide⟩ 99) with
  | .exception t .outOfGas => same t (frame ⟨[11], by decide⟩ 99)
  | _ => false
#eval check <| match Frame.tstore (frame ⟨[3, 0, 11], by decide⟩ 100) with
  | .continue t => same t ⟨⟨#[0xaa]⟩, 100, ⟨[11], by decide⟩, 0, mem, validMem,
      ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
      ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], [(8, ⟨#[0x77]⟩)]⟩,
        ⟨[(8, some ⟨2, 3, 4⟩)], [((7, 3), 9)], [(12, ⟨#[0x66]⟩)], [8], [((8, 3), 2)]⟩, [8], [(8, 3)], [9], [snap]⟩,
      [41], [(8, 3)], false, ⟨123, 456, -9, 7, 8⟩, []⟩
  | _ => false

-- The dispatcher executes a write, a read, a pop and deletion before STOP.
#eval check <| match Runner.run 5 { frame ⟨[3, 9, 3, 3, 0, 11], by decide⟩ 302 with
    code := ⟨#[0x5d, 0x5c, 0x50, 0x5d, 0x00]⟩, pc := 0 } with
  | .stopped t => same t
      ⟨⟨#[0x5d, 0x5c, 0x50, 0x5d, 0x00]⟩, 5, ⟨[11], by decide⟩, 0, mem, validMem,
        ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], [(8, ⟨#[0x77]⟩)]⟩,
          ⟨[(8, some ⟨2, 3, 4⟩)], [((7, 3), 9)], [(12, ⟨#[0x66]⟩)], [8], [((8, 3), 2)]⟩, [8], [(8, 3)], [9], [snap]⟩,
        [41], [(8, 3)], false, ⟨123, 456, -9, 7, 8⟩, []⟩
  | _ => false

-- Dispatch preserves the complete frame at each source-order failure.
#eval check <| match Frame.step { frame Stack.empty 0 with code := ⟨#[0x5c]⟩, pc := 0 } with
  | .exception t .stackUnderflow => same t { frame Stack.empty 0 with code := ⟨#[0x5c]⟩, pc := 0 }
  | _ => false
#eval check <| match Frame.step { frame ⟨[3, 11], by decide⟩ 99 with code := ⟨#[0x5c]⟩, pc := 0 } with
  | .exception t .outOfGas => same t { frame ⟨[11], by decide⟩ 99 with code := ⟨#[0x5c]⟩, pc := 0 }
  | _ => false
#eval check <| match Frame.step { frame ⟨[3, 11], by decide⟩ 100 with code := ⟨#[0x5c]⟩, pc := 0 } with
  | .continue t => same t { frame ⟨[4, 11], by decide⟩ 0 with code := ⟨#[0x5c]⟩, pc := 1 }
  | _ => false
#eval check <| match Frame.step { frame Stack.empty 0 with code := ⟨#[0x5d]⟩, pc := 0, isStatic := true } with
  | .exception t .writeInStaticContext => same t { frame Stack.empty 0 with code := ⟨#[0x5d]⟩, pc := 0, isStatic := true }
  | _ => false
#eval check <| match Frame.step { frame Stack.empty 0 with code := ⟨#[0x5d]⟩, pc := 0 } with
  | .exception t .stackUnderflow => same t { frame Stack.empty 0 with code := ⟨#[0x5d]⟩, pc := 0 }
  | _ => false
#eval check <| match Frame.step { frame ⟨[3], by decide⟩ 0 with code := ⟨#[0x5d]⟩, pc := 0 } with
  | .exception t .stackUnderflow => same t { frame Stack.empty 0 with code := ⟨#[0x5d]⟩, pc := 0 }
  | _ => false
#eval check <| match Frame.step { frame ⟨[3, 9, 11], by decide⟩ 99 with code := ⟨#[0x5d]⟩, pc := 0 } with
  | .exception t .outOfGas => same t { frame ⟨[11], by decide⟩ 99 with code := ⟨#[0x5d]⟩, pc := 0 }
  | _ => false
#eval check <| match Frame.step { frame ⟨[3, 0, 11], by decide⟩ 100 with code := ⟨#[0x5d]⟩, pc := 0 } with
  | .continue t => same t
      ⟨⟨#[0x5d]⟩, 1, ⟨[11], by decide⟩, 0, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], [(8, ⟨#[0x77]⟩)]⟩,
          ⟨[(8, some ⟨2, 3, 4⟩)], [((7, 3), 9)], [(12, ⟨#[0x66]⟩)], [8], [((8, 3), 2)]⟩,
          [8], [(8, 3)], [9], [snap]⟩, [41], [(8, 3)], false, ⟨123, 456, -9, 7, 8⟩, []⟩
  | _ => false

#eval check <| match Frame.tstore (frame Stack.empty 0) with
  | .exception t .stackUnderflow => same t (frame Stack.empty 0)
  | _ => false
#eval check <| match Frame.tstore (frame ⟨[3, 9, 11], by decide⟩ 100) with
  | .continue t => same t
      ⟨⟨#[0xaa]⟩, 100, ⟨[11], by decide⟩, 0, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], [(8, ⟨#[0x77]⟩)]⟩,
          ⟨[(8, some ⟨2, 3, 4⟩)], [((7, 3), 9)], [(12, ⟨#[0x66]⟩)], [8],
            [((7, 3), 9), ((8, 3), 2)]⟩, [8], [(8, 3)], [9], [snap]⟩,
        [41], [(8, 3)], false, ⟨123, 456, -9, 7, 8⟩, []⟩
  | _ => false
-- A high key is kept at full word width and does not alias key 3.
#eval check <| match Frame.tload (frame ⟨[(2^200 + 3), 11], by decide⟩ 100) with
  | .continue t => same t { frame ⟨[0, 11], by decide⟩ 0 with pc := 100 }
  | _ => false

#eval check <| match Frame.step { frame ⟨[(2^200 + 3), 11], by decide⟩ 100 with code := ⟨#[0x5c]⟩, pc := 0 } with
  | .continue t => same t { frame ⟨[0, 11], by decide⟩ 0 with code := ⟨#[0x5c]⟩, pc := 1 }
  | _ => false
#eval check <| match TransactionState.rollback
  (TransactionTracker.setTransientStorage (TransactionState.snapshot tx) 7 3 9) with
  | .ok result => decide (result = tx)
  | .error _ => false

-- A nonzero high-key write keeps all lower and other-address entries.
#eval check <| match Frame.step { frame ⟨[(2^200 + 3), 9, 11], by decide⟩ 100 with code := ⟨#[0x5d]⟩, pc := 0 } with
  | .continue t => same t
      ⟨⟨#[0x5d]⟩, 1, ⟨[11], by decide⟩, 0, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], [(8, ⟨#[0x77]⟩)]⟩,
          ⟨[(8, some ⟨2, 3, 4⟩)], [((7, 3), 9)], [(12, ⟨#[0x66]⟩)], [8],
            [((7, 2^200 + 3), 9), ((7, 3), 4), ((7, 3), 6), ((8, 3), 2)]⟩,
          [8], [(8, 3)], [9], [snap]⟩, [41], [(8, 3)], false, ⟨123, 456, -9, 7, 8⟩, []⟩
  | _ => false

-- TSTORE changes transient storage while preserving every nonempty persistent overlay.
#eval check <| match Runner.run 2 { frame ⟨[3, 9, 11], by decide⟩ 100 with code := ⟨#[0x5d, 0x00]⟩, pc := 0 } with
  | .stopped t => same t
      ⟨⟨#[0x5d, 0x00]⟩, 2, ⟨[11], by decide⟩, 0, mem, validMem, ⟨⟨#[4]⟩, env⟩, ⟨#[6]⟩,
        ⟨⟨[(7, ⟨1, 99, 8⟩)], [((7, 3), 5)], [(8, ⟨#[0x77]⟩)]⟩,
          ⟨[(8, some ⟨2, 3, 4⟩)], [((7, 3), 9)], [(12, ⟨#[0x66]⟩)], [8],
            [((7, 3), 9), ((8, 3), 2)]⟩, [8], [(8, 3)], [9], [snap]⟩,
        [41], [(8, 3)], false, ⟨123, 456, -9, 7, 8⟩, []⟩
  | _ => false
