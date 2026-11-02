import EthLib.EVM

open EthLib.EVM

-- The first copy pads; the second copies a distinct return buffer without padding.
/-- info: (true, true, true, true, true) -/
#guard_msgs in
#eval
  let code : ByteArray := ⟨#[0x37, 0x3e, 0x51, 0x90, 0x51]⟩
  let data : ByteArray := ⟨#[0x12, 0x34]⟩
  let ret : ByteArray := ⟨Array.replicate 32 0xab⟩
  let s : Frame.State := ⟨code, 0, ⟨[0, 0, 32, 32, 0, 32, 0, 32], by decide⟩,
    100, Memory.Allocation.empty, (by intro a _h; rfl), ⟨data, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, [], [], BlobFee.cancun⟩⟩, ret⟩
  let good := match Runner.run 5 s with
    | .exhausted t => (Memory.readRange t.memory.store 0 32 == [0x12, 0x34] ++ List.replicate 30 0 &&
        Memory.readRange t.memory.store 32 32 == List.replicate 32 0xab &&
        t.code == code && t.context.data == data && t.returnData == ret)
    | _ => false
  let bad := { s with stack := ⟨[32, 1, 32], by decide⟩, pc := 1 }
  let rejection := match Runner.run 1 bad with | .exception _ .outOfBoundsRead => true | _ => false
  let settlement := match Runner.settle (Runner.run 1 bad) with | some (.exceptional 0 .outOfBoundsRead) => true | _ => false
  let low := { bad with gas := 0 }
  let priority := match Runner.run 1 low with | .exception _ .outOfGas => true | _ => false
  let lowSettlement := match Runner.settle (Runner.run 1 low) with | some (.exceptional 0 .outOfGas) => true | _ => false
  (good, rejection, settlement, priority, lowSettlement)
