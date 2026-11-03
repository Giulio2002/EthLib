import EthLib.EVM

open EthLib.EVM

private def env : Environment.Context :=
  ⟨0, 0, 0, 0, 0, 0, 0, 17, 42, 0, 0, 0, 0, 0, [], [], BlobFee.amsterdam⟩

private def input : Frame.State :=
  ⟨⟨#[0xfe]⟩, 100, ⟨[9], by decide⟩, 5, Memory.Allocation.empty,
    (by intro a _; rfl), ⟨⟨#[1, 2]⟩, env⟩, ⟨#[3, 4]⟩, { parent := {} }, [], []⟩

-- The helper observes the supplied slot even outside the code.
example : Frame.observe input (fun _ => input.context.environment.slotNumber.val) =
    .continue { input with stack := ⟨[42, 9], by decide⟩, pc := 101, gas := 3 } := by
  rfl

-- Gas is checked before a full stack can overflow.
set_option maxRecDepth 16384 in
example : Frame.observe { input with stack := ⟨List.replicate 1024 0, by simp⟩, gas := 0 }
    (fun _ => 42) = .exception { input with stack := ⟨List.replicate 1024 0, by simp⟩, gas := 0 } .outOfGas := by
  rfl

set_option maxRecDepth 16384 in
example : Frame.observe { input with stack := ⟨List.replicate 1024 0, by simp⟩, gas := 2 }
    (fun _ => 42) = .exception { input with stack := ⟨List.replicate 1024 0, by simp⟩, gas := 2 } .stackOverflow := by
  rfl

-- Slot and number are distinct, and the Amsterdam schedule is preserved.
/-- info: true -/
#guard_msgs in
#eval match Runner.run 3 { input with code := ⟨#[0x4b, 0x43, 0]⟩, pc := 0, gas := 4 } with
  | .stopped t => t.stack.val == [17, 42, 9] && t.pc == 3 && t.gas == 0 &&
      t.context.environment.blobFeeSchedule.updateFraction.val == BlobFee.amsterdam.updateFraction.val
  | _ => false

/-- info: (true, true) -/
#guard_msgs in
#eval ((Frame.observationWord 0).toNat == 0,
  (Frame.observationWord (2^64 - 1)).toNat == 2^64 - 1)

-- Both endpoints of the source U64 domain reach the stack.
/-- info: (true, true) -/
#guard_msgs in
#eval Id.run do
  let check (slot : Fin (2^64)) :=
    let context := { env with slotNumber := slot }
    let s := { input with code := ⟨#[0x4b]⟩, pc := 0, gas := 2, context := ⟨⟨#[1, 2]⟩, context⟩ }
    match Frame.step s with
    | .continue t => t.stack.val.head?.map BitVec.toNat == some slot.val
    | _ => false
  return (check 0, check ⟨2^64 - 1, by decide⟩)
