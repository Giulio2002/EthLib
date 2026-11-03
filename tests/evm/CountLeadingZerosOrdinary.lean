import EthLib.EVM

open EthLib.EVM

private def env : Environment.Context :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, [], [], BlobFee.amsterdam⟩

private def state (stack : Stack) (gas : Nat) : Frame.State :=
  ⟨⟨#[0x1e]⟩, 0, stack, gas, Memory.Allocation.empty,
    (by intro a _; rfl), ⟨ByteArray.empty, env⟩, ByteArray.empty, { parent := {} }, [], [], false, {}⟩

-- These inputs select zero, one, the highest bit, and every bit set.
/-- info: (true, true, true, true) -/
#guard_msgs in
#eval (Word.countLeadingZeros 0 == 256, Word.countLeadingZeros 1 == 255,
  Word.countLeadingZeros (BitVec.ofNat 256 (2^255)) == 0,
  Word.countLeadingZeros (BitVec.ofNat 256 (2^256-1)) == 0)

-- An empty stack wins over insufficient gas.
/-- info: true -/
#guard_msgs in
#eval match Frame.step (state Stack.empty 0) with
  | .exception _ .stackUnderflow => true
  | _ => false

set_option maxRecDepth 4096 in
-- Pop creates room even when the input stack is full.
/-- info: true -/
#guard_msgs in
#eval match Frame.step (state ⟨List.replicate 1024 1, by simp⟩ 5) with
  | .continue t => t.stack.val.length == 1024 && t.stack.val.head? == some 255 &&
      t.gas == 0 && t.pc == 1 && t.context.environment.blobFeeSchedule.updateFraction.val == BlobFee.amsterdam.updateFraction.val
  | _ => false

-- The mixed program keeps the supplied Amsterdam schedule.
/-- info: true -/
#guard_msgs in
#eval match Runner.run 4 { state ⟨[1, 0], by decide⟩ 10 with
    code := ⟨#[0x01, 0x1e, 0x58, 0x00]⟩ } with
  | .stopped t => t.stack.val == [2, 255] && t.pc == 4 && t.gas == 0 &&
      t.context.environment.blobFeeSchedule.updateFraction.val == BlobFee.amsterdam.updateFraction.val
  | _ => false

-- A present operand with four gas fails the later gas check.
/-- info: true -/
#guard_msgs in
#eval match Frame.step (state ⟨[1], by decide⟩ 4) with
  | .exception _ .outOfGas => true
  | _ => false

-- Direct helper calls do not inspect code or require an in-bounds PC.
private def directInput : Frame.State :=
  { state ⟨[1, 42], by decide⟩ 12 with
    code := ⟨#[0xfe, 0x00]⟩, pc := 100,
    context := ⟨⟨#[0x12, 0x34]⟩, env⟩, returnData := ⟨#[0xab, 0xcd]⟩ }

-- This equality pins the full output frame, including every preserved field.
example : Frame.clz directInput = .continue
    { directInput with stack := ⟨[255, 42], by decide⟩, gas := 7, pc := 101 } := by
  rfl

/-- info: true -/
#guard_msgs in
#eval match Frame.clz directInput with
  | .continue t => t.stack.val == [255, 42] && t.gas == 7 && t.pc == 101 &&
      t.code == directInput.code && t.context.data == directInput.context.data &&
      t.context.environment.blobFeeSchedule.updateFraction.val == env.blobFeeSchedule.updateFraction.val &&
      decide (t.memory = directInput.memory) && t.returnData == directInput.returnData
  | _ => false

-- Underflow wins when gas is also insufficient, even outside the code.
/-- info: true -/
#guard_msgs in
#eval match Frame.clz { directInput with stack := Stack.empty, gas := 0 } with
  | .exception _ .stackUnderflow => true
  | _ => false

-- A present operand reaches the gas check.
/-- info: true -/
#guard_msgs in
#eval match Frame.clz { directInput with gas := 4 } with
  | .exception _ .outOfGas => true
  | _ => false
