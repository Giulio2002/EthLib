import EthLib.EVM

open EthLib.EVM

private def env : Environment.Context :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10000000, [], [], BlobFee.amsterdam⟩

private def state : Frame.State :=
  ⟨⟨#[0x4a]⟩, 0, Stack.empty, 2, Memory.Allocation.empty,
    (by intro a _; rfl), ⟨ByteArray.empty, env⟩, ByteArray.empty, { parent := {} }, [], []⟩

-- The expected prices are calculated from the integer recurrence independently.
/-- info: (true, true, true) -/
#guard_msgs in
#eval (BlobFee.calculateBlobGasPrice 10000000 == 19,
  BlobFee.calculateWith BlobFee.amsterdam 10000000 == 2,
  match Frame.step state with
  | .continue t => t.stack.val == [2] && t.pc == 1 && t.gas == 0
  | _ => false)

-- The adjacent Amsterdam inputs straddle the U256 fee boundary.
/-- info: (true, true) -/
#guard_msgs in
#eval (decide (BlobFee.calculateWith BlobFee.amsterdam 2073394370 < 2 ^ 256),
  decide (2 ^ 256 ≤ BlobFee.calculateWith BlobFee.amsterdam 2073394371))

-- The helper accepts unrelated code and an out-of-range program counter.
/-- info: true -/
#guard_msgs in
#eval match Frame.blobBaseFee { state with code := ⟨#[0xfe]⟩, pc := 100 } with
  | .continue t => t.stack.val == [2] && t.pc == 101
  | _ => false

-- Actual frame results on each side of the conversion boundary.
/-- info: (true, true) -/
#guard_msgs in
#eval let below := { env with excessBlobGas := 2073394370 }
  let above := { env with excessBlobGas := 2073394371 }
  (match Frame.step { state with context := ⟨ByteArray.empty, below⟩ } with
    | .continue t => t.stack.val == [BitVec.ofNat 256
        115792085157819435616670057335491363320393331960321608070891430301789171348051]
    | _ => false,
   match Frame.step { state with context := ⟨ByteArray.empty, above⟩ } with
    | .continue t => t.stack.val == [BitVec.ofNat 256
        5829964806082053124667545066972881423056981539420084007468235127343652]
    | _ => false)
