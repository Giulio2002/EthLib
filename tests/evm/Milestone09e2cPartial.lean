import EthLib.EVM

open EthLib.EVM

private def env : Environment.Context :=
  ⟨0, 0, 0, 0, 0, 0, 0, 257, 0, 0, 0, 0, 0, [], [], BlobFee.cancun⟩

private def input (xs : List Word) (bound : xs.length ≤ 1024) (gas : Nat) : Frame.State :=
  ⟨⟨#[0]⟩, 10, ⟨xs, bound⟩, gas, Memory.Allocation.empty,
    (by intro a _; rfl), ⟨ByteArray.empty, env⟩, ByteArray.empty⟩

/-- info: (true, true, true, true, true) -/
#guard_msgs in
#eval (Environment.blockHash [11, 22] 257 256 == 22,
  Environment.blockHash [11, 22] 257 255 == 11,
  Environment.blockHash [11, 22] 257 254 == 0,
  Environment.blockHash [11, 22] 257 257 == 0,
  Environment.blockHash [11, 22] 257 0 == 0)

/-- info: (true, true, true) -/
#guard_msgs in
#eval (match Frame.blockHash (input [] (by decide) 0) [11, 22] with
    | .exception _ .stackUnderflow => true | _ => false,
  match Frame.blockHash (input [256] (by decide) 19) [11, 22] with
    | .exception _ .outOfGas => true | _ => false,
  match Frame.blockHash (input [256, 7] (by decide) 20) [11, 22] with
    | .continue t => t.stack.val == [22, 7] && t.gas == 0 && t.pc == 11
    | _ => false)
