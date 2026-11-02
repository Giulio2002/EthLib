import EthLib.EVM

open EthLib.EVM

private def metadata : Environment.Context :=
  ⟨1, 2, 3, 4, 5, ⟨2^160 - 1, by decide⟩, BitVec.ofNat 256 (2^256 - 1),
    13, 0, BitVec.ofNat 256 (2^255), 17, ⟨2^64 - 1, by decide⟩, 23, 0, [], [], BlobFee.cancun⟩

private def input : Frame.State :=
  ⟨⟨#[0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x48, 0x00]⟩, 0,
    ⟨[99], by decide⟩, 14, Memory.Allocation.empty, (by intro a _; rfl),
    ⟨⟨#[9]⟩, metadata⟩, ⟨#[10]⟩⟩

/-- info: true -/
#guard_msgs in
#eval match Runner.run 8 input with
  | .stopped t => t.pc == 8 && t.gas == 0 &&
    t.stack.val == [23, BitVec.ofNat 256 (2^64 - 1), 17, BitVec.ofNat 256 (2^255),
      13, BitVec.ofNat 256 (2^256 - 1), BitVec.ofNat 256 (2^160 - 1), 99] &&
    t.memory == input.memory && t.returnData == input.returnData &&
    t.context.environment.coinbase == metadata.coinbase
  | _ => false

private def fullStack : Stack := ⟨List.replicate 1024 0, by simp only [List.length_replicate, Nat.le_refl]⟩

/-- info: (true, true) -/
#guard_msgs in
#eval (match Frame.step { input with gas := 1, stack := fullStack } with
    | .exception _ .outOfGas => true | _ => false,
  match Frame.step { input with gas := 2, stack := fullStack } with
    | .exception _ .stackOverflow => true | _ => false)
