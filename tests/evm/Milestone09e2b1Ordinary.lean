import EthLib.EVM

open EthLib.EVM

private def env : Environment.Context :=
  ⟨1, 2, 3, 4, 5, 6, 7, 8, 0, 9, 10, 11, 12, 0,
    [BitVec.ofNat 256 (2^255 + 0x1234), 0xabcdef], [], BlobFee.cancun⟩

private def state (xs : List Word) (bound : xs.length ≤ 1024) (gas : Nat) : Frame.State :=
  ⟨⟨#[0x00]⟩, 100, ⟨xs, bound⟩, gas, Memory.Allocation.empty,
    (by intro a _; rfl), ⟨⟨#[1, 2]⟩, env⟩, ⟨#[3, 4]⟩, { parent := {} }, [], []⟩

/-- info: (true, true, true, true, true) -/
#guard_msgs in
#eval (Environment.blobHash env 0 == BitVec.ofNat 256 (2^255 + 0x1234),
  Environment.blobHash env 1 == 0xabcdef,
  Environment.blobHash env 2 == 0,
  Environment.blobHash env (BitVec.ofNat 256 (2^256 - 1)) == 0,
  Environment.blobHash { env with blobVersionedHashes := [] } 0 == 0)

/-- info: true -/
#guard_msgs in
#eval let s := state [0, 55] (by decide) 3
  match Frame.blobHash s with
  | .continue t => t.stack.val == [BitVec.ofNat 256 (2^255 + 0x1234), 55] &&
      t.pc == 101 && t.gas == 0 && t.context.environment.blobVersionedHashes == env.blobVersionedHashes &&
      t.context.data == s.context.data && t.memory == s.memory && t.returnData == s.returnData
  | _ => false

/-- info: (true, true, true) -/
#guard_msgs in
#eval (match Frame.blobHash (state [] (by decide) 0) with
    | .exception _ .stackUnderflow => true | _ => false,
  match Frame.blobHash (state [0] (by decide) 2) with
    | .exception _ .outOfGas => true | _ => false,
  match Frame.blobHash (state (List.replicate 1024 0) (by simp only [List.length_replicate, Nat.le_refl]) 3) with
    | .continue t => t.stack.val.length == 1024 | _ => false)

/-- info: true -/
#guard_msgs in
#eval match Word.ofBytesBE ⟨#[0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x12, 0x34]⟩ with
  | .ok w => Environment.blobHash env 0 == w
  | .error _ => false
