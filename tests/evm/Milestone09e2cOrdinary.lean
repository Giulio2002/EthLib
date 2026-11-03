import EthLib.EVM

open EthLib.EVM

private def hist : List Word := (List.range 256).map (fun n => BitVec.ofNat 256 (n + 1))
private def env (n : Word) (hs : List Word) : Environment.Context :=
  ⟨0, 0, 0, 0, 0, 0, 0, n, 0, 0, 0, 0, 0, 0, [], hs, BlobFee.cancun⟩
private def state (n : Word) (hs : List Word) (xs : List Word)
    (bound : xs.length ≤ 1024) (gas : Nat) : Frame.State :=
  ⟨⟨#[0x40]⟩, 0, ⟨xs, bound⟩, gas, Memory.Allocation.empty,
    (by intro a _; rfl), ⟨ByteArray.empty, env n hs⟩, ByteArray.empty, { parent := {} }, [], [], false, {}, []⟩
private def result (s : Frame.State) : Option Word :=
  match Frame.step s with
  | .continue t => t.stack.val.head?
  | _ => none

/-- info: (true, true, true, true, true, true, true, true) -/
#guard_msgs in
#eval (result (state 257 hist [256] (by decide) 20) == some 256,
  result (state 257 hist [1] (by decide) 20) == some 1,
  result (state 257 hist [0] (by decide) 20) == some 0,
  result (state 257 hist [257] (by decide) 20) == some 0,
  result (state 257 hist [258] (by decide) 20) == some 0,
  result (state 0 [] [0] (by decide) 20) == some 0,
  result (state 2 [0x1234] [0] (by decide) 20) == some 0,
  result (state 256 hist [0] (by decide) 20) == some 1)

/-- info: (true, true, true, true, true) -/
#guard_msgs in
#eval (result (state 1 [0x1234] [0] (by decide) 20) == some 0x1234,
  result (state 257 hist [BitVec.ofNat 256 (2^256 - 1)] (by decide) 20) == some 0,
  result (state (BitVec.ofNat 256 (2^256 - 1)) [0xabcd] [BitVec.ofNat 256 (2^256 - 2)] (by decide) 20) == some 0xabcd,
  match Frame.step (state 1 [3] [] (by decide) 0) with | .exception _ .stackUnderflow => true | _ => false,
  match Frame.step (state 1 [3] [0] (by decide) 19) with | .exception _ .outOfGas => true | _ => false)

/-- info: true -/
#guard_msgs in
#eval let xs := List.replicate 1024 0
  match Frame.step (state 1 [0x1234] xs (by simp only [xs, List.length_replicate, Nat.le_refl]) 20) with
  | .continue t => t.stack.val.length == 1024 && t.stack.val.head? == some 0x1234
  | _ => false

-- The extra oldest entry models the genesis parent in EELS early histories.
/-- info: (true, true) -/
#guard_msgs in
#eval (result (state 1 [0xdead, 0x1234] [0] (by decide) 20) == some 0x1234,
  result (state 2 [0xdead, 0x1234, 0xabcd] [0] (by decide) 20) == some 0x1234)
