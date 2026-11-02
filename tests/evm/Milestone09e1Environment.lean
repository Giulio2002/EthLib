import EthLib.EVM.Proofs.Runner.Environment

open EthLib.EVM

private def env : Environment.Context := ⟨1, 2, 3, BitVec.ofNat 256 (2^255), BitVec.ofNat 256 (2^255 + 7), 0, 0, 0, 0, 0, 0, 0, []⟩
private def frame (op : UInt8) (gas : Nat) (xs : List Word) (h : xs.length ≤ 1024) : Frame.State :=
  ⟨⟨#[op]⟩, 0, ⟨xs, h⟩, gas, Memory.Allocation.empty,
    by intro a _; rfl, ⟨⟨#[7]⟩, env⟩, ⟨#[8]⟩⟩

private def read (op : UInt8) : Option Nat :=
  match Frame.step (frame op 2 [] (by decide)) with
  | .continue s => s.stack.val.head?.map BitVec.toNat
  | _ => none

/-- info: (some 1, some 2, some 3, true, true) -/
#guard_msgs in
#eval (read 0x30, read 0x32, read 0x33, read 0x34 == some (2^255), read 0x3a == some (2^255 + 7))

/-- info: (true, true) -/
#guard_msgs in
#eval let full := List.replicate 1024 (0 : Word)
  (match Frame.step (frame 0x30 1 full (by simp only [full, List.length_replicate, Nat.le_refl])) with | .exception _ .outOfGas => true | _ => false,
   match Frame.step (frame 0x30 2 full (by simp only [full, List.length_replicate, Nat.le_refl])) with | .exception _ .stackOverflow => true | _ => false)

example (fuel : Nat) (s : Frame.State) :
    (Runner.run fuel s).frame.context.environment = s.context.environment := by
  rw [Runner.run_context_unchanged]

/-- info: (0, true) -/
#guard_msgs in
#eval ((Environment.addressWord (0 : Environment.Address)).toNat,
  (Environment.addressWord ⟨2^160 - 1, by decide⟩).toNat == 2^160 - 1)

/-- info: (true, true, true) -/
#guard_msgs in
#eval let maxAddress : Environment.Address := ⟨2^160 - 1, by decide⟩
  let s := frame 0x30 2 [] (by decide)
  let zero := { s with context := ⟨s.context.data, { env with currentTarget := 0 }⟩ }
  let max := { s with context := ⟨s.context.data, { env with currentTarget := maxAddress }⟩ }
  (match Frame.step zero with | .continue t => t.stack.val == [0] | _ => false,
   match Frame.step max with | .continue t => t.stack.val == [Environment.addressWord maxAddress] | _ => false,
   match Runner.run 0 max with | .exhausted t => t.context.environment.currentTarget == maxAddress | _ => false)

/-- info: (true, true) -/
#guard_msgs in
#eval let bad := frame 0xfe 2 [] (by decide)
  let unknown := frame 0x31 2 [] (by decide)
  (match Runner.run 1 bad with | .exception t _ => t.context.environment.origin == env.origin | _ => false,
   match Runner.run 1 unknown with | .unsupported t _ => t.context.environment.caller == env.caller | _ => false)
