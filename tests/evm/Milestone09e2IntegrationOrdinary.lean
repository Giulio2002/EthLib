import EthLib.EVM

open EthLib.EVM

private def env : Environment.Context :=
  ⟨1, 2, 3, 4, 5, 6, 7, 8, 0, 9, 10, 11, 12, 2314058, [42, 43], [70, 71], BlobFee.cancun⟩

private def state (xs : List Word) (bound : xs.length ≤ 1024) (gas : Nat) : Frame.State :=
  ⟨⟨#[0x40, 0x90, 0x49, 0x43, 0x4a]⟩, 0, ⟨xs, bound⟩, gas,
    Memory.Allocation.empty, (by intro a _; rfl), ⟨⟨#[13]⟩, env⟩, ⟨#[14]⟩, { parent := {} }, [], [], false, {}⟩

/-- info: (true, true, true) -/
#guard_msgs in
#eval (match Runner.run 5 (state [7, 1, 99] (by decide) 37) with
  | .exhausted t => t.stack.val == [2, 8, 43, 71, 99] && t.gas == 7 && t.pc == 5 &&
      t.context.data == (⟨#[13]⟩ : ByteArray) && t.returnData == (⟨#[14]⟩ : ByteArray) &&
      t.context.environment.blockHashes == [70, 71] && t.memory == Memory.Allocation.empty
  | _ => false,
  match Runner.run 5 (state [] (by decide) 37) with
  | .exception _ .stackUnderflow => true | _ => false,
  match Runner.run 5 (state [7, 1] (by decide) 19) with
  | .exception _ .outOfGas => true | _ => false)
