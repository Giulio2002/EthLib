import EthLib.EVM

open EthLib.EVM

example (environment : Environment.Context) (data : ByteArray) : CallData.Context :=
  ⟨data, environment⟩

example (address : Environment.Address) : Word := Environment.addressWord address

private def metadata : Environment.Context := ⟨11, 22, 33, 44, 55, 0, 0, 0, 0, 0, 0, 0⟩
private def input : Frame.State :=
  ⟨⟨#[0xfe]⟩, 99, ⟨[7, 8], by decide⟩, 5, Memory.Allocation.empty,
    by intro a _; rfl, ⟨⟨#[9]⟩, metadata⟩, ⟨#[10]⟩⟩

-- The helper is callable independently of the instruction at the program counter.
/-- info: true -/
#guard_msgs in
#eval match Frame.observe input (fun gas => 2^256 + gas + 13) with
  | .continue t =>
    t.code == input.code && t.pc == 100 && t.gas == 3 &&
    t.stack.val == [16, 7, 8] && t.memory == input.memory &&
    t.context.data == input.context.data &&
    t.context.environment.currentTarget == metadata.currentTarget &&
    t.context.environment.origin == metadata.origin &&
    t.context.environment.caller == metadata.caller &&
    t.context.environment.value == metadata.value &&
    t.context.environment.gasPrice == metadata.gasPrice &&
    t.returnData == input.returnData
  | _ => false

private def fullStack : Stack := ⟨List.replicate 1024 0, by simp only [List.length_replicate, Nat.le_refl]⟩

/-- info: (true, true) -/
#guard_msgs in
#eval (match Frame.observe { input with gas := 1, stack := fullStack } (fun _ => 0) with
    | .exception _ .outOfGas => true | _ => false,
  match Frame.observe { input with gas := 2, stack := fullStack } (fun _ => 0) with
    | .exception _ .stackOverflow => true | _ => false)

-- The ordinary root executes all five observations in one bounded program.
/-- info: true -/
#guard_msgs in
#eval let s : Frame.State := { input with code := ⟨#[0x30, 0x32, 0x33, 0x34, 0x3a, 0x00]⟩, pc := 0, gas := 10 }
  match Runner.run 6 s with
  | .stopped t => t.pc == 6 && t.gas == 0 && t.stack.val == [55, 44, 33, 22, 11, 7, 8] &&
    t.memory == s.memory && t.context.data == s.context.data && t.returnData == s.returnData
  | _ => false
