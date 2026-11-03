import EthLib.EVM.Runner
import EthLib.EVM.Proofs.Memory.Allocation

open EthLib.EVM

private def frame (code : ByteArray) (pc gas : Nat) (xs : List Word) : Frame.State :=
  ⟨code, pc, if h : xs.length ≤ 1024 then ⟨xs, h⟩ else Stack.empty, gas,
    Memory.Allocation.empty, Memory.Allocation.empty_valid, ⟨ByteArray.empty, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, [], [], BlobFee.cancun⟩⟩, ByteArray.empty, { parent := {} }⟩

private def continued (s : Frame.State) (pc gas : Nat) (xs : List Word) : Bool :=
  match Frame.step s with
  | .continue t => t.pc == pc && t.gas == gas && t.stack.val == xs &&
      t.code == s.code && t.memory == s.memory
  | _ => false

private def failed (s : Frame.State) (e : Frame.Exception) : Bool :=
  match Frame.step s with
  | .exception _ reason => reason == e
  | _ => false

-- These cases exercise the source check order and the scanner on actual steps.
/-- info: [("forward", true),
 ("backward", true),
 ("zero", true),
 ("beyond", true),
 ("max word", true),
 ("non destination", true),
 ("push payload", true),
 ("truncated push", true),
 ("invalid before target", true),
 ("eip8024 invalid immediate target", true),
 ("eip8024 push masks target", true),
 ("false invalid", true),
 ("false max", true),
 ("condition two", true),
 ("true invalid", true),
 ("jump exact gas", true),
 ("jump short gas", true),
 ("jumpi exact gas", true),
 ("jumpi short gas", true),
 ("jumpdest exact gas", true),
 ("jumpdest short gas", true),
 ("jump empty before gas", true),
 ("jumpi empty before gas", true),
 ("jumpi one before gas", true),
 ("gas before destination", true),
 ("jumpi gas before destination", true)] -/
#guard_msgs in
#eval [
  ("forward", continued (frame ⟨#[0x56, 0x00, 0x5b]⟩ 0 8 [2, 17]) 2 0 [17]),
  ("backward", continued (frame ⟨#[0x5b, 0x56]⟩ 1 8 [0, 17]) 0 0 [17]),
  ("zero", continued (frame ⟨#[0x5b, 0x56]⟩ 1 9 [0]) 0 1 []),
  ("beyond", failed (frame ⟨#[0x56, 0x5b]⟩ 0 8 [2]) .invalidJumpDestination),
  ("max word", failed (frame ⟨#[0x56, 0x5b]⟩ 0 8 [-1]) .invalidJumpDestination),
  ("non destination", failed (frame ⟨#[0x56, 0x00]⟩ 0 8 [1]) .invalidJumpDestination),
  ("push payload", failed (frame ⟨#[0x56, 0x60, 0x5b]⟩ 0 8 [2]) .invalidJumpDestination),
  ("truncated push", failed (frame ⟨#[0x56, 0x62, 0x5b]⟩ 0 8 [2]) .invalidJumpDestination),
  ("invalid before target", continued (frame ⟨#[0x56, 0x0c, 0x5b]⟩ 0 8 [2]) 2 0 []),
  ("eip8024 invalid immediate target", continued (frame ⟨#[0x56, 0xe6, 0x5b]⟩ 0 8 [2]) 2 0 []),
  ("eip8024 push masks target", failed (frame ⟨#[0x56, 0xe6, 0x60, 0x5b]⟩ 0 8 [3]) .invalidJumpDestination),
  ("false invalid", continued (frame ⟨#[0x57, 0x00]⟩ 0 10 [1, 0, 42]) 1 0 [42]),
  ("false max", continued (frame ⟨#[0x57]⟩ 0 10 [-1, 0]) 1 0 []),
  ("condition two", continued (frame ⟨#[0x57, 0x5b]⟩ 0 10 [1, 2, 7]) 1 0 [7]),
  ("true invalid", failed (frame ⟨#[0x57, 0x00]⟩ 0 10 [1, 2]) .invalidJumpDestination),
  ("jump exact gas", continued (frame ⟨#[0x56, 0x5b]⟩ 0 8 [1]) 1 0 []),
  ("jump short gas", failed (frame ⟨#[0x56, 0x5b]⟩ 0 7 [1]) .outOfGas),
  ("jumpi exact gas", continued (frame ⟨#[0x57, 0x5b]⟩ 0 10 [1, 1]) 1 0 []),
  ("jumpi short gas", failed (frame ⟨#[0x57, 0x5b]⟩ 0 9 [1, 1]) .outOfGas),
  ("jumpdest exact gas", continued (frame ⟨#[0x5b]⟩ 0 1 [5]) 1 0 [5]),
  ("jumpdest short gas", failed (frame ⟨#[0x5b]⟩ 0 0 [5]) .outOfGas),
  ("jump empty before gas", failed (frame ⟨#[0x56]⟩ 0 0 []) .stackUnderflow),
  ("jumpi empty before gas", failed (frame ⟨#[0x57]⟩ 0 0 []) .stackUnderflow),
  ("jumpi one before gas", failed (frame ⟨#[0x57]⟩ 0 0 [1]) .stackUnderflow),
  ("gas before destination", failed (frame ⟨#[0x56]⟩ 0 7 [-1]) .outOfGas),
  ("jumpi gas before destination", failed (frame ⟨#[0x57]⟩ 0 9 [-1, 1]) .outOfGas)
]

private def branchCode : ByteArray := ⟨#[0x60, 2, 0x60, 7, 0x57, 0x60, 0xff, 0x5b, 0x60, 42, 0x00]⟩
private def filledMemory : Memory.Allocation.State := Memory.Allocation.write Memory.Allocation.empty 0 [0xab]
private def branchFrame : Frame.State :=
  ⟨branchCode, 0, Stack.empty, 20, filledMemory,
    Memory.Allocation.write_valid _ _ _ Memory.Allocation.empty_valid, ⟨ByteArray.empty, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, [], [], BlobFee.cancun⟩⟩, ByteArray.empty, { parent := {} }⟩

-- The taken branch skips PUSH1 0xff and preserves nonempty memory and code.
/-- info: true -/
#guard_msgs in
#eval match Runner.run 6 branchFrame with
  | .stopped s => s.pc == 11 && s.gas == 0 && s.stack.val == [42] &&
      s.code == branchCode && s.memory == filledMemory &&
      Memory.readByte s.memory.store 0 == 0xab
  | _ => false

private def loopFrame : Frame.State := frame ⟨#[0x5b, 0x5f, 0x56]⟩ 0 11 []

-- One loop consumes 11 gas; fuel exhaustion is distinct from the next out-of-gas step.
/-- info: (true, true) -/
#guard_msgs in
#eval (match Runner.run 3 loopFrame with
  | .exhausted s => s.pc == 0 && s.gas == 0
  | _ => false,
  match Runner.run 4 loopFrame with
  | .exception s .outOfGas => s.pc == 0 && s.gas == 0
  | _ => false)

-- EIP-8024 Specification: the jump reaches 0x5b after the invalid immediate.
/-- info: true -/
#guard_msgs in
#eval match Runner.run 4 (frame ⟨#[0x60, 0x04, 0x56, 0xe6, 0x5b]⟩ 0 12 []) with
  | .stopped s => s.pc == 5 && s.gas == 0 && s.stack.val == []
  | _ => false
