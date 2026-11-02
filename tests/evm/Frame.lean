import EthLib.EVM.Runner
import EthLib.EVM.Proofs.Memory.Allocation

open EthLib.EVM
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def initial (code : ByteArray) (gas : Nat) : Frame.State :=
  ⟨code, 0, Stack.empty, gas, Memory.Allocation.empty, Memory.Allocation.empty_valid⟩

-- The STOP byte is at position five, and executing it advances the counter.
/-- info: ([5], 0, 6) -/
#guard_msgs in
#eval match Runner.run 4 (initial ⟨#[0x60, 2, 0x60, 3, 0x01, 0x00]⟩ 9) with
    | .stopped s => (s.stack.val.map BitVec.toNat, s.gas, s.pc)
    | _ => ([], 0, 0)

-- End of code stops without advancing the counter.
example : match Runner.run 1 (initial ⟨#[]⟩ 0) with
    | .stopped s => s.pc = 0 ∧ s.gas = 0
    | _ => False := by cbv

-- PUSH2 pads its missing low byte with zero.
/-- info: ([512], 3) -/
#guard_msgs in
#eval match Runner.run 2 (initial ⟨#[0x61, 0x02]⟩ 3) with
    | .stopped s => (s.stack.val.map BitVec.toNat, s.pc)
    | _ => ([], 0)

-- An assigned instruction outside the slice is tooling unsupported.
example : match Runner.run 1 (initial ⟨#[0x02]⟩ 0) with
    | .unsupported _ .mul => True
    | _ => False := by cbv

-- An unassigned instruction is exceptional.
example : match Runner.run 1 (initial ⟨#[0x0c]⟩ 9) with
    | .exception _ .invalidOpcode => True
    | _ => False := by cbv

-- Fuel exhaustion is not an EVM exception.
example : match Runner.run 0 (initial ⟨#[0x00]⟩ 9) with
    | .exhausted _ => True
    | _ => False := by cbv

-- POP checks stack underflow before gas.
example : match Runner.run 1 (initial ⟨#[0x50]⟩ 0) with
    | .exception _ .stackUnderflow => True
    | _ => False := by cbv

-- DUP checks gas before stack underflow.
example : match Runner.run 1 (initial ⟨#[0x80]⟩ 0) with
    | .exception _ .outOfGas => True
    | _ => False := by cbv

-- INVALID is exceptional even when gas is zero.
example : match Runner.run 1 (initial ⟨#[0xfe]⟩ 0) with
    | .exception _ .invalidOpcode => True
    | _ => False := by cbv

-- ADD checks its second operand before charging gas.
example : match Runner.run 1 (initial ⟨#[0x01]⟩ 0) with
    | .exception _ .stackUnderflow => True
    | _ => False := by cbv

-- SWAP checks gas before stack depth.
example : match Runner.run 1 (initial ⟨#[0x90]⟩ 0) with
    | .exception _ .outOfGas => True
    | _ => False := by cbv

def full (code : ByteArray) (gas : Nat) : Frame.State :=
  ⟨code, 0, ⟨List.replicate 1024 0, by simp⟩, gas,
    Memory.Allocation.empty, Memory.Allocation.empty_valid⟩

-- A full stack makes PUSH overflow after its gas check.
/-- info: true -/
#guard_msgs in
#eval match Runner.run 1 (full ⟨#[0x5f]⟩ 2) with
    | .exception _ .stackOverflow => true
    | _ => false

-- Insufficient gas wins over full-stack PUSH overflow.
/-- info: true -/
#guard_msgs in
#eval match Runner.run 1 (full ⟨#[0x5f]⟩ 1) with
    | .exception _ .outOfGas => true
    | _ => false

-- DUP on a full stack reports overflow after charging gas.
/-- info: true -/
#guard_msgs in
#eval match Runner.run 1 (full ⟨#[0x80]⟩ 3) with
    | .exception _ .stackOverflow => true
    | _ => false

def withStack (code : ByteArray) (gas : Nat) (xs : List Word)
    (bound : xs.length ≤ 1024) : Frame.State :=
  ⟨code, 0, ⟨xs, bound⟩, gas, Memory.Allocation.empty, Memory.Allocation.empty_valid⟩

-- POP with an entry and insufficient gas reports out of gas.
/-- info: true -/
#guard_msgs in
#eval match Runner.run 1 (withStack ⟨#[0x50]⟩ 1 [9] (by decide)) with
    | .exception _ .outOfGas => true
    | _ => false

-- ADD with two entries and insufficient gas reports out of gas.
/-- info: true -/
#guard_msgs in
#eval match Runner.run 1 (withStack ⟨#[0x01]⟩ 2 [9, 4] (by decide)) with
    | .exception _ .outOfGas => true
    | _ => false

-- DUP2 copies the second entry to the top.
/-- info: [4, 9, 4] -/
#guard_msgs in
#eval (Runner.run 1 (withStack ⟨#[0x81]⟩ 3 [9, 4] (by decide))).frame.stack.val.map BitVec.toNat

-- SWAP1 exchanges the top two entries.
/-- info: [4, 9] -/
#guard_msgs in
#eval (Runner.run 1 (withStack ⟨#[0x90]⟩ 3 [9, 4] (by decide))).frame.stack.val.map BitVec.toNat

-- With sufficient gas, SWAP1 rejects a one-entry stack.
/-- info: true -/
#guard_msgs in
#eval match Runner.run 1 (withStack ⟨#[0x90]⟩ 3 [9] (by decide)) with
    | .exception _ .stackUnderflow => true
    | _ => false

-- A single STOP needs one step, and extra fuel keeps the result.
example : match Runner.run 1 (initial ⟨#[0x00]⟩ 9) with
    | .stopped s => s.pc = 1 ∧ s.gas = 9
    | _ => False := by cbv
example : match Runner.run 5 (initial ⟨#[0x00]⟩ 9) with
    | .stopped s => s.pc = 1 ∧ s.gas = 9
    | _ => False := by cbv

-- The diagnostic frame keeps gas while exceptional settlement burns it.
example : match Runner.run 1 (initial ⟨#[0xfe]⟩ 9) with
    | .exception s e => s.gas = 9 ∧ Runner.settle (.exception s e) = some (.exceptional 0 e)
    | _ => False := by cbv
example : Runner.settle (Runner.run 1 (initial ⟨#[0x02]⟩ 9)) = none := by cbv
example : Runner.settle (Runner.run 0 (initial ⟨#[0x00]⟩ 9)) = none := by cbv

-- The first step exhausts, and resuming executes STOP.
/-- info: (2, 0) -/
#guard_msgs in
#eval match Runner.run 1 (initial ⟨#[0x5f, 0x00]⟩ 2) with
    | .exhausted s => match Runner.run 1 s with
      | .stopped t => (t.pc, t.gas)
      | _ => (0, 0)
    | _ => (0, 0)

-- Manual revert values are boundary scaffolding, not REVERT execution.
example (s : EthLib.EVM.Frame.State) (gas : Nat) (output : ByteArray) :
    EthLib.EVM.Frame.settle (.revert s gas output) = some (.reverted gas output) := rfl

example (s : EthLib.EVM.Frame.State) (gas : Nat) (output : ByteArray) :
    EthLib.EVM.Runner.settle (.reverted s gas output) = some (.reverted gas output) := rfl

-- The REVERT byte remains an unsupported assigned instruction.
example : match EthLib.EVM.Runner.run 1 (initial ⟨#[0xfd]⟩ 10) with
    | .unsupported _ .revert => True
    | _ => False := by trivial
