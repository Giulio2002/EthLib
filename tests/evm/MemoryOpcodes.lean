import EthLib.EVM.Runner
import EthLib.EVM.Proofs.Memory.Allocation

open EthLib.EVM

def memoryFrame (code : ByteArray) (gas : Nat) (xs : List Word)
    (bound : xs.length ≤ 1024) : Frame.State :=
  ⟨code, 0, ⟨xs, bound⟩, gas, Memory.Allocation.empty, Memory.Allocation.empty_valid, ⟨ByteArray.empty, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, [], [], BlobFee.cancun⟩⟩, ByteArray.empty, { parent := {} }, []⟩

-- Offset is the top operand; the unaligned write crosses a word boundary.
/-- info: ([0, 64, 4660], 0) -/
#guard_msgs in
#eval match Runner.run 5 (memoryFrame ⟨#[0x52, 0x51, 0x59, 0x5a, 0x00]⟩ 16
    [31, 4660, 31] (by decide)) with
  | .stopped s => (s.stack.val.map BitVec.toNat, s.gas)
  | _ => ([], 0)

-- A second read of allocated zero memory costs only its base gas.
/-- info: ([0, 0], 0) -/
#guard_msgs in
#eval match Runner.run 3 (memoryFrame ⟨#[0x51, 0x51, 0x00]⟩ 9 [0, 0] (by decide)) with
  | .stopped s => (s.stack.val.map BitVec.toNat, s.gas)
  | _ => ([], 1)

-- Store8 takes the low byte, and an untouched neighbor remains zero.
/-- info: (52, 0) -/
#guard_msgs in
#eval match Runner.run 1 (memoryFrame ⟨#[0x53]⟩ 6 [1, 0x1234] (by decide)) with
  | .exhausted s => ((Memory.readByte s.memory.store 1).toNat,
      (Memory.readByte s.memory.store 0).toNat)
  | _ => (0, 1)

-- Underflow precedes gas charging.
example : match Runner.run 1 (memoryFrame ⟨#[0x52]⟩ 0 [1] (by decide)) with
  | .exception _ .stackUnderflow => True
  | _ => False := by cbv

-- One gas below the first-word store cost fails before changing memory.
example : match Runner.run 1 (memoryFrame ⟨#[0x52]⟩ 5 [0, 1] (by decide)) with
  | .exception s .outOfGas => s.memory = Memory.Allocation.empty
  | _ => False := by cbv

-- The maximum 256-bit offset is charged without wrapping its end address.
/-- info: true -/
#guard_msgs in
#eval match Runner.run 1 (memoryFrame ⟨#[0x51]⟩ 1000000
    [BitVec.ofNat 256 (2^256 - 1)] (by decide)) with
  | .exception s .outOfGas => s.memory.words == 0
  | _ => false

-- Exact first-word gas succeeds and leaves no gas.
/-- info: (0, 1) -/
#guard_msgs in
#eval match Runner.run 1 (memoryFrame ⟨#[0x52]⟩ 6 [0, 1] (by decide)) with
  | .exhausted s => (s.gas, s.memory.words)
  | _ => (1, 0)

-- Two byte stores overwrite one address and preserve a neighboring word byte.
/-- info: (170, 204, 0, 32) -/
#guard_msgs in
#eval match Runner.run 3 (memoryFrame ⟨#[0x52, 0x53, 0x53]⟩ 12
    [0, 0xaa00, 31, 0xbb, 31, 0xcc] (by decide)) with
  | .exhausted s => ((Memory.readByte s.memory.store 30).toNat,
      (Memory.readByte s.memory.store 31).toNat,
      (Memory.readByte s.memory.store 29).toNat, s.memory.words * 32)
  | _ => (0, 0, 1, 0)

-- A small gas reserve fails after both store operands have been checked.
example : match Runner.run 1 (memoryFrame ⟨#[0x53]⟩ 2 [0, 255] (by decide)) with
  | .exception s .outOfGas => s.memory = Memory.Allocation.empty
  | _ => False := by cbv
