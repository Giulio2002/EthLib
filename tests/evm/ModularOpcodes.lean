import EthLib.EVM.Runner
import EthLib.EVM.Proofs.Memory.Allocation

open EthLib.EVM

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def state (op : UInt8) (gas : Nat) (xs : List Word) (bound : xs.length ≤ 1024) : Frame.State :=
  ⟨⟨#[op]⟩, 0, ⟨xs, bound⟩, gas, Memory.Allocation.empty, Memory.Allocation.empty_valid, ⟨ByteArray.empty, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, [], [], BlobFee.cancun⟩⟩, ByteArray.empty⟩

def result (op : UInt8) (gas : Nat) (xs : List Word) (bound : xs.length ≤ 1024) :
    Option (List Word × Nat × Nat) :=
  match Frame.step (state op gas xs bound) with
  | .continue s => some (s.stack.val, s.gas, s.pc)
  | _ => none

def failure (op : UInt8) (gas : Nat) (xs : List Word) (bound : xs.length ≤ 1024) :
    Option Frame.Exception :=
  match Frame.step (state op gas xs bound) with
  | .exception _ e => some e
  | _ => none

-- Distinct operands pin the first two positions and the modulus position.
#guard result 0x08 8 [9, 5, 7] (by simp) == some ([0], 0, 1)
#guard result 0x08 8 [9, 7, 5] (by simp) == some ([1], 0, 1)
#guard result 0x09 8 [9, 5, 11] (by simp) == some ([1], 0, 1)
#guard result 0x09 8 [9, 11, 5] (by simp) == some ([4], 0, 1)
#guard result 0x0a 60 [2, 3] (by simp) == some ([8], 0, 1)
#guard result 0x0a 60 [3, 2] (by simp) == some ([9], 0, 1)

-- Full precision distinguishes reduction from arithmetic wrapped at 256 bits.
#guard result 0x08 8 [-1, 1, 3] (by simp) == some ([1], 0, 1)
#guard result 0x09 8 [BitVec.ofNat 256 (2 ^ 255), 2, 3] (by simp) == some ([1], 0, 1)
#guard result 0x08 8 [9, 5, 0] (by simp) == some ([0], 0, 1)
#guard result 0x09 8 [9, 5, 0] (by simp) == some ([0], 0, 1)

-- Each ternary underflow takes precedence over a zero gas balance.
#guard [0x08, 0x09].all (fun op =>
  failure op 0 [] (by simp) == some .stackUnderflow &&
  failure op 0 [1] (by simp) == some .stackUnderflow &&
  failure op 0 [1, 2] (by simp) == some .stackUnderflow &&
  failure op 7 [1, 2, 3] (by simp) == some .outOfGas)
#guard failure 0x0a 0 [] (by simp) == some .stackUnderflow
#guard failure 0x0a 0 [1] (by simp) == some .stackUnderflow

-- EXP prices the second stack item; changing only the base leaves the cost unchanged.
#guard result 0x0a 10 [0, 0] (by simp) == some ([1], 0, 1)
#guard result 0x0a 60 [7, 1] (by simp) == some ([7], 0, 1)
#guard result 0x0a 60 [1, 255] (by simp) == some ([1], 0, 1)
#guard result 0x0a 110 [1, 256] (by simp) == some ([1], 0, 1)
#guard result 0x0a 110 [2, 256] (by simp) == some ([0], 0, 1)
#guard result 0x0a 1610 [1, -1] (by simp) == some ([1], 0, 1)
#guard result 0x0a 110 [1, 65535] (by simp) == some ([1], 0, 1)
#guard result 0x0a 160 [1, 65536] (by simp) == some ([1], 0, 1)
#guard failure 0x0a 109 [1, 65535] (by simp) == some .outOfGas
#guard failure 0x0a 159 [1, 65536] (by simp) == some .outOfGas
#guard failure 0x0a 9 [0, 0] (by simp) == some .outOfGas
#guard failure 0x0a 59 [1, 1] (by simp) == some .outOfGas
#guard failure 0x0a 59 [1, 255] (by simp) == some .outOfGas
#guard failure 0x0a 109 [1, 256] (by simp) == some .outOfGas
#guard failure 0x0a 1609 [1, -1] (by simp) == some .outOfGas

-- Popping before pushing permits success even at the stack limit.
#guard match Frame.step (state 0x08 8 (List.replicate 1024 0) (by simp)) with
  | .continue s => s.stack.val.length == 1022 && s.gas == 0 && s.pc == 1
  | _ => false
#guard match Frame.step (state 0x09 8 (List.replicate 1024 0) (by simp)) with
  | .continue s => s.stack.val.length == 1022 && s.gas == 0 && s.pc == 1
  | _ => false
#guard match Frame.step (state 0x0a 10 (List.replicate 1024 0) (by simp)) with
  | .continue s => s.stack.val.length == 1023 && s.gas == 0 && s.pc == 1
  | _ => false

-- PUSH values feed ADDMOD, EXP, and MULMOD; STOP retains code and memory.
def program : ByteArray := ⟨#[0x60, 7, 0x60, 5, 0x60, 7, 0x60, 5, 0x60, 9, 0x08, 0x60, 2, 0x0a, 0x09, 0x00]⟩
def start : Frame.State :=
  ⟨program, 0, Stack.empty, 44, Memory.Allocation.empty, Memory.Allocation.empty_valid, ⟨ByteArray.empty, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, [], [], BlobFee.cancun⟩⟩, ByteArray.empty⟩
#guard match Runner.run 10 start with
  | .stopped s => s.stack.val == [5] && s.pc == 16 && s.gas == 0 &&
      s.code == program && decide (s.memory = start.memory)
  | _ => false
