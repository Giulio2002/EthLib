import EthLib.EVM.Runner
import EthLib.EVM.Proofs.Memory.Allocation

open EthLib.EVM

private def frame (code : ByteArray) (gas : Nat) (xs : List Word)
    (bound : xs.length ≤ 1024) : Frame.State :=
  ⟨code, 0, ⟨xs, bound⟩, gas, Memory.Allocation.empty, Memory.Allocation.empty_valid, ⟨ByteArray.empty, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, []⟩⟩, ByteArray.empty⟩

-- The three missing-operand cases fail before gas is checked.
example : match Frame.step (frame ⟨#[0x5e]⟩ 0 [] (by decide)) with
  | .exception _ .stackUnderflow => True | _ => False := by cbv
example : match Frame.step (frame ⟨#[0x5e]⟩ 0 [0] (by decide)) with
  | .exception _ .stackUnderflow => True | _ => False := by cbv
example : match Frame.step (frame ⟨#[0x5e]⟩ 0 [0, 0] (by decide)) with
  | .exception _ .stackUnderflow => True | _ => False := by cbv

-- Empty ranges at the largest offsets pay only the base cost.
/-- info: (0, 0) -/
#guard_msgs in
#eval match Frame.step (frame ⟨#[0x5e]⟩ 3
    [BitVec.allOnes 256, BitVec.allOnes 256, 0] (by decide)) with
  | .continue s => (s.gas, s.memory.words) | _ => (1, 1)

-- An unpayable full-width length or offset is rejected without copying.
/-- info: (true, true) -/
#guard_msgs in
#eval (match Frame.step (frame ⟨#[0x5e]⟩ 100 [0, 0, BitVec.allOnes 256] (by decide)) with
  | .exception _ .outOfGas => true | _ => false,
  match Frame.step (frame ⟨#[0x5e]⟩ 100 [BitVec.allOnes 256, 0, 1] (by decide)) with
  | .exception _ .outOfGas => true | _ => false)

-- One byte with one allocated word costs nine gas; one less fails.
/-- info: (true, true) -/
#guard_msgs in
#eval (match Frame.step (frame ⟨#[0x5e]⟩ 9 [0, 0, 1] (by decide)) with
  | .continue s => s.gas == 0 && s.memory.words == 1 | _ => false,
  match Frame.step (frame ⟨#[0x5e]⟩ 8 [0, 0, 1] (by decide)) with
  | .exception _ .outOfGas => true | _ => false)

-- Store bytes, copy an overlapping range, then observe size and remaining gas.
/-- info: ([1, 1, 2, 3, 0], 32, 0) -/
#guard_msgs in
#eval match Runner.run 4 (frame ⟨#[0x53, 0x53, 0x53, 0x5e]⟩ 18
    [0, 1, 1, 2, 2, 3, 1, 0, 3] (by decide)) with
  | .exhausted s => ((List.range 5).map (fun i => (Memory.readByte s.memory.store i).toNat),
      Memory.Allocation.byteSize s.memory, s.gas)
  | _ => ([], 0, 1)

-- Both overlap directions and self-copy retain the original source bytes.
/-- info: ([2, 3, 4, 4], [1, 2, 3, 4]) -/
#guard_msgs in
#eval let base := Memory.Allocation.write Memory.Allocation.empty 0 [1, 2, 3, 4]
  let result := Memory.Allocation.copy base 0 1 3
  let self := Memory.Allocation.copy base 0 0 4
  ((Memory.readRange result.store 0 4).map UInt8.toNat,
   (Memory.readRange self.store 0 4).map UInt8.toNat)

-- A source beyond the allocation supplies zeros and preserves outside bytes.
/-- info: ([9, 0, 0, 0, 0], 96) -/
#guard_msgs in
#eval let base := Memory.Allocation.write Memory.Allocation.empty 0 [9, 8, 7]
  let result := Memory.Allocation.copy base 1 64 3
  ((Memory.readRange result.store 0 5).map UInt8.toNat, Memory.Allocation.byteSize result)

-- MSIZE and GAS observe the copy allocation and its remaining gas.
/-- info: ([0, 32], 0) -/
#guard_msgs in
#eval match Runner.run 3 (frame ⟨#[0x5e, 0x59, 0x5a]⟩ 13 [0, 0, 1] (by decide)) with
  | .exhausted s => (s.stack.val.map BitVec.toNat, s.gas) | _ => ([], 1)

private def seeded (xs : List Word) (bound : xs.length ≤ 1024) : Frame.State :=
  ⟨⟨#[0x5e]⟩, 0, ⟨xs, bound⟩, 6,
    Memory.Allocation.write Memory.Allocation.empty 0 [1, 2, 3, 4],
    Memory.Allocation.write_valid_for_frame _ _ _ Memory.Allocation.empty_valid, ⟨ByteArray.empty, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, []⟩⟩, ByteArray.empty⟩

-- Reverse overlap and self-copy execute against the pre-step snapshot.
/-- info: ([2, 3, 4, 4], [1, 2, 3, 4]) -/
#guard_msgs in
#eval (match Frame.step (seeded [0, 1, 3] (by decide)) with
  | .continue s => (Memory.readRange s.memory.store 0 4).map UInt8.toNat | _ => [],
  match Frame.step (seeded [0, 0, 4] (by decide)) with
  | .continue s => (Memory.readRange s.memory.store 0 4).map UInt8.toNat | _ => [])

-- The source and destination independently determine expansion.
/-- info: (96, 96) -/
#guard_msgs in
#eval (match Frame.step (frame ⟨#[0x5e]⟩ 15 [0, 64, 1] (by decide)) with
  | .continue s => Memory.Allocation.byteSize s.memory | _ => 0,
  match Frame.step (frame ⟨#[0x5e]⟩ 15 [64, 0, 1] (by decide)) with
  | .continue s => Memory.Allocation.byteSize s.memory | _ => 0)

-- The rounded copy charge increases at the 32-byte boundary.
/-- info: ([0, 0, 0, 0], [1, 1, 1, 2]) -/
#guard_msgs in
#eval let cases := [(1, 9), (31, 9), (32, 9), (33, 15)]
  let outcomes := cases.map fun (length, gas) =>
    match Frame.step (frame ⟨#[0x5e]⟩ gas [0, 0, BitVec.ofNat 256 length] (by simp)) with
    | .continue s => (s.gas, s.memory.words) | _ => (999, 999)
  (outcomes.map Prod.fst, outcomes.map Prod.snd)

-- An expanded source supplies zeros and copying leaves the preceding byte intact.
/-- info: ([1, 0, 0, 0, 0], 96) -/
#guard_msgs in
#eval let s : Frame.State := { seeded [1, 64, 3] (by decide) with gas := 12 }
  match Frame.step s with
  | .continue t => ((Memory.readRange t.memory.store 0 5).map UInt8.toNat,
      Memory.Allocation.byteSize t.memory)
  | _ => ([], 0)
