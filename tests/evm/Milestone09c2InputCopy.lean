import EthLib.EVM.Proofs.Frame.Memory
import EthLib.EVM.Runner

open EthLib.EVM

private def frame (code data : ByteArray) (gas : Nat) (xs : List Word)
    (bound : xs.length ≤ 1024) : Frame.State :=
  ⟨code, 0, ⟨xs, bound⟩, gas, Memory.Allocation.empty,
    Memory.Allocation.empty_valid, ⟨data, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, [], [], BlobFee.cancun⟩⟩, ByteArray.empty, { parent := {} }, []⟩

-- Data and code are distinct, and each copy starts at source offset one.
/-- info: ([34, 51, 0, 0], [170, 187, 0, 0]) -/
#guard_msgs in
#eval let data := ByteArray.mk #[0x11, 0x22, 0x33]
  let run := fun code => match Frame.step (frame code data 9 [2, 1, 4] (by decide)) with
    | .continue s => (Memory.readRange s.memory.store 2 4).map UInt8.toNat
    | _ => []
  (run ⟨#[0x37, 0xaa, 0xbb]⟩, run ⟨#[0x39, 0xaa, 0xbb]⟩)

-- A maximum source offset copies zeros at the normal destination cost.
/-- info: (0, 1, [0, 0, 0]) -/
#guard_msgs in
#eval match Frame.step (frame ⟨#[0x37]⟩ ⟨#[1, 2]⟩ 9
    [1, BitVec.allOnes 256, 3] (by decide)) with
  | .continue s => (s.gas, s.memory.words, (Memory.readRange s.memory.store 1 3).map UInt8.toNat)
  | _ => (1, 0, [])

-- Empty input copies at maximum offsets leave allocation unchanged.
/-- info: (0, 0) -/
#guard_msgs in
#eval match Frame.step (frame ⟨#[0x39]⟩ ByteArray.empty 3
    [BitVec.allOnes 256, BitVec.allOnes 256, 0] (by decide)) with
  | .continue s => (s.gas, s.memory.words) | _ => (1, 1)

-- Underflow is checked before gas, and large allocations fail before reading.
/-- info: (true, true, true, true, true, true) -/
#guard_msgs in
#eval let fail := fun xs (h : xs.length ≤ 1024) => match Frame.step (frame ⟨#[0x37]⟩ ByteArray.empty 0 xs h) with
    | .exception _ .stackUnderflow => true | _ => false
  (fail [] (by decide), fail [0] (by decide), fail [0, 0] (by decide),
   match Frame.step (frame ⟨#[0x37]⟩ ByteArray.empty 8 [0, 0, 1] (by decide)) with
    | .exception _ .outOfGas => true | _ => false,
   match Frame.step (frame ⟨#[0x39]⟩ ByteArray.empty 100 [BitVec.allOnes 256, 0, 1] (by decide)) with
    | .exception _ .outOfGas => true | _ => false,
   match Frame.step (frame ⟨#[0x37]⟩ ByteArray.empty 100 [0, 0, BitVec.allOnes 256] (by decide)) with
    | .exception _ .outOfGas => true | _ => false)

-- Rounded word charges and allocations at the 32-byte boundary.
/-- info: ([0, 0, 0, 0, 0], [0, 1, 1, 1, 2]) -/
#guard_msgs in
#eval let cases := [(0, 3), (1, 9), (31, 9), (32, 9), (33, 15)]
  let outcomes := cases.map fun (length, gas) =>
    match Frame.step (frame ⟨#[0x37]⟩ ⟨#[9]⟩ gas [0, 0, BitVec.ofNat 256 length] (by simp)) with
    | .continue s => (s.gas, s.memory.words) | _ => (999, 999)
  (outcomes.map Prod.fst, outcomes.map Prod.snd)

-- Executing copy followed by MLOAD exposes the copied and padded source bytes.
/-- info: (true, 0) -/
#guard_msgs in
#eval match Runner.run 2 (frame ⟨#[0x37, 0x51]⟩ ⟨#[0x12, 0x34]⟩ 12
    [0, 0, 2, 0] (by decide)) with
  | .exhausted s => (s.stack.val == [BitVec.ofNat 256 (0x1234 * 256 ^ 30)], s.gas)
  | _ => (false, 1)

-- MSIZE and GAS see only the destination expansion and remaining gas.
/-- info: ([0, 32], 0) -/
#guard_msgs in
#eval match Runner.run 3 (frame ⟨#[0x39, 0x59, 0x5a]⟩ ByteArray.empty 13
    [0, BitVec.allOnes 256, 1] (by decide)) with
  | .exhausted s => (s.stack.val.map BitVec.toNat, s.gas) | _ => ([], 1)

-- A proof consumer applies the actual-success converse to arbitrary context.
example (s t : Frame.State) (x y z : Word) (xs : List Word)
    (at_ : Frame.At s (some .calldatacopy))
    (items : s.stack.val = x :: y :: z :: xs) (run : Frame.step s = .continue t)
    (i : Nat) (hi : i < z.toNat) :
    Memory.readByte t.memory.store (x.toNat + i) =
      PushImmediate.byteAt s.context.data (y.toNat + i) := by
  exact (Frame.inputCopy_success_output s t .calldata x y z xs at_ items run).2.2.2.2.2.2.1 i hi

-- Exact, partial, and past-end reads preserve bytes outside the destination.
/-- info: ([[9, 1, 2, 3, 9], [9, 3, 0, 0, 9], [9, 0, 0, 0, 9]], true) -/
#guard_msgs in
#eval let memory := Memory.Allocation.write Memory.Allocation.empty 0 [9, 9, 9, 9, 9]
  let run := fun (src : Word) =>
    let s : Frame.State := ⟨⟨#[0x37]⟩, 0, ⟨[1, src, 3], by simp⟩, 6,
      memory, Memory.Allocation.write_valid_for_frame _ _ _ Memory.Allocation.empty_valid,
      ⟨⟨#[1, 2, 3]⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, [], [], BlobFee.cancun⟩⟩, ByteArray.empty, { parent := {} }, []⟩
    match Frame.step s with
    | .continue t => ((Memory.readRange t.memory.store 0 5).map UInt8.toNat,
      t.code == s.code && t.context.data == s.context.data)
    | _ => ([], false)
  ([(run 0).1, (run 2).1, (run 3).1], (run 2).2)

-- A proof consumer applies the copy-and-load contract for arbitrary input.
example (s t u : Frame.State) (x y : Word) (xs : List Word)
    (at_ : Frame.At s (some .calldatacopy))
    (items : s.stack.val = x :: y :: (32 : Word) :: x :: xs)
    (copy : Frame.step s = .continue t) (loadAt : Frame.At t (some .mload))
    (load : Frame.step t = .continue u) :
    ∃ w, u.stack.val = w :: xs ∧ w.toNat =
      EthLib.Execution.Precompiles.Modexp.bytesToNat (CallData.readRange s.context.data y.toNat 32) := by
  exact Frame.inputCopy_then_mload_actual s t u .calldata x y xs at_ items copy loadAt load

-- The constructive program contract supplies both execution steps.
example (s : Frame.State) (x y : Word) (xs : List Word)
    (at_ : Frame.At s (some .calldatacopy))
    (next : ∃ h : s.pc + 1 < s.code.size, Opcode.decode s.code[s.pc + 1] = some .mload)
    (items : s.stack.val = x :: y :: (32 : Word) :: x :: xs)
    (gas : Gas.inputCopyCost s.memory.words x.toNat 32 +
      (3 + Gas.rangeCost (max s.memory.words (Memory.Allocation.requiredWords x.toNat 32))
        x.toNat 32) ≤ s.gas) :
    ∃ t u w, Frame.step s = .continue t ∧ Frame.step t = .continue u ∧
      u.stack.val = w :: xs ∧ w.toNat =
        EthLib.Execution.Precompiles.Modexp.bytesToNat (CallData.readRange s.context.data y.toNat 32) := by
  exact Frame.inputCopy_then_mload_program s .calldata x y xs at_ next items gas
