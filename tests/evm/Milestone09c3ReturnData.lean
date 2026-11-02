import EthLib.EVM.Proofs.Frame.Memory
import EthLib.EVM.Proofs.Runner

open EthLib.EVM

private def frame (code data ret : ByteArray) (gas : Nat) (xs : List Word)
    (bound : xs.length ≤ 1024) : Frame.State :=
  ⟨code, 0, ⟨xs, bound⟩, gas, Memory.Allocation.empty,
    Memory.Allocation.empty_valid, ⟨data⟩, ret⟩

private def copy (ret : ByteArray) (gas : Nat) (xs : List Word)
    (bound : xs.length ≤ 1024) : Frame.Outcome :=
  Frame.step (frame ⟨#[0x3e]⟩ ⟨#[99]⟩ ret gas xs bound)

-- Size observes return data, including an empty buffer.
/-- info: ([3], [0]) -/
#guard_msgs in
#eval let size := fun ret => match Frame.step (frame ⟨#[0x3d, 0xaa]⟩ ⟨#[1]⟩ ret 2 [] (by decide)) with
    | .continue s => s.stack.val.map BitVec.toNat | _ => []
  (size ⟨#[4, 5, 6]⟩, size ByteArray.empty)

-- The exact end is valid, including the zero-length range.
/-- info: (true, true, true, true, true) -/
#guard_msgs in
#eval let ret := ByteArray.mk #[1, 2, 3]
  (match copy ret 9 [0, 1, 2] (by decide) with
    | .continue s => Memory.readRange s.memory.store 0 2 == [2, 3] | _ => false,
   match copy ret 3 [0, 3, 0] (by decide) with | .continue _ => true | _ => false,
   match copy ret 3 [0, 4, 0] (by decide) with | .exception _ .outOfBoundsRead => true | _ => false,
   match copy ret 9 [0, 3, 1] (by decide) with | .exception _ .outOfBoundsRead => true | _ => false,
   match copy ret 0 [0, 4, 1] (by decide) with | .exception _ .outOfGas => true | _ => false)

-- Missing operands precede both gas and bounds checks.
/-- info: (true, true, true) -/
#guard_msgs in
#eval let fail := fun xs (h : xs.length ≤ 1024) => match copy ByteArray.empty 0 xs h with
    | .exception _ .stackUnderflow => true | _ => false
  (fail [] (by decide), fail [0] (by decide), fail [0, 0] (by decide))

-- Full-width offsets do not wrap, and unpayable destinations are charged before allocation.
/-- info: (true, true, true, true) -/
#guard_msgs in
#eval let max := BitVec.allOnes 256
  (match copy ⟨#[1]⟩ 9 [0, max, 1] (by decide) with | .exception _ .outOfBoundsRead => true | _ => false,
   match copy ⟨#[1]⟩ 3 [0, max, 0] (by decide) with | .exception _ .outOfBoundsRead => true | _ => false,
   match copy ⟨#[1]⟩ 100 [max, 0, 1] (by decide) with | .exception _ .outOfGas => true | _ => false,
   match copy ⟨#[1]⟩ 100 [0, 0, max] (by decide) with | .exception _ .outOfGas => true | _ => false)

-- Copy charges rounded words and expands destination memory only.
/-- info: ([true, true, true, true], [true, true, true, true]) -/
#guard_msgs in
#eval let ret := ByteArray.mk (Array.replicate 64 7)
  let cases := [(1, 9), (31, 9), (32, 9), (33, 15)]
  let good := cases.map fun (n, gas) => match copy ret gas [0, 16, BitVec.ofNat 256 n] (by simp) with
    | .continue s => s.gas == 0 && s.memory.words == (n + 31) / 32
    | _ => false
  let short := cases.map fun (n, gas) => match copy ret (gas - 1) [0, 16, BitVec.ofNat 256 n] (by simp) with
    | .exception _ .outOfGas => true | _ => false
  (good, short)

-- The ordinary runner sees copied bytes, MSIZE and GAS with distinct calldata.
/-- info: (true, true, true) -/
#guard_msgs in
#eval let s := frame ⟨#[0x3e, 0x51, 0x59, 0x5a]⟩ ⟨#[99]⟩ ⟨#[0x12, 0x34]⟩ 16 [0, 0, 2, 0] (by decide)
  match Runner.run 4 s with
  | .exhausted t => (t.stack.val == [0, 32, BitVec.ofNat 256 (0x1234 * 256 ^ 30)],
      t.context.data == s.context.data, t.returnData == s.returnData)
  | _ => (false, false, false)

-- A consumer derives the source bound, exact bytes and preservation from execution.
example (s t : Frame.State) (x y z : Word) (xs : List Word)
    (at_ : Frame.At s (some .returndatacopy))
    (items : s.stack.val = x :: y :: z :: xs) (run : Frame.step s = .continue t) :
    t.returnData = s.returnData ∧ y.toNat + z.toNat ≤ s.returnData.size := by
  exact ⟨Frame.continue_returnData_unchanged run, (Frame.returnDataCopy_actual s t x y z xs at_ items run).2.1⟩

example (fuel : Nat) (s : Frame.State) : (Runner.run fuel s).frame.returnData = s.returnData :=
  Runner.run_returnData_unchanged fuel s

example (s : Frame.State) (x y : Word) (xs : List Word)
    (at_ : Frame.At s (some .returndatacopy))
    (next : ∃ h : s.pc + 1 < s.code.size, Opcode.decode s.code[s.pc + 1] = some .mload)
    (items : s.stack.val = x :: y :: (32 : Word) :: x :: xs)
    (bound : y.toNat + 32 ≤ s.returnData.size)
    (gas : Gas.inputCopyCost s.memory.words x.toNat 32 +
      (3 + Gas.rangeCost (max s.memory.words (Memory.Allocation.requiredWords x.toNat 32)) x.toNat 32) ≤ s.gas) :
    ∃ t u w, Frame.step s = .continue t ∧ Frame.step t = .continue u ∧ u.stack.val = w :: xs ∧
      w.toNat = EthLib.Precompiles.Modexp.bytesToNat ((s.returnData.data.toList.drop y.toNat).take 32) :=
  Frame.returnDataCopy_then_mload_program s x y xs at_ next items bound gas

-- Size charges before checking stack capacity.
/-- info: (true, true) -/
#guard_msgs in
#eval let full : Stack := ⟨List.replicate 1024 0, by rw [List.length_replicate]⟩
  let s := frame ⟨#[0x3d]⟩ ByteArray.empty ⟨#[1]⟩ 1 [] (by decide)
  (match Frame.step { s with stack := full } with | .exception _ .outOfGas => true | _ => false,
   match Frame.step { s with stack := full, gas := 2 } with | .exception _ .stackOverflow => true | _ => false)

-- A failed bounds check retains the diagnostic memory and settles as exceptional.
/-- info: (true, true, true) -/
#guard_msgs in
#eval let memory := Memory.Allocation.write Memory.Allocation.empty 0 [9, 9, 9, 9, 9]
  let s : Frame.State := ⟨⟨#[0x3e]⟩, 0, ⟨[1, 3, 1], by decide⟩, 6,
    memory, Memory.Allocation.write_valid_for_frame _ _ _ Memory.Allocation.empty_valid,
    ⟨⟨#[99]⟩⟩, ⟨#[1, 2, 3]⟩⟩
  match Frame.step s with
  | .exception input .outOfBoundsRead =>
    (input.memory == s.memory, input.returnData == s.returnData,
      match Frame.settle (.exception input .outOfBoundsRead) with
      | some (.exceptional 0 .outOfBoundsRead) => true | _ => false)
  | _ => (false, false, false)

-- Copy into an existing allocation preserves bytes outside the destination.
/-- info: ([9, 2, 3, 9, 9], true) -/
#guard_msgs in
#eval let memory := Memory.Allocation.write Memory.Allocation.empty 0 [9, 9, 9, 9, 9]
  let s : Frame.State := ⟨⟨#[0x3e]⟩, 0, ⟨[1, 1, 2], by decide⟩, 6,
    memory, Memory.Allocation.write_valid_for_frame _ _ _ Memory.Allocation.empty_valid,
    ⟨⟨#[99]⟩⟩, ⟨#[1, 2, 3]⟩⟩
  match Frame.step s with
  | .continue t => ((Memory.readRange t.memory.store 0 5).map UInt8.toNat,
      t.code == s.code && t.context.data == s.context.data && t.returnData == s.returnData)
  | _ => ([], false)

example (s : Frame.State) (x y z : Word) (xs : List Word)
    (at_ : Frame.At s (some .returndatacopy))
    (items : s.stack.val = x :: y :: z :: xs)
    (gas : Gas.inputCopyCost s.memory.words x.toNat z.toNat ≤ s.gas)
    (bad : s.returnData.size < y.toNat + z.toNat) :
    Frame.step s = .exception s .outOfBoundsRead :=
  Frame.rule_sound (.returnDataCopyBounds s x y z xs at_ items gas bad)

-- An empty range before the end succeeds without expanding memory.
/-- info: true -/
#guard_msgs in
#eval match copy ⟨#[1, 2, 3]⟩ 3 [BitVec.allOnes 256, 2, 0] (by decide) with
  | .continue s => s.memory.words == 0 | _ => false

example (s t : Frame.State) (x y z : Word) (xs : List Word)
    (at_ : Frame.At s (some .returndatacopy))
    (items : s.stack.val = x :: y :: z :: xs) (run : Frame.step s = .continue t) :
    ∃ h : y.toNat + z.toNat ≤ s.returnData.size,
      ∀ i, (hi : i < z.toNat) → Memory.readByte t.memory.store (x.toNat + i) =
        s.returnData[y.toNat + i]'(by omega) := by
  obtain ⟨bound, _, _, _, _, _, _, _, _, bytes, _⟩ :=
    Frame.returnDataCopy_actual_output s t x y z xs at_ items run
  exact ⟨bound, bytes⟩

example (s t : Frame.State) (at_ : Frame.At s (some .returndatasize))
    (run : Frame.step s = .continue t) (bound : s.returnData.size < Word.modulus) :
    ∃ w, t.stack.val = w :: s.stack.val ∧ w.toNat = s.returnData.size := by
  exact Frame.step_observation_stack_exact s t .returndatasize at_ run bound
