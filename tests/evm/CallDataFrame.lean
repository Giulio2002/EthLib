import EthLib.EVM.Proofs

open EthLib.EVM
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

private def data : ByteArray := ⟨#[0x12, 0x34, 0x56]⟩
private def frame (op : UInt8) (gas : Nat) (xs : List Word) (bound : xs.length ≤ 1024)
    (input : ByteArray) : Frame.State :=
  ⟨⟨#[op]⟩, 0, ⟨xs, bound⟩, gas, Memory.Allocation.empty,
    Memory.Allocation.empty_valid, ⟨input, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, []⟩⟩, ByteArray.empty⟩

private def head (op : UInt8) (gas : Nat) (xs : List Word) (bound : xs.length ≤ 1024)
    (input : ByteArray) : Option Nat :=
  match Frame.step (frame op gas xs bound input) with
  | .continue t => t.stack.val.head?.map BitVec.toNat
  | _ => none

-- Each fixed value describes the observed bytes in big-endian order.
example : head 0x35 3 [0] (by decide) data = some (0x123456 * 256 ^ 29) := by decide
example : head 0x35 3 [1] (by decide) data = some (0x3456 * 256 ^ 30) := by decide
example : head 0x35 3 [31] (by decide) data = some 0 := by decide
example : head 0x35 3 [32] (by decide) data = some 0 := by decide
example : head 0x35 3 [-1] (by decide) data = some 0 := by decide
example : head 0x35 3 [0] (by decide) ByteArray.empty = some 0 := by decide
example : head 0x36 2 [] (by decide) data = some 3 := by decide
example : head 0x38 2 [] (by decide) data = some 1 := by decide

-- A short stack fails before gas for load; size charges before checking capacity.
example : match Frame.step (frame 0x35 0 [] (by decide) data) with
  | .exception _ .stackUnderflow => True | _ => False := by cbv
example : match Frame.step (frame 0x35 2 [0] (by decide) data) with
  | .exception _ .outOfGas => True | _ => False := by cbv
example : match Frame.step (frame 0x36 1 (List.replicate 1024 0) (by decide) data) with
  | .exception _ .outOfGas => True | _ => False := by cbv
example : match Frame.step (frame 0x36 2 (List.replicate 1024 0) (by decide) data) with
  | .exception _ .stackOverflow => True | _ => False := by cbv
/-- info: (1024, 0, true) -/
#guard_msgs in
#eval match Frame.step (frame 0x35 3 (List.replicate 1024 0) (by decide) data) with
  | .continue t => (t.stack.val.length, t.memory.words, t.context.data == data)
  | _ => (0, 0, false)

example (s t : Frame.State) (x : Word) (xs : List Word)
    (at_ : Frame.At s (some .calldataload)) (items : s.stack.val = x :: xs)
    (run : Frame.step s = .continue t) :
    t.context = s.context ∧ t.memory = s.memory ∧
      t.stack.val = CallData.load s.context x :: xs := by
  have h := (Frame.calldataload_actual s t x xs at_ items run).2
  exact ⟨h.2.2.2.2.2.1, h.2.1, h.2.2.2.2.1⟩

example (fuel : Nat) (s : Frame.State) : (Runner.run fuel s).frame.context = s.context :=
  Runner.run_context_unchanged fuel s

private def exact32 : ByteArray := ⟨#[0x80, 1, 2, 3, 4, 5, 6, 7,
  8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
  24, 25, 26, 27, 28, 29, 30, 0xab]⟩

example : head 0x35 3 [31] (by decide) exact32 = some (0xab * 256 ^ 31) := by decide
example : head 0x35 3 [32] (by decide) exact32 = some 0 := by decide
example : head 0x35 3 [33] (by decide) exact32 = some 0 := by decide
example : head 0x35 3 [0] (by decide) exact32 =
    some 0x800102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1eab := by decide

example : match Frame.step (frame 0x38 1 (List.replicate 1024 0) (by decide) data) with
  | .exception _ .outOfGas => True | _ => False := by cbv
example : match Frame.step (frame 0x38 2 (List.replicate 1024 0) (by decide) data) with
  | .exception _ .stackOverflow => True | _ => False := by cbv

-- MSTORE retains the same message input while changing memory.
/-- info: true -/
#guard_msgs in
#eval match Frame.step (frame 0x52 6 [0, 0xab] (by decide) data) with
  | .continue t => t.context.data == data && t.memory.words == 1
  | _ => false

example (s t : Frame.State) (at_ : Frame.At s (some .calldatasize))
    (run : Frame.step s = .continue t) (bound : s.context.data.size < Word.modulus) :
    ∃ w, t.stack.val = w :: s.stack.val ∧ w.toNat = s.context.data.size := by
  simpa [Frame.Observation.opcode, Frame.Observation.value] using
    Frame.step_observation_stack_exact s t .calldatasize at_ run bound

example (s t : Frame.State) (at_ : Frame.At s (some .codesize))
    (run : Frame.step s = .continue t) :
    ∃ w, t.stack.val = w :: s.stack.val ∧ w.toNat = s.code.size % Word.modulus := by
  simpa [Frame.Observation.opcode, Frame.Observation.value] using
    Frame.step_observation_stack_mod s t .codesize at_ run
