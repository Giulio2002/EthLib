import EthLib.EVM.Runner
import EthLib.EVM.Proofs.Memory.Allocation

open EthLib.EVM

private def initial (stack : Stack) (gas : Nat) : Frame.State :=
  ⟨⟨#[0x20]⟩, 0, stack, gas, Memory.Allocation.empty,
    Memory.Allocation.empty_valid, ⟨ByteArray.empty, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, [], [], BlobFee.cancun⟩⟩, ByteArray.empty, { parent := {} }⟩

-- Keccak team's ShortMsgKAT_256.txt, Len = 0.
/-- info: (89477152217924674838424037953991966239322087453347756267410168184682657981552, 0, 1, 0) -/
#guard_msgs in
#eval match Frame.step (initial ⟨[0, 0], by decide⟩ 30) with
  | .continue s => (s.stack.val.head!.toNat, s.gas, s.pc, s.memory.words)
  | _ => (0, 0, 0, 0)

-- Both operands are checked before gas.
example : match Frame.step (initial Stack.empty 0) with
  | .exception _ .stackUnderflow => True
  | _ => False := by cbv

example : match Frame.step (initial ⟨[0], by decide⟩ 0) with
  | .exception _ .stackUnderflow => True
  | _ => False := by cbv

-- A huge offset with nonzero length is rejected before materializing memory.
example : match Frame.step (initial ⟨[BitVec.allOnes 256, 1], by decide⟩ 100) with
  | .exception _ .outOfGas => True
  | _ => False := by cbv

-- The zero-length range ignores even the largest word offset.
/-- info: (true, 0, 0) -/
#guard_msgs in
#eval match Frame.step (initial ⟨[BitVec.allOnes 256, 0], by decide⟩ 30) with
  | .continue s => (s.stack.val.head!.toNat == 89477152217924674838424037953991966239322087453347756267410168184682657981552, s.memory.words, s.gas)
  | _ => (false, 1, 1)

-- One byte costs one hash word and one newly allocated memory word.
example : match Frame.step (initial ⟨[0, 1], by decide⟩ 38) with
  | .exception _ .outOfGas => True
  | _ => False := by cbv

-- Keccak team's ShortMsgKAT_256.txt, Len = 8, message CC.
private def oneByte : Frame.State :=
  let memory := Memory.Allocation.write Memory.Allocation.empty 7 [0xcc]
  { (initial ⟨[7, 1], by decide⟩ 36) with memory, memoryValid := Memory.Allocation.write_valid_for_frame _ _ _ Memory.Allocation.empty_valid }

/-- info: (107956879965704228734569137041262965338817142023000182365167206346872019422090, 0, 1) -/
#guard_msgs in
#eval match Frame.step oneByte with
  | .continue s => (s.stack.val.head!.toNat, s.gas, s.memory.words)
  | _ => (0, 0, 0)

-- Rounded hash and expansion charges at word and sponge-rate boundaries.
/-- info: [39, 39, 48, 75, 75, 75] -/
#guard_msgs in
#eval [31, 32, 33, 135, 136, 137].map (Gas.keccakCost 0 0)

-- Exact gas covers hashing one zero-filled byte from unallocated memory.
/-- info: (true, 0, 1) -/
#guard_msgs in
#eval match Frame.step (initial ⟨[0, 1], by decide⟩ 39) with
  | .continue s => (s.stack.val.head! == Frame.digestWord
      (EthLib.Cryptography.Hash.Keccak.keccak256 ⟨#[0]⟩), s.gas, s.memory.words)
  | _ => (false, 1, 0)

-- These comparisons test memory adaptation against the same shared primitive.
-- They are not independent cryptographic known answers.
private def boundary (length cost words : Nat) : Bool := Id.run do
  let stack : Stack := ⟨[0, BitVec.ofNat 256 length], by simp⟩
  let exactState := initial stack cost
  let shortState := initial stack (cost - 1)
  let digest := Frame.digestWord (EthLib.Cryptography.Hash.Keccak.keccak256
    ⟨Array.replicate length 0⟩)
  let exactOK := match Frame.step exactState with
    | .continue s => s.gas == 0 && s.pc == 1 && s.memory.words == words &&
        s.stack.val == [digest]
    | _ => false
  let shortOK := match Frame.step shortState with
    | .exception _ .outOfGas => true
    | _ => false
  return exactOK && shortOK

-- Exact and one-short gas execute at word and sponge-rate boundaries.
/-- info: [true, true, true, true, true, true] -/
#guard_msgs in
#eval [(31, 39, 1), (32, 39, 1), (33, 48, 2), (135, 75, 5),
  (136, 75, 5), (137, 75, 5)].map fun (n, gas, words) => boundary n gas words
