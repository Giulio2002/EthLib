import EthLib.EVM.Runner

open EthLib.EVM

private theorem emptyValid : Memory.Allocation.Valid Memory.Allocation.empty := by
  intro _ _
  rfl

private instance : DecidableEq BlobFee.Schedule := by
  intro a b
  cases a with
  | mk a => cases b with | mk b =>
    by_cases h : a = b
    · subst b; exact isTrue rfl
    · exact isFalse (fun eq => h (by cases eq; rfl))

deriving instance DecidableEq for Environment.Context
deriving instance DecidableEq for CallData.Context

private def frame (code : ByteArray) (pc gas : Nat) (xs : List Word) : Frame.State :=
  ⟨code, pc, if h : xs.length ≤ 1024 then ⟨xs, h⟩ else Stack.empty, gas,
    Memory.Allocation.empty, emptyValid,
    ⟨⟨#[0xaa]⟩, ⟨1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, [15], [16], BlobFee.cancun⟩⟩,
    ⟨#[0xcc]⟩, { parent := {} }, []⟩

private def result (f : Frame.State → Frame.Outcome) (input : Frame.State)
    (pc gas : Nat) (xs : List Word) : Bool :=
  match f input with
  | .continue s => s.pc == pc && s.gas == gas && s.stack.val == xs &&
      s.code == input.code && decide (s.memory = input.memory) &&
      decide (s.context = input.context) && s.returnData == input.returnData
  | _ => false

private def failed (out : Frame.Outcome) (error : Frame.Exception) : Bool :=
  match out with
  | .exception _ e => e == error
  | _ => false

-- These direct calls do not require an opcode at the program counter.
/-- info: [true, true, true, true, true, true] -/
#guard_msgs in
#eval [
  result Frame.dupn (frame ⟨#[0x00, 0x80]⟩ 0 3 (List.range 17 |>.map (BitVec.ofNat 256))) 2 0
    (16 :: (List.range 17 |>.map (BitVec.ofNat 256))),
  result Frame.swapn (frame ⟨#[0x00, 0x80]⟩ 0 3 (List.range 18 |>.map (BitVec.ofNat 256))) 2 0
    (17 :: (List.range' 1 16 |>.map (BitVec.ofNat 256)) ++ [0]),
  result Frame.exchange (frame ⟨#[0x00, 0x9d]⟩ 0 3 [0, 1, 2, 3]) 2 0 [0, 1, 3, 2],
  failed (Frame.dupn (frame ⟨#[0, 0x5b]⟩ 0 2 []) ) .outOfGas,
  failed (Frame.swapn (frame ⟨#[0, 0x5b]⟩ 0 3 [])) .invalidParameter,
  failed (Frame.exchange (frame ⟨#[]⟩ 100 3 [])) .stackUnderflow
]

-- Execution distinguishes opcode dispatch, invalid data, depth, and capacity.
/-- info: [true, true, true, true, true, true, true, true] -/
#guard_msgs in
#eval [
  result Frame.step (frame ⟨#[0xe6, 0x80]⟩ 0 3 (List.replicate 17 7)) 2 0
    (List.replicate 18 7),
  result Frame.step (frame ⟨#[0xe7, 0x80]⟩ 0 3 (List.replicate 18 7)) 2 0
    (List.replicate 18 7),
  result Frame.step (frame ⟨#[0xe8, 0x9d]⟩ 0 3 [0, 1, 2, 3]) 2 0 [0, 1, 3, 2],
  result Frame.dupn (frame ⟨#[0, 0x5a]⟩ 0 3 (List.replicate 235 7)) 2 0
    (List.replicate 236 7),
  failed (Frame.dupn (frame ⟨#[0, 0x5a]⟩ 0 3 (List.replicate 234 7))) .stackUnderflow,
  failed (Frame.dupn (frame ⟨#[0, 0x80]⟩ 0 3 (List.replicate 1024 7))) .stackOverflow,
  failed (Frame.exchange (frame ⟨#[0, 0x52]⟩ 0 2 [])) .outOfGas,
  failed (Frame.exchange (frame ⟨#[0, 0x52]⟩ 0 3 [])) .invalidParameter
]

-- An absent immediate reads as zero even when the helper PC is past the code.
/-- info: [true, true, true] -/
#guard_msgs in
#eval [
  result Frame.dupn (frame ⟨#[0x00]⟩ 100 3 (List.replicate 146 7)) 102 0
    (List.replicate 147 7),
  result Frame.swapn (frame ⟨#[0x00]⟩ 100 3 (List.replicate 146 7)) 102 0
    (List.replicate 146 7),
  result Frame.exchange (frame ⟨#[0x00]⟩ 100 3 (List.replicate 146 7)) 102 0
    (List.replicate 146 7)
]

-- The bounded runner executes all three instructions before stopping.
/-- info: true -/
#guard_msgs in
#eval Id.run do
  let code : ByteArray := ⟨#[0xe6, 0x80, 0xe7, 0x80, 0xe8, 0x9d, 0x00]⟩
  let input := frame code 0 9 ([1, 2, 3] ++ List.replicate 14 7)
  match Runner.run 4 input with
  | .stopped s =>
    return s.pc == 7 && s.gas == 0 && s.stack.val == ([7, 1, 3, 2] ++ List.replicate 14 7) &&
      s.code == input.code && decide (s.memory = input.memory) &&
      decide (s.context = input.context) && s.returnData == input.returnData
  | _ => return false
