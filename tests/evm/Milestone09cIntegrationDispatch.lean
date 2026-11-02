import EthLib.EVM.Proofs.Opcode
import EthLib.EVM.Frame.Rules
import EthLib.EVM.Proofs.Memory.Allocation

open EthLib.EVM

-- This range list is independent of the decoder and matches the supported slice.
private def supported (n : Nat) : Bool :=
  n ≤ 0x0b || (0x10 ≤ n && n ≤ 0x1d) || n == 0x20 || (n == 0x30 || (0x32 ≤ n && n ≤ 0x3a)) || n == 0x3d || n == 0x3e || (0x40 ≤ n && n ≤ 0x46) || n == 0x48 || n == 0x49 || n == 0x4a || n == 0x50 || n == 0x51 || n == 0x52 || n == 0x53 ||
  (0x56 ≤ n && n ≤ 0x5b) || n == 0x5e || (0x5f ≤ n && n ≤ 0x9f)

private instance (op : Opcode) : Decidable (Frame.Unsupported op) := by
  cases op <;> simp [Frame.Unsupported] <;> infer_instance

private def state (b : UInt8) : Frame.State :=
  ⟨⟨#[b]⟩, 0, ⟨[2, 1, 3], by decide⟩, 10000,
    Memory.Allocation.empty, Memory.Allocation.empty_valid, ⟨ByteArray.empty, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, [], [], BlobFee.cancun⟩⟩, ByteArray.empty⟩

-- Check the independent reference, classification predicate and executable dispatch.
private def check (n : Nat) : Bool := Id.run do
  let b := UInt8.ofNat n
  let decoded := Opcode.decode b
  if decoded != Proofs.Opcode.reference.lookup b then return false
  let cls := match decoded with
    | none | some .invalid => 0
    | some op => if decide (Frame.Unsupported op) then 1 else 2
  let expected := if n == 0xfe then 0 else if supported n then 2
    else if (Proofs.Opcode.reference.lookup b).isSome then 1 else 0
  let actual := match Frame.step (state b) with
    | .exception _ .invalidOpcode => 0
    | .unsupported _ _ => 1
    | _ => 2
  return cls == expected && actual == expected

-- The enumeration is unique and complete, and every byte matches all three views.
/-- info: (256, 256, true) -/
#guard_msgs in
#eval ((List.range 256).length, ((List.range 256).eraseDups).length,
  (List.range 256).all check)

-- Count the actual decoder and step classifications across unique bytes.
/-- info: (125, 23, 107, 1) -/
#guard_msgs in
#eval Id.run do
  let mut supportedCount := 0
  let mut unsupportedCount := 0
  let mut unassignedCount := 0
  let mut invalidCount := 0
  for n in List.range 256 do
    let byte := UInt8.ofNat n
    match Opcode.decode byte with
    | none => unassignedCount := unassignedCount + 1
    | some .invalid => invalidCount := invalidCount + 1
    | some op =>
      if decide (Frame.Unsupported op) then
        unsupportedCount := unsupportedCount + 1
      else
        supportedCount := supportedCount + 1
  return (supportedCount, unsupportedCount, unassignedCount, invalidCount)

-- Count the outcomes produced by executable dispatch.
/-- info: (125, 23, 108) -/
#guard_msgs in
#eval Id.run do
  let mut executed := 0
  let mut unsupported := 0
  let mut invalid := 0
  for n in List.range 256 do
    match Frame.step (state (UInt8.ofNat n)) with
    | .exception _ .invalidOpcode => invalid := invalid + 1
    | .unsupported _ _ => unsupported := unsupported + 1
    | _ => executed := executed + 1
  return (executed, unsupported, invalid)
