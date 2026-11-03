import EthLib.EVM

open EthLib.EVM

private def env : Environment.Context :=
  ⟨1, 2, 3, 4, 5, 6, 7, 8, 0, 9, 10, 11, 12, 2314058, [42], [], BlobFee.cancun⟩

private def state (xs : List Word) (bound : xs.length ≤ 1024) (gas : Nat) : Frame.State :=
  ⟨⟨#[0x4a, 0x00]⟩, 0, ⟨xs, bound⟩, gas, Memory.Allocation.empty,
    (by intro a _; rfl), ⟨⟨#[]⟩, env⟩, ⟨#[]⟩, { parent := {} }, [], []⟩

/-- info: (true, true, true, true, true, true) -/
#guard_msgs in
#eval (BlobFee.calculateBlobGasPrice 0 == 1,
  BlobFee.calculateBlobGasPrice 1 == 1,
  BlobFee.calculateBlobGasPrice 2314057 == 1,
  BlobFee.calculateBlobGasPrice 2314058 == 2,
  BlobFee.calculateBlobGasPrice 6676954 == 7,
  BlobFee.calculateBlobGasPrice 10000000 == 19)

/-- info: true -/
#guard_msgs in
#eval match Frame.step (state [9] (by decide) 2) with
  | .continue t => t.pc == 1 && t.gas == 0 && t.stack.val == [2, 9] &&
      t.context.environment.excessBlobGas == env.excessBlobGas
  | _ => false

/-- info: (true, true) -/
#guard_msgs in
#eval (match Frame.step (state (List.replicate 1024 0) (by simp only [List.length_replicate, Nat.le_refl]) 1) with
    | .exception _ .outOfGas => true | _ => false,
  match Frame.step (state (List.replicate 1024 0) (by simp only [List.length_replicate, Nat.le_refl]) 2) with
    | .exception _ .stackOverflow => true | _ => false)

-- The direct helper does not inspect code or the program counter.
/-- info: true -/
#guard_msgs in
#eval let s := { state [9] (by decide) 2 with code := ⟨#[0xfe]⟩, pc := 100, context := ⟨⟨#[7]⟩, env⟩, returnData := ⟨#[8]⟩ }
  match Frame.blobBaseFee s with
  | .continue t => t.pc == 101 && t.gas == 0 && t.stack.val == [2, 9] &&
      t.code == s.code && t.memory == s.memory && t.returnData == s.returnData &&
      t.context.data == s.context.data &&
      t.context.environment.currentTarget == env.currentTarget &&
      t.context.environment.origin == env.origin && t.context.environment.caller == env.caller &&
      t.context.environment.value == env.value && t.context.environment.gasPrice == env.gasPrice &&
      t.context.environment.coinbase == env.coinbase && t.context.environment.timestamp == env.timestamp &&
      t.context.environment.number == env.number && t.context.environment.prevRandao == env.prevRandao &&
      t.context.environment.gasLimit == env.gasLimit && t.context.environment.chainId == env.chainId &&
      t.context.environment.baseFee == env.baseFee &&
      t.context.environment.excessBlobGas == env.excessBlobGas &&
      t.context.environment.blobVersionedHashes == env.blobVersionedHashes
  | _ => false

-- Gas is checked before stack capacity for the direct helper too.
/-- info: (true, true) -/
#guard_msgs in
#eval let full := List.replicate 1024 (0 : Word)
  let s := { state full (by simp only [full, List.length_replicate, Nat.le_refl]) 1 with
    code := ⟨#[0xfe]⟩, pc := 100 }
  (match Frame.blobBaseFee s with
    | .exception _ .outOfGas => true | _ => false,
   match Frame.blobBaseFee { s with gas := 2 } with
    | .exception _ .stackOverflow => true | _ => false)

-- The adjacent values cross the checked U256 conversion boundary.
/-- info: (true, true, true) -/
#guard_msgs in
#eval (decide (BlobFee.calculateBlobGasPrice 592398315 < 2 ^ 256),
  decide (2 ^ 256 ≤ BlobFee.calculateBlobGasPrice 592398316),
  decide (2 ^ 256 ≤ BlobFee.calculateBlobGasPrice (2 ^ 32)))


-- These adjacent inputs pin the exact and modulo-extension results.
-- The oversized case is a total Lean extension beyond the source U256 conversion.
/-- info: (true, true) -/
#guard_msgs in
#eval let exactEnv := { env with excessBlobGas := 592398315 }
  let largeEnv := { env with excessBlobGas := 592398316 }
  let s := state [9] (by decide) 2
  (match Frame.step { s with context := ⟨s.context.data, exactEnv⟩ } with
    | .continue t => match t.stack.val with
      | w :: [9] => w.toNat == 115792071961871597569864401767843993244140375666330206955159735174071991568500
      | _ => false
    | _ => false,
   match Frame.step { s with context := ⟨s.context.data, largeEnv⟩ } with
    | .continue t => match t.stack.val with
      | w :: [9] => w.toNat == 17409909295229528157535056316183729965443689596646594698923390584776054
      | _ => false
    | _ => false)
