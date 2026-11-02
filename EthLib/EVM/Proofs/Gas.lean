module

public import EthLib.EVM.Gas
public import EthLib.EVM.Proofs.Memory.Allocation

@[expose] public section
namespace EthLib.EVM.Gas

open EthLib.EVM.Memory.Allocation

/-- Charging succeeds exactly when the cost is affordable, with the exact remainder. -/
theorem charge_ok (gas cost remaining : Nat) :
    charge gas cost = .ok remaining ↔ cost ≤ gas ∧ remaining = gas - cost := by
  by_cases h : cost ≤ gas <;> simp [charge, h, eq_comm]

/-- Charging fails exactly when gas is insufficient. -/
theorem charge_error (gas cost : Nat) :
    charge gas cost = .error .outOfGas ↔ gas < cost := by
  by_cases h : cost ≤ gas
  · simp [charge, h, Nat.not_lt.mpr h]
  · simp [charge, h, Nat.lt_of_not_ge h]

/-- Successful charging conserves gas. -/
theorem charge_conservation (gas cost remaining : Nat)
    (h : charge gas cost = .ok remaining) : gas = remaining + cost := by
  obtain ⟨hc, rfl⟩ := (charge_ok _ _ _).mp h
  omega

/-- An exact payment leaves zero gas. -/
theorem charge_exact (cost : Nat) : charge cost cost = .ok 0 := by simp [charge]

/-- Less gas remains insufficient when a larger amount is insufficient. -/
theorem charge_insufficient_mono (gas gas' cost : Nat) (h : gas' ≤ gas)
    (fail : charge gas cost = .error .outOfGas) :
    charge gas' cost = .error .outOfGas := by
  apply (charge_error _ _).2
  have := (charge_error _ _).1 fail
  omega

/-- Total memory cost is monotone in allocated words. -/
theorem memoryCost_mono {a b : Nat} (h : a ≤ b) : memoryCost a ≤ memoryCost b := by
  unfold memoryCost
  have sq : a * a ≤ b * b := Nat.mul_le_mul h h
  have div : a * a / 512 ≤ b * b / 512 := Nat.div_le_div_right sq
  omega

/-- Expansion cost is the exact difference and allocation cannot shrink. -/
theorem expansion_contract (old req : Nat) :
    old ≤ max old req ∧ memoryCost old + expansionCost old req = memoryCost (max old req) := by
  constructor
  · exact Nat.le_max_left _ _
  · have h := memoryCost_mono (Nat.le_max_left old req)
    unfold expansionCost
    omega

/-- Consecutive expansions telescope. -/
theorem expansion_telescope (old a b : Nat) :
    expansionCost old a + expansionCost (max old a) b =
      expansionCost old (max a b) := by
  have h₁ := expansion_contract old a
  have h₂ := expansion_contract (max old a) b
  have h₃ := expansion_contract old (max a b)
  rw [Nat.max_assoc] at h₂
  omega

/-- Empty ranges cost nothing, independently of their offset. -/
theorem rangeCost_zero (old offset : Nat) : rangeCost old offset 0 = 0 := by
  simp [rangeCost, expansionCost, requiredWords]

/-- A repeated requirement costs nothing after its first expansion. -/
theorem expansion_idempotent (old req : Nat) : expansionCost (max old req) req = 0 := by
  simp [expansionCost, Nat.max_assoc]

/-- Two requirements have the same cost in either order. -/
theorem pairCost_comm (old a n b m : Nat) :
    pairCost old a n b m = pairCost old b m a n := by
  simp [pairCost, Nat.max_comm]

/-- A pair charge equals consecutive expansion charges. -/
theorem pairCost_telescope (old a n b m : Nat) :
    pairCost old a n b m = rangeCost old a n +
      rangeCost (max old (requiredWords a n)) b m := by
  exact (expansion_telescope old (requiredWords a n) (requiredWords b m)).symm

/-- Failure returns only an error, before an expanded state is produced. -/
theorem chargeExpand_error (gas : Nat) (s : State) (offset length : Nat) :
    chargeExpand gas s offset length = .error .outOfGas ↔
      gas < rangeCost s.words offset length := by
  by_cases h : rangeCost s.words offset length ≤ gas
  · simp [chargeExpand, charge, h, Nat.not_lt.mpr h]
  · simp [chargeExpand, charge, h, Nat.lt_of_not_ge h]

/-- Success returns the exact remaining gas and the unchanged store at the new size. -/
theorem chargeExpand_ok (gas : Nat) (s : State) (offset length remaining : Nat) (t : State) :
    chargeExpand gas s offset length = .ok (remaining, t) ↔
      rangeCost s.words offset length ≤ gas ∧
      remaining = gas - rangeCost s.words offset length ∧ t = expand s offset length := by
  by_cases h : rangeCost s.words offset length ≤ gas
  · simp [chargeExpand, charge, h, eq_comm]
  · simp [chargeExpand, charge, h]

/-- Successful expansion preserves valid sparse memory. -/
theorem chargeExpand_valid (gas : Nat) (s : State) (offset length remaining : Nat) (t : State)
    (valid : Valid s) (h : chargeExpand gas s offset length = .ok (remaining, t)) : Valid t := by
  obtain ⟨_, _, rfl⟩ := (chargeExpand_ok _ _ _ _ _ _).1 h
  exact expand_valid _ _ _ valid

/-- A shortest unsigned byte count is zero for zero and otherwise brackets its value. -/
def ExpByteCount (value bytes : Nat) : Prop :=
  (value = 0 ∧ bytes = 0) ∨
    (0 < bytes ∧ 2 ^ (8 * (bytes - 1)) ≤ value ∧ value < 2 ^ (8 * bytes))

/-- EXP's byte count satisfies the independent shortest-encoding bounds. -/
theorem expBytes_spec (exponent : Word) : ExpByteCount exponent.toNat (expBytes exponent) := by
  by_cases h : exponent.toNat = 0
  · exact Or.inl ⟨h, by simp [expBytes, h]⟩
  · right
    have pos : 0 < (exponent.toNat.log2 + 8) / 8 := by omega
    have lo : 8 * ((exponent.toNat.log2 + 8) / 8 - 1) ≤ exponent.toNat.log2 := by omega
    have hi : exponent.toNat.log2 < 8 * ((exponent.toNat.log2 + 8) / 8) := by omega
    refine ⟨?_, ?_, ?_⟩
    · simp [expBytes, h]
    · simpa [expBytes, h] using (Nat.le_log2 h).mp lo
    · simpa [expBytes, h] using (Nat.log2_lt h).mp hi

/-- The byte interval determines its length uniquely. -/
theorem expByteCount_unique (value a b : Nat)
    (ha : ExpByteCount value a) (hb : ExpByteCount value b) : a = b := by
  rcases ha with ⟨az, rfl⟩ | ⟨ap, alo, ahi⟩
  · rcases hb with ⟨_, rfl⟩ | ⟨bp, blo, _⟩
    · rfl
    · subst value
      have : 0 < 2 ^ (8 * (b - 1)) := Nat.two_pow_pos _
      omega
  · rcases hb with ⟨bz, rfl⟩ | ⟨bp, blo, bhi⟩
    · subst value
      have : 0 < 2 ^ (8 * (a - 1)) := Nat.two_pow_pos _
      omega
    · by_cases h : a = b
      · exact h
      · rcases Nat.lt_or_gt_of_ne h with hab | hba
        · have he : 8 * a ≤ 8 * (b - 1) := by omega
          have hp := Nat.pow_le_pow_right (n := 2) (by decide) he
          omega
        · have he : 8 * b ≤ 8 * (a - 1) := by omega
          have hp := Nat.pow_le_pow_right (n := 2) (by decide) he
          omega

/-- The executable byte length is exactly the unique mathematical byte count. -/
theorem expBytes_iff (exponent : Word) (bytes : Nat) :
    expBytes exponent = bytes ↔ ExpByteCount exponent.toNat bytes := by
  constructor
  · intro h
    rw [← h]
    exact expBytes_spec exponent
  · exact expByteCount_unique _ _ _ (expBytes_spec exponent)

/-- Only zero has a zero-length unsigned encoding. -/
theorem expBytes_eq_zero_iff (exponent : Word) :
    expBytes exponent = 0 ↔ exponent.toNat = 0 := by
  by_cases h : exponent.toNat = 0
  · simp [expBytes, h]
  · have spec := expBytes_spec exponent
    simp only [ExpByteCount, h, false_and, false_or] at spec
    omega

/-- A nonzero exponent has a positive byte count and lies in its byte interval. -/
theorem expBytes_nonzero (exponent : Word) (h : exponent.toNat ≠ 0) :
    0 < expBytes exponent ∧
    2 ^ (8 * (expBytes exponent - 1)) ≤ exponent.toNat ∧
    exponent.toNat < 2 ^ (8 * expBytes exponent) := by
  have spec := expBytes_spec exponent
  simpa [ExpByteCount, h] using spec

/-- EXP costs 10 gas plus 50 gas for each byte in the shortest encoding. -/
theorem expCost_spec (exponent : Word) (cost : Nat) :
    expCost exponent = cost ↔
      ∃ bytes, ExpByteCount exponent.toNat bytes ∧ cost = 10 + 50 * bytes := by
  constructor
  · intro h
    exact ⟨expBytes exponent, expBytes_spec exponent, h.symm⟩
  · rintro ⟨bytes, hb, rfl⟩
    rw [expCost, (expBytes_iff exponent bytes).mpr hb]

/-- The gas price is bounded below by the base charge. -/
theorem expCost_min (exponent : Word) : 10 ≤ expCost exponent := by
  simp [expCost]

/-- Zero exponent pays only the base charge. -/
theorem expCost_zero : expCost 0 = 10 := by simp [expCost, expBytes]

/-- Every word exponent has at most 32 bytes. -/
theorem expBytes_le (exponent : Word) : expBytes exponent ≤ 32 := by
  by_cases h : exponent.toNat = 0
  · simp [expBytes, h]
  · have bound : exponent.toNat < 2 ^ 256 := exponent.isLt
    have logbound : exponent.toNat.log2 < 256 := (Nat.log2_lt h).mpr bound
    simp only [expBytes, ite_eq_right h]
    omega

/-- At each representable power of 256, the byte length increases by one. -/
theorem expBytes_pow256 (n : Nat) (hn : n < 32) :
    expBytes (BitVec.ofNat 256 (256 ^ n)) = n + 1 := by
  have bound : 2 ^ (8 * n) < 2 ^ 256 :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have representation : 256 ^ n = 2 ^ (8 * n) := by
    rw [Nat.pow_mul]
  have positive : 2 ^ (8 * n) ≠ 0 := Nat.ne_of_gt (Nat.two_pow_pos _)
  simp only [expBytes, BitVec.toNat_ofNat, representation, Nat.mod_eq_of_lt bound,
    ite_eq_right positive, Nat.log2_two_pow]
  omega

/-- The maximum word occupies all 32 bytes. -/
theorem expBytes_max : expBytes (BitVec.allOnes 256) = 32 := by
  apply (expBytes_iff _ _).mpr
  right
  have low : 2 ^ 248 < 2 ^ 256 := Nat.pow_lt_pow_right (by decide) (by decide)
  have pos : 0 < 2 ^ 256 := Nat.two_pow_pos _
  simp only [BitVec.toNat_allOnes]
  change 0 < 32 ∧ 2 ^ 248 ≤ 2 ^ 256 - 1 ∧ 2 ^ 256 - 1 < 2 ^ 256
  omega

/-- The cost increases at every representable power of 256. -/
theorem expCost_pow256 (n : Nat) (hn : n < 32) :
    expCost (BitVec.ofNat 256 (256 ^ n)) = 10 + 50 * (n + 1) := by
  rw [expCost, expBytes_pow256 n hn]

/-- The maximum word pays for 32 exponent bytes. -/
theorem expCost_max : expCost (BitVec.allOnes 256) = 1610 := by
  rw [expCost, expBytes_max]

/-- A nonzero exponent costs at least one byte charge in addition to the base. -/
theorem expCost_nonzero (exponent : Word) (h : exponent.toNat ≠ 0) :
    60 ≤ expCost exponent := by
  have count := (expBytes_nonzero exponent h).1
  simp only [expCost]
  omega

/-- EXP costs at most the base charge plus 32 byte charges. -/
theorem expCost_le (exponent : Word) : expCost exponent ≤ 1610 := by
  have h := expBytes_le exponent
  simp only [expCost]
  omega

end EthLib.EVM.Gas
