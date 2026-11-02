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

end EthLib.EVM.Gas
