import EthLib.EVM.Proofs.Gas

open EthLib.EVM.Gas EthLib.EVM.Memory.Allocation

-- Exact, insufficient, and zero payments.
example : charge 3 3 = .ok 0 := by rfl
example : charge 2 3 = .error .outOfGas := by rfl
example : charge 0 0 = .ok 0 := by rfl
example : charge 0 1 = .error .outOfGas := by rfl

-- The first word boundary and the first quadratic increment.
example : rangeCost 0 0 31 = 3 := by decide
example : rangeCost 0 0 32 = 3 := by decide
example : rangeCost 0 0 33 = 6 := by decide
example : memoryCost 22 = 66 := by decide
example : memoryCost 23 = 70 := by decide
example : expansionCost 23 23 = 0 := by decide
example : rangeCost 0 (2^256 - 1) 0 = 0 := by decide
example : pairCost 0 0 32 64 32 = 9 := by decide
-- This calculates only the cost, without allocating the range.
example : rangeCost 0 (2^256) 1 > 2^256 := by decide
