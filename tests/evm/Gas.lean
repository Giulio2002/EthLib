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
-- MCOPY pays three base gas, three per rounded word, and expansion gas.
example : mcopyCost 0 (2^256 - 1) (2^256 - 1) 0 = 3 := by decide
example : mcopyCost 0 0 0 1 = 9 := by decide
example : mcopyCost 0 0 0 31 = 9 := by decide
example : mcopyCost 0 0 0 32 = 9 := by decide
example : mcopyCost 0 0 0 33 = 15 := by decide
example : mcopyCost 0 64 0 1 = 15 := by decide
example : mcopyCost 0 0 64 1 = 15 := by decide
-- This calculates only the cost, without allocating the range.
example : rangeCost 0 (2^256) 1 > 2^256 := by decide

-- Cancun EXP prices depend on the exponent's shortest unsigned encoding.
example : expCost 0 = 10 := by decide
example : expCost 1 = 60 := by decide
example : expCost 255 = 60 := by decide
example : expCost 256 = 110 := by decide
example : expCost (BitVec.allOnes 256) = 1610 := by decide
example : charge 110 (expCost 256) = .ok 0 := by rfl
example : charge 109 (expCost 256) = .error .outOfGas := by rfl
