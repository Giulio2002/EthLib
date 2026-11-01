module
public meta import EthLib.EVM

open EthLib.EVM

-- These cases pin zero, one, powers of two and the largest word.
-- Large exponents run through the executable modular algorithm.
/-- info: true -/
#guard_msgs in
#eval Id.run do
  let max : Word := BitVec.ofNat 256 (2 ^ 256 - 1)
  let bases : List Word := [0, 1, 2, max]
  let exponents : List Word := [0, 1, 255, 256, max]
  let expected : List (List Nat) := [
    [1, 0, 0, 0, 0],
    [1, 1, 1, 1, 1],
    [1, 2, 2 ^ 255, 0, 0],
    [1, 2 ^ 256 - 1, 2 ^ 256 - 1, 1, 2 ^ 256 - 1]]
  return (bases.map fun b => exponents.map fun e => (Word.exp b e).toNat) == expected
