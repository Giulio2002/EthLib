module

public import EthLib.EVM.Memory.Allocation
public import EthLib.EVM.Word

/-!
# Gas and memory expansion

Cancun execution-specs `vm/gas.py`, `charge_gas`, `calculate_memory_gas_cost`,
and `calculate_gas_extend_memory`:
https://github.com/ethereum/execution-specs/blob/fd9298410ec7218838c8348f69c1eb633f1797dc/src/ethereum/forks/cancun/vm/gas.py

The Yellow Paper Appendix G and Appendix H, Gas Cost specify the memory cost:
https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex

These pure functions do not model an EVM frame or execute instructions.
Natural numbers avoid address and cost overflow.
-/

@[expose] public section
namespace EthLib.EVM.Gas

open EthLib.EVM.Memory.Allocation

inductive Error where
  | outOfGas
  deriving DecidableEq, Repr

/-- Charge only when the available gas covers the cost. -/
def charge (gas cost : Nat) : Except Error Nat :=
  if cost ≤ gas then .ok (gas - cost) else .error .outOfGas

/-- Total cost of allocating `words` 32-byte words. -/
def memoryCost (words : Nat) : Nat := 3 * words + words * words / 512

/-- Cost of expanding to cover one requirement. -/
def expansionCost (old requirement : Nat) : Nat :=
  memoryCost (max old requirement) - memoryCost old

/-- Cost of covering a byte range. -/
def rangeCost (old offset length : Nat) : Nat :=
  expansionCost old (requiredWords offset length)

/-- Cost of covering two ranges in one expansion. -/
def pairCost (old a n b m : Nat) : Nat :=
  expansionCost old (max (requiredWords a n) (requiredWords b m))

/-- Cancun `instructions/memory.py`, `mcopy`, and `gas.py`, `GasCosts`.

The copy charge rounds the length up to whole words.
Expansion covers both source and destination in one charge.
-/
def mcopyCost (old destination source length : Nat) : Nat :=
  3 + 3 * ((length + 31) / 32) + pairCost old source length destination length

/-- Cancun `instructions/environment.py`, `calldatacopy` and `codecopy`.

Only the destination range expands memory.
-/
def inputCopyCost (old destination length : Nat) : Nat :=
  3 + 3 * ((length + 31) / 32) + rangeCost old destination length

/-- Charge before expanding the logical allocation. -/
def chargeExpand (gas : Nat) (s : State) (offset length : Nat) : Except Error (Nat × State) :=
  match charge gas (rangeCost s.words offset length) with
  | .error e => .error e
  | .ok remaining => .ok (remaining, expand s offset length)

/-- The number of bytes in the shortest unsigned encoding of an EXP exponent.

Cancun execution-specs `arithmetic.py`, `exp`, uses the exponent bit length.
-/
def expBytes (exponent : Word) : Nat :=
  if exponent.toNat = 0 then 0 else (exponent.toNat.log2 + 8) / 8

/-- Cancun execution-specs `arithmetic.py`, `exp`, and `gas.py`, `GasCosts`. -/
def expCost (exponent : Word) : Nat := 10 + 50 * expBytes exponent

end EthLib.EVM.Gas
