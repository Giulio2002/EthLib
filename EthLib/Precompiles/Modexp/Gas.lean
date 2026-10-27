import EthLib.Precompiles.Modexp.Constants

/-!
# `Modexp.Gas`

The gas charged by MODEXP.

The rule is EIP-7883, which replaced the pricing of EIP-2565.
EIP-2565 in turn replaced the pricing of EIP-198.
No other pricing is specified here.

The executable source is `complexity`, `iterations` and `gas_cost`.
They are in `forks/bpo2/vm/precompiled_contracts/modexp.py`, in execution-specs at `2c0c8e7`.

## Where this module departs from the EIP-7883 pseudocode

The exponent bits come from the first 32 bytes of the exponent, as in EIP-198.
EIP-198 says "the first 32 bytes of `EXPONENT`".
It also says "If all of the first 32 bytes of `EXPONENT` are zero, return exactly
`8 * (length_of_EXPONENT - 32)`".
EIP-7883 scales that 8 to 16.

The EIP-7883 pseudocode reads differently, taken literally.
For a long exponent it writes `exponent & (2**256 - 1)`.
That keeps the LOW 256 bits of the whole exponent, not the first 32 bytes.
When the first 32 bytes are zero it gives one iteration less,
because `(0).bit_length() - 1 = -1`.

Execution-specs and EIP-198 agree with each other, so this module follows them.
EIP-2565 has the same pseudocode, with 8 in place of 16.
-/

namespace EthLib.Precompiles.Modexp

open EthLib.Precompiles.Modexp.Constants

/-- The multiplication complexity.

EIP-7883, Specification, `calculate_multiplication_complexity`.
`complexity` in the execution-specs module.

- Operands of at most 32 bytes cost a flat 16.
- Longer ones cost twice the square of their length in 8-byte words. -/
def complexity (baseLen modLen : Nat) : Nat :=
  let maxLength := max baseLen modLen
  -- `math.ceil(max_length / 8)`
  let words := (maxLength + WORD_BYTES - 1) / WORD_BYTES
  if maxLength > SMALL_LENGTH_BYTES then 2 * words ^ 2 else MIN_COMPLEXITY

/-- The iteration count: the adjusted exponent length, at least 1.

EIP-7883, Specification, `calculate_iteration_count`, read as in EIP-198 (see above).
`iterations` in the execution-specs module.

`expHead` is the integer in the first `min 32 expLen` bytes of the exponent.
`Nat.log2 expHead` is the index of its highest set bit, and `0` when it has none.
So one formula covers both the zero and the non-zero head. -/
def iterations (expLen expHead : Nat) : Nat :=
  let bitsPart := Nat.log2 expHead
  let count :=
    if expLen ≤ EXPONENT_HEAD_BYTES then bitsPart
    else ITERATIONS_PER_EXTRA_EXPONENT_BYTE * (expLen - EXPONENT_HEAD_BYTES) + bitsPart
  max count 1

/-- The gas of one call, from the three lengths and the exponent head.

EIP-7883, Specification, `calculate_gas_cost`.
`gas_cost` in the execution-specs module.

EIP-7883 removed the division by 3 that EIP-2565 applied. -/
def gasCost (baseLen modLen expLen expHead : Nat) : Nat :=
  max MIN_GAS (complexity baseLen modLen * iterations expLen expHead)

end EthLib.Precompiles.Modexp
