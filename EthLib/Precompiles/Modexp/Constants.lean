/-!
# `Modexp.Constants`

The fixed numbers of the MODEXP precompile at address `0x05`.

Every value is taken from the rules in force as of the BPO2 fork.

BPO2 is the latest fork activated on mainnet in `ethereum/execution-specs`.
The commit is `2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1`.
BPO2 activated on 2026-01-07, at timestamp 1767747671.

BPO2 changes only blob parameters.
So MODEXP behaves as in Osaka, the fork that introduced EIP-7823 and EIP-7883.
-/

namespace EthLib.Precompiles.Modexp.Constants

/-- Width in bytes of each of the three length headers.

EIP-198, Specification: "every length is a 32-byte left-padded integer". -/
def LENGTH_HEADER_BYTES : Nat := 32

/-- Offset of `BASE` in the input: it follows the three length headers.

EIP-198, Specification:
`<length_of_BASE> <length_of_EXPONENT> <length_of_MODULUS> <BASE> <EXPONENT> <MODULUS>`. -/
def BASE_OFFSET : Nat := 3 * LENGTH_HEADER_BYTES

/-- Largest accepted value of each length header, in bytes (8192 bits).

EIP-7823, Specification. -/
def MAX_LENGTH_BYTES : Nat := 1024

/-- Number of leading exponent bytes that enter the gas formula.

EIP-198, Specification, `ADJUSTED_EXPONENT_LENGTH`: "the first 32 bytes of `EXPONENT`".
See also `iterations` in the execution-specs module. -/
def EXPONENT_HEAD_BYTES : Nat := 32

/-- Bytes per word in the multiplication complexity.

EIP-7883, Specification: `words = math.ceil(max_length / 8)`. -/
def WORD_BYTES : Nat := 8

/-- Largest `max(base_length, modulus_length)` that is charged the minimal complexity.

EIP-7883, Specification, `calculate_multiplication_complexity`. -/
def SMALL_LENGTH_BYTES : Nat := 32

/-- Multiplication complexity of an operand of at most `SMALL_LENGTH_BYTES`.

EIP-7883, Specification, `calculate_multiplication_complexity`. -/
def MIN_COMPLEXITY : Nat := 16

/-- Iterations charged per exponent byte beyond `EXPONENT_HEAD_BYTES`.

EIP-7883, Specification, `calculate_iteration_count`
(EIP-2565 charged 8; EIP-7883 doubles it). -/
def ITERATIONS_PER_EXTRA_EXPONENT_BYTE : Nat := 16

/-- The least gas the precompile ever charges.

EIP-7883, Specification, `calculate_gas_cost`
(EIP-2565 charged at least 200). -/
def MIN_GAS : Nat := 500

/-! ## C-callable size accessors

The Python bindings read these at load time, so they hard-code no length.
Each takes a `Unit` to keep the C signature predictable. -/

@[export eth_modexp_const_length_header_bytes]
def constLengthHeaderBytes (_ : Unit) : UInt64 :=
  UInt64.ofNat LENGTH_HEADER_BYTES

@[export eth_modexp_const_max_length_bytes]
def constMaxLengthBytes (_ : Unit) : UInt64 :=
  UInt64.ofNat MAX_LENGTH_BYTES

end EthLib.Precompiles.Modexp.Constants
