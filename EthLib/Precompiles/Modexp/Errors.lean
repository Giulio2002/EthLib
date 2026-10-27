import EthLib.Precompiles.Modexp.Constants

/-!
# `Modexp.Errors`

Typed failures of the MODEXP precompile.

Both failures end the call and consume all its gas.
They differ in why.

- A length above the bound of EIP-7823 is an exceptional halt, raised before any gas is charged.
- A call whose gas is below the price runs out of gas.
-/

namespace EthLib.Precompiles.Modexp

/-- The three length headers of the input. -/
inductive LengthField where
  | base
  | exponent
  | modulus

/-- Every way a MODEXP call can fail. -/
inductive ModexpError where
  /-- A length header exceeded `MAX_LENGTH_BYTES`.

  EIP-7823, Specification: "the precompile execution stops, returns an error,
  and consumes all gas".
  `ExceptionalHalt` in `forks/bpo2/vm/precompiled_contracts/modexp.py`. -/
  | lengthTooLarge (field : LengthField) (length : Nat)
  /-- The gas given was below the price.

  `charge_gas` raises `OutOfGasError` in `forks/bpo2/vm/gas.py`. -/
  | outOfGas (cost gas : Nat)

/-- Human-readable description, used at the C-ABI boundary. -/
def ModexpError.message : ModexpError → String
  | .lengthTooLarge .base length =>
      s!"base length {length} exceeds {Constants.MAX_LENGTH_BYTES}"
  | .lengthTooLarge .exponent length =>
      s!"exponent length {length} exceeds {Constants.MAX_LENGTH_BYTES}"
  | .lengthTooLarge .modulus length =>
      s!"modulus length {length} exceeds {Constants.MAX_LENGTH_BYTES}"
  | .outOfGas cost gas => s!"out of gas: price {cost}, gas {gas}"

/-- Run a fallible MODEXP computation down to `IO`.

The C-ABI layer surfaces failures to Python as exceptions. -/
def runModexp {α : Type} (act : Except ModexpError α) : IO α :=
  match act with
  | .ok a => pure a
  | .error e => throw (IO.userError e.message)

end EthLib.Precompiles.Modexp
