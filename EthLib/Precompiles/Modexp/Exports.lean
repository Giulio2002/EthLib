import EthLib.Precompiles.Modexp.Core

/-!
# `Modexp.Exports`

C-ABI exports for the MODEXP precompile, callable from the Python C extension.

Inputs are `ByteArray` or `UInt64`.
Outputs are `ByteArray`, and failures are `IO` errors that Python raises.
-/

namespace EthLib.Precompiles.Modexp.Exports

open EthLib.Precompiles.Modexp

/-- A natural number as its shortest big-endian bytes, or one zero byte for `0`.

A gas price can exceed `2 ^ 64`, so it travels as bytes. -/
def natToMinimalBytes (n : Nat) : ByteArray :=
  ByteArray.mk (natToBytes (Nat.log2 n / 8 + 1) n).toArray

@[export eth_modexp]
def modexpExport (data : ByteArray) (gas : UInt64) : IO ByteArray :=
  runModexp (modexp data gas.toNat)

@[export eth_modexp_gas_cost]
def gasCostExport (data : ByteArray) : IO ByteArray :=
  runModexp ((chargedGas data).map natToMinimalBytes)

end EthLib.Precompiles.Modexp.Exports
