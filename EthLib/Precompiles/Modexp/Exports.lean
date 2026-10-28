import EthLib.Precompiles.Modexp.Core

/-!
# `Modexp.Exports`

C-ABI exports for the MODEXP precompile, callable from the Python C extension.

- Inputs are `ByteArray` or `UInt64`.
- Outputs are `ByteArray` or `UInt64`.
- Failures are `IO` errors, which Python raises.
-/

namespace EthLib.Precompiles.Modexp.Exports

open EthLib.Precompiles.Modexp

/-- Run the precompile on the call data with the gas given.

EVM gas is a 64-bit integer, so the gas crosses the boundary as `UInt64`. -/
@[export eth_modexp]
def modexpExport (data : ByteArray) (gas : UInt64) : IO ByteArray :=
  runModexp (modexp data gas.toNat)

/-- The gas the precompile charges for the call data.

The price is at most 528449536 once the lengths are in bounds.

A proof in the proofs library shows this, so the conversion to `UInt64` drops nothing. -/
@[export eth_modexp_gas_cost]
def gasCostExport (data : ByteArray) : IO UInt64 :=
  runModexp ((chargedGas data).map UInt64.ofNat)

end EthLib.Precompiles.Modexp.Exports
