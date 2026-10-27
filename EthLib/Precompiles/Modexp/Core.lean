import EthLib.Precompiles.Modexp.Bytes
import EthLib.Precompiles.Modexp.Gas
import EthLib.Precompiles.Modexp.Errors

/-!
# `Modexp.Core`

The MODEXP precompile at address `0x05`, as of the BPO2 fork.

The input has this layout, from EIP-198:

```text
    [ len_base: 32 | len_exp: 32 | len_mod: 32 | BASE | EXPONENT | MODULUS ]
```

- Each length is a 32-byte big-endian integer, in bytes.
- The call data is read as if it were followed by infinitely many zero bytes.
  So a short input is padded and a long one has its excess ignored.
- Each length must be at most 1024 (EIP-7823).

The output is `BASE ^ EXPONENT mod MODULUS` as exactly `len_mod` big-endian bytes.
It is `len_mod` zero bytes when `MODULUS` is 0.

The steps run in the order of `modexp` in the execution-specs module.
That module is `forks/bpo2/vm/precompiled_contracts/modexp.py`, in execution-specs at `2c0c8e7`.
First the bounds are checked, then the gas is charged, then the operation runs.
-/

namespace EthLib.Precompiles.Modexp

open EthLib.Precompiles.Modexp.Constants

/-- The three length headers of an input, in bytes. -/
structure Lengths where
  base : Nat
  exponent : Nat
  modulus : Nat

/-- Read the three length headers.

EIP-198, Specification.
The first lines of `modexp` in the execution-specs module. -/
def parseLengths (data : ByteArray) : Lengths where
  base := readNat data 0 LENGTH_HEADER_BYTES
  exponent := readNat data LENGTH_HEADER_BYTES LENGTH_HEADER_BYTES
  modulus := readNat data (2 * LENGTH_HEADER_BYTES) LENGTH_HEADER_BYTES

/-- Reject a length above `MAX_LENGTH_BYTES`.

EIP-7823, Specification.
The three `ExceptionalHalt` checks of `modexp` in the execution-specs module.
They run in the order base, exponent, modulus. -/
def checkLengths (l : Lengths) : Except ModexpError Unit :=
  if l.base > MAX_LENGTH_BYTES then .error (.lengthTooLarge .base l.base)
  else if l.exponent > MAX_LENGTH_BYTES then .error (.lengthTooLarge .exponent l.exponent)
  else if l.modulus > MAX_LENGTH_BYTES then .error (.lengthTooLarge .modulus l.modulus)
  else .ok ()

/-- Where `EXPONENT` starts: right after `BASE`. -/
def Lengths.exponentStart (l : Lengths) : Nat :=
  BASE_OFFSET + l.base

/-- Where `MODULUS` starts: right after `EXPONENT`. -/
def Lengths.modulusStart (l : Lengths) : Nat :=
  l.exponentStart + l.exponent

/-- The first 32 bytes of `EXPONENT` (fewer when it is shorter), as an integer.

`exp_head` in `modexp` in the execution-specs module. -/
def exponentHead (data : ByteArray) (l : Lengths) : Nat :=
  readNat data l.exponentStart (min EXPONENT_HEAD_BYTES l.exponent)

/-- The gas the call is charged, read from the input.

This is `gas_cost(base_length, modulus_length, exp_length, exp_head)`
in `modexp` in the execution-specs module. -/
def requiredGas (data : ByteArray) (l : Lengths) : Nat :=
  gasCost l.base l.modulus l.exponent (exponentHead data l)

/-- `b ^ e mod m` by square-and-multiply, in `log2 e` steps.

Each step halves the exponent and squares the base modulo `m`.
The naive `b ^ e % m` is out of reach for a 1024-byte exponent,
so the specification needs this form to be executable.
`Proofs.Modexp.PowMod` shows it equals `b ^ e % m`. -/
def powMod (b e m : Nat) : Nat :=
  if h : e = 0 then 1 % m
  else
    -- The result for the exponent `e / 2` and the squared base.
    let half := powMod (b * b % m) (e / 2) m
    -- An odd exponent leaves one factor of `b` over.
    if e % 2 = 1 then half * b % m else half
termination_by e
decreasing_by omega

/-- The operation of the precompile: the output bytes, once the gas is paid.

The `# OPERATION` part of `modexp` in the execution-specs module.
Python's `pow(base, exp, modulus)` is `powMod`, and a zero modulus gives zero bytes.
When `base` and `modulus` are both empty the output is empty,
which is the explicit early return of the execution-specs module. -/
def compute (data : ByteArray) (l : Lengths) : ByteArray :=
  let base := readNat data BASE_OFFSET l.base
  let exponent := readNat data l.exponentStart l.exponent
  let modulus := readNat data l.modulusStart l.modulus
  let result := if modulus = 0 then 0 else powMod base exponent modulus
  ByteArray.mk (natToBytes l.modulus result).toArray

/-- The gas a call is charged, or the reason it fails before gas is charged. -/
def chargedGas (data : ByteArray) : Except ModexpError Nat :=
  let l := parseLengths data
  match checkLengths l with
  | .error e => .error e
  | .ok () => .ok (requiredGas data l)

/-- Run the precompile on `data` with `gas` available.

Returns the output, or the error that consumes all the gas.
`modexp` in the execution-specs module. -/
def modexp (data : ByteArray) (gas : Nat) : Except ModexpError ByteArray :=
  let l := parseLengths data
  -- EIP-7823: bounds first, before any gas is charged.
  match checkLengths l with
  | .error e => .error e
  | .ok () =>
    -- Gas is charged before the base, exponent and modulus are read.
    let cost := requiredGas data l
    if gas < cost then .error (.outOfGas cost gas) else .ok (compute data l)

end EthLib.Precompiles.Modexp
