module

public import EthLib.EVM.Word

/-!
# Immutable message environment

Cancun execution-specs revision `fd9298410ec7218838c8348f69c1eb633f1797dc`,
`vm/__init__.py` and `vm/instructions/environment.py` define these fields.
The gas price is restricted to the U256 domain accepted by GASPRICE.
The context supplies metadata and does not execute calls or transactions.
-/

@[expose] public section
namespace EthLib.EVM.Environment

/-- A 160-bit account address interpreted as an unsigned big-endian integer. -/
abbrev Address := Fin (2 ^ 160)

/-- Zero-extend the address to a stack word. -/
def addressWord (address : Address) : Word := BitVec.ofNat 256 address.val

/-- Immutable metadata supplied to a message frame. -/
structure Context where
  currentTarget : Address
  origin : Address
  caller : Address
  value : Word
  gasPrice : Word

end EthLib.EVM.Environment
