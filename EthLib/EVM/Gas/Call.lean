module

public import EthLib.EVM.Gas

/-!
# Amsterdam message-call gas grants

Execution-specs Amsterdam revision `fd9298410ec7218838c8348f69c1eb633f1797dc`,
`vm/gas.py`, `calculate_message_call_gas` and `max_message_call_gas`.
The unaffordable branch preserves the source's calculation; the caller must
still perform the source's gas check and charge.
This module does not execute a call or model state-gas grants.
-/

@[expose] public section
namespace EthLib.EVM.Gas.Call

/-- Execution-gas charge and execution gas supplied to a child. -/
structure Grant where
  cost : Nat
  child : Nat
  deriving DecidableEq, Repr

/-- Source cap after deducting the state-independent costs. -/
def cap (gas : Nat) : Nat := gas - gas / 64

/-- Calculate the call's charge and child grant before the caller charges gas. -/
def calculate (value gas gasLeft memoryCost extraGas stipend : Nat) : Grant :=
  let forwarded := if gasLeft < extraGas + memoryCost then gas
    else min gas (cap (gasLeft - memoryCost - extraGas))
  ⟨forwarded + extraGas, forwarded + if value = 0 then 0 else stipend⟩

end EthLib.EVM.Gas.Call
