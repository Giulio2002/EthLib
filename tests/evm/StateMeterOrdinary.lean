import EthLib.EVM

open EthLib.EVM.Gas.StateMeter

private def meter : Meter := ⟨8, 5, 17, -9, 3, 2⟩
private def clean : Meter := ⟨8, 5, 17, -9, 0, 2⟩

private def check (ok : Bool) : IO Unit :=
  if ok then pure () else throw (IO.userError "state-gas meter assertion failed")

private def isCharge (result : Except EthLib.EVM.Gas.Error Meter) (expected : Meter) : Bool :=
  match result with
  | .ok actual => decide (actual = expected)
  | .error _ => false

-- The reservoir covers zero and exact-reservoir charges.
#eval check <| isCharge (chargeState meter 0) ⟨8, 5, 17, -9, 3, 2⟩
#eval check <| isCharge (chargeState meter 5) ⟨8, 0, 17, -9, 3, 2⟩

-- A charge spills into execution gas, including the exact total boundary.
#eval check <| isCharge (chargeState meter 7) ⟨6, 0, 17, -9, 5, 2⟩
#eval check <| isCharge (chargeState meter 13) ⟨0, 0, 17, -9, 11, 2⟩
#eval check <| match chargeState meter 14 with | .error .outOfGas => true | _ => false

-- Credits pay the spill first, then refill the reservoir.
#eval check <| decide (creditState meter 0 = ⟨8, 5, 17, -9, 3, 2⟩)
#eval check <| decide (creditState meter 2 = ⟨10, 5, 17, -9, 1, 2⟩)
#eval check <| decide (creditState meter 3 = ⟨11, 5, 17, -9, 0, 2⟩)
#eval check <| decide (creditState meter 7 = ⟨11, 9, 17, -9, 0, 2⟩)

-- A source-ordered charge and credit spans both gas pools.
#eval check <| match chargeState clean 7 with
  | .ok charged => decide (charged = ⟨6, 0, 17, -9, 2, 2⟩ ∧
      creditState charged 7 = ⟨8, 5, 17, -9, 0, 2⟩)
  | .error _ => false

-- Signed refund changes preserve the remaining meter fields.
#eval check <| decide (adjustRefund meter (-20) = ⟨8, 5, 17, -29, 3, 2⟩)
#eval check <| decide (adjustRefund meter 15 = ⟨8, 5, 17, 6, 3, 2⟩)
