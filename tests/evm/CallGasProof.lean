import EthLib.EVM.Proofs.Gas.Call

open EthLib.EVM.Gas.Call

-- Actual grant results satisfy both source branches for arbitrary inputs.
theorem call_grant_forward (value gas available memory extra stipend : Nat) :
    GrantSpec value gas available memory extra stipend
      (calculate value gas available memory extra stipend) :=
  (calculate_iff value gas available memory extra stipend _).mp rfl

-- Independent charge and child constraints determine the implementation result.
theorem call_grant_converse (value gas available memory extra stipend : Nat) (out : Grant)
    (h : GrantSpec value gas available memory extra stipend out) :
    calculate value gas available memory extra stipend = out :=
  (calculate_iff value gas available memory extra stipend out).mpr h
