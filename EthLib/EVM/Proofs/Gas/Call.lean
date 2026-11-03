module

public import EthLib.EVM.Gas.Call

@[expose] public section
namespace EthLib.EVM.Gas.Call

/-- An independent case specification of the charge and child grant. -/
def GrantSpec (value requested available memory extra stipend : Nat) (out : Grant) : Prop :=
  ∃ forwarded,
    (available < extra + memory → forwarded = requested) ∧
    (extra + memory ≤ available →
      forwarded = min requested (available - memory - extra - (available - memory - extra) / 64)) ∧
    out.cost = forwarded + extra ∧
    (value = 0 → out.child = forwarded) ∧
    (value ≠ 0 → out.child = forwarded + stipend)

/-- The source-oriented observations characterize every calculated grant. -/
theorem calculate_iff (value requested available memory extra stipend : Nat) (out : Grant) :
    calculate value requested available memory extra stipend = out ↔
      GrantSpec value requested available memory extra stipend out := by
  by_cases h : available < extra + memory
  · have hn : ¬ extra + memory ≤ available := by omega
    by_cases hv : value = 0 <;> cases out <;>
      simp [calculate, GrantSpec, h, hv, hn, Nat.sub_sub, eq_comm]
  · have hl : extra + memory ≤ available := by omega
    by_cases hv : value = 0 <;> cases out <;>
      simp [calculate, cap, GrantSpec, h, hv, hl, Nat.sub_sub, eq_comm] <;> omega

end EthLib.EVM.Gas.Call
