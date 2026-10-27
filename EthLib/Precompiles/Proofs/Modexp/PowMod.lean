import EthLib.Precompiles.Modexp.Core

/-!
# Proofs: `powMod`

The square-and-multiply loop of the specification computes `b ^ e % m`.

This is the link between the executable form, which takes `log2 e` steps,
and the mathematical definition, which could not be run on a 1024-byte exponent.

The statement holds for every modulus, including `0`,
where `% 0` leaves the number unchanged.
-/

namespace EthLib.Precompiles.Modexp

/-- `powMod b e m` is `b ^ e % m`. -/
theorem powMod_eq (b e m : Nat) : powMod b e m = b ^ e % m := by
  induction e using Nat.strongRecOn generalizing b with
  | _ e ih =>
    rw [powMod]
    by_cases h0 : e = 0
    · subst h0
      simp
    · rw [dif_neg h0]
      -- The loop on the squared base and the halved exponent.
      have hrec := ih (e / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide)) (b * b % m)
      -- Squaring modulo `m` first changes nothing, so the half is `b ^ (2 * (e / 2)) % m`.
      have hhalf : (b * b % m) ^ (e / 2) % m = b ^ (2 * (e / 2)) % m := by
        rw [← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul]
      rw [hrec, hhalf]
      by_cases h1 : e % 2 = 1
      · -- An odd exponent: `e = 2 * (e / 2) + 1`.
        rw [if_pos h1, Nat.mod_mul_mod, ← Nat.pow_succ, show (2 * (e / 2)).succ = e by omega]
      · rw [if_neg h1, show 2 * (e / 2) = e by omega]

/-! ## Known answer

EIP-198, Specification, fourth worked example: base 3, exponent 65535 and modulus `2 ^ 255`.
The EIP gives the inputs but not the output.
The output is the one of `EIP-198-case4-extra-data_07`.
That case is in `tests/byzantium/eip198_modexp_precompile/test_modexp.py`.
The file is in `ethereum/execution-specs` at `2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1`.

`decide +kernel` makes the kernel evaluate the claim.
It adds no axiom, unlike `native_decide`. -/

example : powMod 3 65535 (2 ^ 255)
    = 0x3b01b01ac41f2d6e917c6d6a221ce793802469026d9ab7578fa2e79e4da6aaab := by
  rw [powMod_eq]
  decide +kernel

end EthLib.Precompiles.Modexp
