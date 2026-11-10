# EthLib MODEXP specification, Lean v4.34.1 build

This branch contains the MODEXP precompile specification of [ethereum/EthLib](https://github.com/ethereum/EthLib)
and the modules it imports, **byte-for-byte identical** to upstream commit
`ffd60c4bcbafa185ad8fbcf23be544d4b01f6d1c`, so that it can be used as a pinned dependency by packages on Lean `v4.34.1`
(upstream EthLib uses `v4.35.0`; these 11 modules use no Mathlib and build unchanged on `v4.34.1`).

Only `lakefile.toml`, `lean-toolchain`, `UPSTREAM.md` and `scripts/check-upstream.sh` are new.
`scripts/check-upstream.sh <ethlib-checkout>` checks every `EthLib/**/*.lean` file here against that checkout at `ffd60c4bcbafa185ad8fbcf23be544d4b01f6d1c`.
