# Upstream compatibility

This development tree was rebased onto upstream `9ac0fb685ef9980ca139aacf7bd2878ff45f6dcd`.
Byte conversion now uses `EthLib.Base.BigEndian`; modular exponentiation and RIPEMD-160 reuse `EthLib.Execution.Evm.Precompiles`.
The rebase adapts imports and namespaces, not the historical EVM contracts' fork scope.

The Amsterdam EVM interpretation cites execution-specs `fd9298410ec7218838c8348f69c1eb633f1797dc`.
Upstream precompile dependencies cite `2c0c8e7d2010771621e9ae34f68a0d2d3e738aa1`.
`tests/evm/UpstreamPrecompileIntegration.lean` proves unrestricted agreement for the RIPEMD-160 gas formula, the precompile address set, and the runner's RIPEMD branch with the upstream call function.
These Lean equations do not establish equivalence to Python or agreement of every operation across forks.

`EthLib.EVM` and upstream `EthLib.Execution.Evm` remain separate implementations; this change does not merge their instruction-level semantics.
Only the documented pure dependencies are reused.
Delegation, unavailable precompile execution, other unimplemented instructions, and transaction initialization remain outside the implemented subset.

`ARCHITECTURE.md` requests one source revision per repository.
Reconciling these historical pins remains an explicit policy obligation, not a claim fulfilled by this rebase.
Blindly replacing a pin would relabel already-proved historical contracts without checking intervening source changes.
The overlap theorems above preserve the narrow dependency agreement while leaving a broader single-pin migration outstanding.
