import EthLib.Precompiles.Proofs.Modexp

/-!
# `EthLib.Precompiles.Proofs`

Machine-checked properties of the executable specification. This tree
mirrors the layout of the definitions it proves things about: proofs for
`EthLib.Precompiles.Foo` live in `EthLib.Precompiles.Proofs.Foo`.

The proofs are compiled by the `Proofs` Lake library, which the runtime
code does not depend on: nothing here is linked into the Python extension.
-/
