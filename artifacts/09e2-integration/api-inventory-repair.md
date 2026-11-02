# 09e2 API inventory repair

The lexical extractor now stops at an equation-style definition body.
It also handles a terminal equation-style definition without looking for a later declaration.
A missing delimiter raises an error instead of silently omitting the declaration.
The generator and its regression tests are in this directory.

The four child snapshots contain 227, 249, 251, and 271 matched declaration headers.
That is 998 child-to-candidate header comparisons in total.
The separate authored-declaration inventory contains 83 names and no missing names.
The corrected comparison finds no changed or missing headers or missing child imports.
It is a lexical comparison, not a proof of elaborated type equality.
The constructor and root changes remain recorded in `constructor-and-roots.diff`.

The inventory records `Frame.settle` in each child.
Each complete definition is byte-identical to the candidate definition.
Their SHA-256 is `41966ecf862297b455838ea6c0bd572b362a1a48146af0292ac08de5fbb88fe8`.

Five generator regression tests passed.
The generator was rerun and the inventory counts and all four `settle` checks were verified.
A manifest of 497 tracked and untracked Lean files was captured at the start of this repair.
The same file paths and SHA-256 values were verified after the repair.
`lean-files-sha256.txt` records that manifest.
This comparison establishes no Lean changes during the repair.
The supplied host gate evidence did not include a pre-existing whole-tree Lean hash manifest.

The host's existing gate evidence is unchanged.
The scoped axiom target inventory retains 307 entries.
The expensive Lean suite was not rerun for this evidence-only correction.
