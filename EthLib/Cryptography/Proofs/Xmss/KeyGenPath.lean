import EthLib.Cryptography.Proofs.Xmss.KeyGenLeaf6
import EthLib.Cryptography.Proofs.Xmss.KeyGenLeaf8
import Mathlib.Tactic.IntervalCases

/-!
# Proofs: the Merkle path of epoch 7

The reference key covers epochs 6 to 8.

Its tree has three real leaves.

A node with no epoch below it is a filler, one hash of the seed.

The path of leaf 7 holds one sibling per level:

```text
    level      sibling   value
    0          6         leaf 6
    1          2         filler
    2          0         filler
    3          1         above leaf 8: one hash per level, each with a filler on the right
    4 to 31    1         filler
```

These theorems show the key's tree gives leaf 7 the path of the reference signature.
-/

namespace EthLib.Cryptography.Xmss
open Constants

/-- The tree of the reference key. -/
def katTree : TreeParams where
  publicParam := examplePublicKey.publicParam
  seed := exampleSeed
  epochStart := 6
  epochEnd := 8
  epochStart_le_epochEnd := by decide

theorem exampleSk_tree_eq : exampleSk.tree = katTree := by
  unfold SecretKey.tree katTree
  rw [katPublicParam]
  rfl

/-- The node above leaf 8 on level 3 is the fourth sibling of the reference path. -/
theorem katNode_3_1 :
    katTree.node exampleSk.leaves 3 1 = exampleSignature.merklePath[3] := by
  -- Each level hashes the node above leaf 8 with a filler on its right.
  rw [node_succ (l := 2) (by decide)]
  change merkleNode katTree.publicParam 3 1
    (katTree.node exampleSk.leaves 2 2) (katTree.node exampleSk.leaves 2 3) = _
  rw [node_succ (l := 1) (by decide)]
  change merkleNode katTree.publicParam 3 1
    (merkleNode katTree.publicParam 2 2
      (katTree.node exampleSk.leaves 1 4) (katTree.node exampleSk.leaves 1 5))
    (katTree.node exampleSk.leaves 2 3) = _
  rw [node_succ (l := 0) (by decide)]
  change merkleNode katTree.publicParam 3 1
    (merkleNode katTree.publicParam 2 2
      (merkleNode katTree.publicParam 1 4
        (katTree.node exampleSk.leaves 0 8) (katTree.node exampleSk.leaves 0 9))
      (katTree.node exampleSk.leaves 1 5))
    (katTree.node exampleSk.leaves 2 3) = _
  rw [node_zero (by decide), katLeaf8_eq, node_of_not_covers (tp := katTree) (by decide),
    node_of_not_covers (tp := katTree) (by decide), node_of_not_covers (tp := katTree) (by decide)]
  -- One leaf hash, three Merkle nodes and three fillers, for the kernel.
  simp only [merkleNode_eq_fast, fillerNode_eq_fast, otsLeaf_eq_fast]
  decide +kernel

/-- A node no epoch reaches is the filler at its position, as the reference path has it. -/
local macro "kat_filler" : tactic =>
  `(tactic| (rw [node_of_not_covers (by decide), fillerNode_eq_fast]; decide +kernel +revert))

/-- The key's tree gives leaf 7 the path of the reference signature. -/
theorem katAuthPath7 :
    exampleSk.tree.authPath exampleSk.leaves 7 = exampleSignature.merklePath := by
  rw [exampleSk_tree_eq]
  apply Vector.ext
  intro i hi
  change i < 32 at hi
  simp only [TreeParams.authPath, Vector.getElem_ofFn]
  interval_cases i
  -- Level 0: the leaf at epoch 6.
  · change katTree.node exampleSk.leaves 0 6 = _
    rw [node_zero (by decide), katLeaf6_eq]
    rfl
  · kat_filler
  · kat_filler
  -- Level 3: the node above leaf 8.
  · change katTree.node exampleSk.leaves 3 1 = _
    exact katNode_3_1
  -- Levels 4 to 31: fillers.
  all_goals kat_filler

end EthLib.Cryptography.Xmss
