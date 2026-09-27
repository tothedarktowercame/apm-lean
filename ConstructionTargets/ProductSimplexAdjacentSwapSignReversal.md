# Shuffle-sign reversal under an adjacent path swap

`ConstructionTargets.ProductSimplexAdjacentSwapSignReversal` proves the sign
change associated with swapping two unequal consecutive steps of a maximal
product-simplex path.

`shuffleSign_adjacentSwapPath` assumes that the balanced word extracted from
`z : MaximalPath p q` has unequal letters at the transported positions
`finCongr h i.castSucc` and `finCongr h i.succ`. Its conclusion is oriented
from the swapped path to the source path:

```lean
shuffleSign (adjacentSwapPath z h i) = -shuffleSign z
```

Three private helpers transport word-inversion cardinalities through
`finCongr`, identify the transported `balancedAdjacentSwap` word with
`adjacentSwapWord`, and lift the reviewed unit cardinality change to balanced
words. The public proof then rewrites both geometric inversion sets through
the reviewed Boolean-word representation and applies the reviewed parity
theorem for powers of `-1`.

This module defines no face pairing, cancellation, chain, or cross product. It
edits no consumer and claims no closure. Combining this sign equation with the
reviewed common simplicial and affine face equalities remains for `t03J05`,
`t96J06`, and `t97A04`.
