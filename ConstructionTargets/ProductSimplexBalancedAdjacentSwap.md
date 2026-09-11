# Balanced adjacent-word swaps

`ConstructionTargets.ProductSimplexBalancedAdjacentSwap` lifts the generic
adjacent Boolean-word transposition to `BalancedWord p q`.  An equality
`n + 1 = p + q` transports the transposition on `Fin (n + 1)` to the balanced
word's index type through `finCongr`.

`horizontalCount_adjacentSwapWord_last` and
`verticalCount_adjacentSwapWord_last` show that the transposition preserves
both terminal counts.  They use the terminal filtered-cardinality identities
and invariance of a filtered finite set under an equivalence.
`balancedAdjacentSwap_toWord` identifies the lifted operation's underlying
word, and `balancedAdjacentSwap_involutive` proves that applying the same swap
twice returns the original balanced word.

The module does not transport the operation to maximal paths, compare deleted
faces, assign shuffle signs, cancel chains, construct a cross product, or state
consumer closure.
