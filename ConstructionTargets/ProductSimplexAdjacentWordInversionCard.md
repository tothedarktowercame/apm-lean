# Adjacent-word inversion cardinality

`ConstructionTargets.ProductSimplexAdjacentWordInversionCard` proves the
finite-set step needed to compare shuffle signs under an adjacent Boolean-word
swap.

`wordInversionPairs_card_adjacentSwapWord` states that when the letters at
`i.castSucc` and `i.succ` differ, the cardinalities of `wordInversionPairs w`
and `wordInversionPairs (adjacentSwapWord w i)` differ by exactly one, in one
of the two possible directions.

The private helpers apply the actual adjacent-index transposition to both
coordinates of an inversion pair. Away from the special pair
`(i.castSucc, i.succ)`, that map preserves order and gives a bijection between
the two erased inversion sets. Exactly one of the original or swapped words
contains the erased special pair, producing the unit cardinality difference.

This module proves no path-level sign reversal and defines no cancellation,
chain, or cross product. It edits no consumer and claims no closure. Transport
through `adjacentSwapPath_word` and the geometric word-inversion equality
remains for `t03J05`, `t96J06`, and `t97A04`.
