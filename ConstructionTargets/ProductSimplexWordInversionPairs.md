# Boolean-word inversion pairs

`ConstructionTargets.ProductSimplexWordInversionPairs` connects the geometric
inversion set used by the product-simplex shuffle sign to the Boolean word
representation used by adjacent swaps.

`wordInversionPairs w` is the finite set of ordered positions `i < j` where
the Boolean word is vertical (`false`) at `i` and horizontal (`true`) at `j`.

`inversionPairs_eq_wordInversionPairs` states an exact equality from the
geometric `inversionPairs z`, defined using `IsHorizontal`, to
`wordInversionPairs` of the balanced word extracted by
`(wordPathEquiv p q).symm z`. The proof reuses the reviewed step-word
characterization of horizontal steps.

This representation comparison does not prove how an adjacent swap changes
the inversion-set cardinality or the shuffle sign. It defines no cancellation
pairing, chain, or cross product, edits no consumer, and claims no closure.
Those steps remain for `t03J05`, `t96J06`, and `t97A04`.
