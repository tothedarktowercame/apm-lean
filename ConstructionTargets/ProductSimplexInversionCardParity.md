# Inversion-cardinality parity

`ConstructionTargets.ProductSimplexInversionCardParity` supplies the bounded
arithmetic conversion needed by the adjacent-swap sign calculation.

`neg_one_pow_card_eq_neg_of_unit_difference` takes two finite sets of one
common type. If either cardinality is exactly one greater than the other, it
proves that the integer power of `-1` indexed by the target cardinality is the
negative of the power indexed by the source cardinality. The disjunction makes
the result independent of which set has the larger cardinality while retaining
the source-to-target equation required by `shuffleSign`.

The theorem does not establish that adjacent swaps change inversion-set
cardinality by one. It defines no cancellation pairing, chain, or cross
product, and makes no consumer claim. Those steps remain for `t03J05`,
`t96J06`, and `t97A04`.
