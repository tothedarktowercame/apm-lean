# Cardinality bound from a finite measurable packing

`finset_card_mul_le_measure_of_disjoint` supplies the measure-theoretic counting
step for a finite packing.  If the measurable sets indexed by `s` are pairwise
disjoint, each has measure at least `v`, and their union lies in `B`, then
`(s.card : ENNReal) * v ≤ μ B`.

This theorem does not construct a maximal separated family or prove that its
small source balls are disjoint and lie in a bounded enlargement.  It also does
not combine their cardinality estimate with Taylor-controlled target-ball
volumes.  The remaining Sard obligation is one maximal-separated-set source
cover construction and Taylor/volume exponent estimate, before local rank
reduction.
