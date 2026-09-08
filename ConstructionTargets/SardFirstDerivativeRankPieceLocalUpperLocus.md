# First-derivative rank-piece local upper locus

`exists_open_inter_firstNonzeroJetLocus_one_rankStratum_eq_rankLE` localizes an
order-one first-nonzero-jet exact-rank piece at one of its points.

Its direct theorem dependency is
`:critical-value-sard-exact-rank-local-upper-locus-1`, which supplies
`exists_open_inter_rankStratum_eq_rankLE`; the row ledger must retain that id
in addition to the order-one aggregation and rank-strata dependencies.

Derivative-rank lower semicontinuity supplies an open neighborhood on which
rank is at least the base rank. Consequently, within that neighborhood, exact
rank is equivalent to the complementary rank-at-most condition. Intersecting
this equality with the localized order-one locus preserves the exact predicate
needed by its image-nullity aggregation theorem.

The remaining consumer step is to construct projected local rank coordinates
on this rank-at-most locus and prove residual derivative flatness along their
constant projected-coordinate slices.
