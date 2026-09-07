# Higher-jet locus decomposition

This module isolates the finite set-theoretic decomposition needed to connect
the quantitative flat-locus Taylor theorem to the remaining Morse--Sard
rank/source-dimension induction.

For a map `f`, source locus `K`, and derivative cutoff `k`, `flatThrough`
contains exactly those points of `K` where every `iteratedFDeriv` of order from
one through `k` vanishes.  Its complement in `K` is expressed as the finite
indexed union of the corresponding `nonzeroJetLocus` sets.  The union is not
made artificially disjoint: later induction may refine it by the least
nonzero derivative order if that representation is useful.

The flat part now matches the vanishing premise of
`smooth_flat_locus_image_volume_eq_zero`.  The theorem does not incorrectly
deduce higher-order flatness from the already banked pointwise first-derivative
result.  Nullity of the nonzero-jet loci remains the analytic
rank/source-dimension induction step before rectangular aggregation.
