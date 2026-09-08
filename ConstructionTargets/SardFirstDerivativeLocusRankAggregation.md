# First-derivative locus rank aggregation

`firstNonzeroJetLocus_one_image_null_of_rankStrata` reduces nullity of the
localized order-one first-nonzero-jet locus to nullity of its exact derivative
rank pieces.

The theorem assumes the order-one locus lies in the nonsurjective derivative
locus. The finite-dimensional target then decomposes that critical locus into
the finitely indexed rank strata `Fin (Module.finrank ℝ F)`. Intersecting the
decomposition with the localized order-one locus and applying countable-union
nullity gives the result for an arbitrary target measure.

The remaining consumer obligation is analytic: prove image nullity for each
localized exact-rank piece using the local rank-normal-form branch.
