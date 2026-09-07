# Finite-cover measure aggregation for Sard estimates

`measure_le_finset_sum_of_subset_biUnion` states the finite indexed-cover
inequality in the form used by the Sard scale argument.  When `s` is contained
in the union of the sets `u i` for `i` in a finite index set `I`, its measure is
bounded by `∑ i ∈ I, μ (u i)`.

This theorem supplies only the finite-union measure bookkeeping.  It neither
constructs a cover from smooth flatness nor estimates the cover cardinality or
the measures of its members.  The remaining analytic obligation is one smooth
flat-locus scale-cover and arbitrarily-small-measure theorem, before local rank
reduction.
