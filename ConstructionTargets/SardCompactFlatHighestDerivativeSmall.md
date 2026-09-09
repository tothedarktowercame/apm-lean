# Uniform smallness near a compact flat locus

`exists_uniform_small_iteratedFDeriv_near_compact_flat` proves that the nth
derivative of a globally C^n map has arbitrarily small norm throughout a uniform
neighborhood of a compact locus on which that derivative vanishes.

Continuity makes the strict norm sublevel set open. Compactness supplies one
positive thickening radius contained in this sublevel set, which gives the
stated bound near every locus point.

The remaining analytic step applies this derivative bound along short affine
segments to obtain small Taylor remainder coefficients. The compact cover
construction and endpoint nullity can then consume those coefficients.
