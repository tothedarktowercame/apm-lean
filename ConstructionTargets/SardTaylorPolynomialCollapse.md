# Vanishing-derivative Taylor polynomial collapse

`taylorWithinEval_eq_value_of_iteratedDerivWithin_eq_zero` proves that the
order-`k` Taylor polynomial is the constant value at its expansion point when
all within-set derivatives of orders `1` through `k` vanish.

`taylorWithinEval_eq_value_of_iteratedDeriv_eq_zero` supplies the interval form
used by Taylor's remainder theorem: on a `UniqueDiffOn` set, global `ContDiff`
regularity identifies the within-set iterated derivatives with the global
ones, so global derivative vanishing gives the same collapse. The exact
derivative range and `UniqueDiffOn` comparison are preserved from the fixture,
using only standard axioms.

The remaining consumer work is to uniformly bound the `(k + 1)`st derivative
of every affine-line restriction over the compact segment family, apply
`taylor_mean_remainder_bound`, and absorb its factorial constant into the
multivariable remainder required by `exists_taylor_cover_measure_lt`.
