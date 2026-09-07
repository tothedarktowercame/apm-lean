# Affine-line iterated Fréchet derivative

`scalarLineMap` is the continuous linear map sending a scalar to that scalar
multiple of a fixed direction. `affineLineRestriction` restricts a map to the
corresponding affine line.

`iteratedFDeriv_affineLineRestriction_zero` identifies the iterated derivative
at zero of `t ↦ f (a + t • v)` with the multivariable iterated derivative at
`a`, composed slotwise with `scalarLineMap v`.
`iteratedFDeriv_affineLineRestriction_zero_of_eq_zero` transfers vanishing of
the multivariable derivative to the affine-line restriction. Both the exact
composition identity and the `ContDiff`/order hypotheses are preserved from
the compiled fixture, using only standard axioms.

The remaining consumer work is to apply vector-valued one-dimensional Taylor
remainder along each affine segment, collapse the Taylor polynomial using the
transferred derivative vanishing, and obtain the uniform multivariable
order-`k + 1` remainder required by `exists_taylor_cover_measure_lt`.
