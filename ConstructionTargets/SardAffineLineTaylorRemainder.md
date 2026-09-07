# Affine-line flat Taylor remainder

`affineLine_flat_taylor_remainder_bound` transfers the one-dimensional mean
Taylor remainder theorem to the affine segment from `a` to `x`. Its hypotheses
retain global `ContDiff ℝ (k + 1)` regularity, vanishing multivariable iterated
Fréchet derivatives through order `k`, and the scaled interval-relative bound
on the `(k + 1)`st line derivative.

The proof uses the promoted affine-line derivative comparison to transfer
vanishing, the Taylor-polynomial collapse theorem to reduce the polynomial to
`f a`, and `taylor_mean_remainder_bound` to obtain the exact bound with the
`k!` denominator. It uses only standard axioms.

The remaining consumer work is to produce the scaled highest-line-derivative
bound uniformly from continuity on the compact family of segment parameters,
absorb the factorial into the constant, and feed the resulting multivariable
remainder into `exists_taylor_cover_measure_lt`.
