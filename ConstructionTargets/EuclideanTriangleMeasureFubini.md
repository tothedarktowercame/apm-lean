# Euclidean triangle measure/Fubini adapter

The frozen triangle lives in `EuclideanSpace ℝ (Fin 2)`, implemented as an
`L²` `WithLp` wrapper. This leaf proves that `WithLp.toLp` carries the literal
coordinate triangle

```
0 ≤ q 0, 0 ≤ q 1, q 0 + q 1 ≤ 1
```

exactly onto the frozen set. Mathlib's
`PiLp.volume_preserving_toLp` then gives an exact equality between the frozen
set integral and the corresponding integral over `Fin 2 → ℝ`. Both sets are
proved measurable; the transport is performed on their indicators.

The remaining theorem is now only `FinTwoTriangleFubini`: normalize volume on
`Fin 2 → ℝ` as the two-fold product Lebesgue measure and rewrite the triangular
indicator as the iterated bounds `0 ≤ x ≤ 1`, `0 ≤ y ≤ 1-x`. The current API
has `volume_pi` and product Fubini separately, but no direct eliminator for the
`Fin 2` function space that closes this rewrite. No integral value or Stokes
statement is assumed, and the frozen adapter follows immediately once this
single standard normalization is supplied.
