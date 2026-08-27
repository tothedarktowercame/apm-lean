# Euclidean dimension-drop image nullity

This target packages the square-dimensional Mathlib Sard theorem for a map
whose target is explicitly split as `E × G`, with `G` nontrivial. Given a
differentiable `f : E → E × G`, its extension

```text
(x, y) ↦ f x
```

has the same range and has singular derivative everywhere because it kills
the entire `G` direction. Mathlib's
`addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` therefore proves that the
range, and hence the image of every source subset, is null for any add-Haar
measure on `E × G`.

`addHaar_range_eq_zero_of_equiv` first transports the result through an
explicit continuous linear equivalence `F ≃L[ℝ] E × G`. Nullness is
transported without a measurability assumption on the range, using
`Measure.preimage_null_of_map_null` for the pushforward add-Haar measure.

`addHaar_range_eq_zero_of_finrank_lt` then constructs the complement rather
than assuming it. For `finrank E < finrank F`, take
`G = Fin (finrank F - finrank E) → ℝ`; strict inequality makes `G`
nontrivial, and `ContinuousLinearEquiv.ofFinrankEq` supplies
`F ≃L[ℝ] E × G`. Thus the target now covers arbitrary finite-dimensional
real normed source and target spaces with strict finrank inequality.

The corresponding `DifferentiableOn` result does not extend the map outside
its source set.  `addHaar_image_eq_zero_of_differentiableOn` applies the
fixed-dimensional Sard theorem to the complement extension only on
`s × univ`; its within derivative kills the complementary factor there.
`addHaar_image_eq_zero_of_equiv_differentiableOn` transports that local
statement through the target equivalence, and
`addHaar_image_eq_zero_of_finrank_lt_differentiableOn` constructs the finite
coordinate complement from the strict finrank inequality.

This is the bounded dimension-drop interface supported directly by the
current Jacobian API. It does not prove manifold Sard, construct regular
values, or promote a regular fiber to a manifold.

`ChartCoordinateNullTransport` is experimental-only and is deliberately not
imported here. Once promoted separately, it can transport this coordinate
nullity across differentiable chart changes.
