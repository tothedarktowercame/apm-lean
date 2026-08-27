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

This is the bounded dimension-drop interface supported directly by the
current Jacobian API. It does not prove manifold Sard or construct regular
values. Applying it to arbitrary finite-dimensional source and target spaces
with strict finrank inequality still requires an explicit continuous linear
equivalence of the target with the source times a nontrivial complement.

`ChartCoordinateNullTransport` is experimental-only and is deliberately not
imported here. Once promoted separately, it can transport this coordinate
nullity across differentiable chart changes.
