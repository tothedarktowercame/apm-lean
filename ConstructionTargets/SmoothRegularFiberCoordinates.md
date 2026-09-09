# Smooth regular-fiber coordinate restriction

This module refines the constructed regular-fiber coordinates to a smooth
local coordinate map with smooth inverse, preserving the exact fiber slice
and its strict derivative at zero.

The hypotheses are finite-dimensional real normed spaces `E` and `F`,
`CompleteSpace E`, a smooth map `f`, a strict derivative `L` at `x`, and
surjectivity of `L`. Smoothness can supply the strict derivative using
`RegularFiberChart.smooth_derivative`. Neither a fiber chart nor a smooth
inverse is assumed.

`exists_coordinates` constructs the continuous linear equivalence
`E ≃L[ℝ] F × L.ker` from the surjective derivative and the banked kernel
projection and complementary kernel. The derivative of the existing `base`
coordinates is this equivalence. Their forward map is smooth because its
components are `f y - f x` and the continuous linear projection of `y - x`.

The theorem applies `SardSmoothNeighborhoodImplicitChart`'s existing
smooth-neighborhood refinement. The resulting partial homeomorphism `e`
has source containing `x` and contained in the original source. Its forward
function equals `base` exactly, and its inverse agrees with `base.symm`
on its target. Both functions are smooth on their respective domains.

`exists_smooth_fiber_slice` retains these facts and proves

```text
e x = (0,0),       (e y).fst = f y - f x.
```

The coordinate order is `F × L.ker`. The set of kernel vectors `z` with
`(0,z) ∈ e.target` is open and contains zero. The map `z ↦ e.symm (0,z)`
is smooth there, and its image equals exactly
`e.source ∩ {y | f y = f x}`. The image equality uses the banked inverse
slice theorem for actual partial homeomorphisms.

Inverse agreement on an open neighborhood of zero transfers the strict
derivative from `RegularFiberChart.param_derivative`: the slice derivative
at zero is `L.ker.subtypeL`, the kernel inclusion into `E`.

Transport of varying kernels to a common Euclidean model, smooth overlap
construction, a fiber atlas, smooth embedded inclusion, and its tangent-image
equation remain downstream. Empty-fiber and global specialization obligations
remain in the parent. This module does not claim global manifold structure,
orientation or frozen consumer closure.

The source is an unchanged promotion of
`/tmp/SmoothRegularFiberCoordinates.lean`, SHA-256
`ee204dbe9cfca2f6389bd8d5ea33b6157d8876327292de07a72f1aa4d2638176`.
Validation compiles the fixture and canonical target, builds this module
with `RegularFiberChart` and `SardSmoothNeighborhoodImplicitChart`, and
reproduces both printed axiom audits. Only `propext`, `Classical.choice`,
and `Quot.sound` are permitted.
