# Constructed local regular-fiber chart

This module constructs centered coordinates and a homeomorphism for a local
fiber from a surjective strict derivative. The hypotheses are real normed
spaces `E` and `F`, completeness of `E`, finite dimensionality of `F`,
`HasStrictFDerivAt f L x`, and surjectivity of the continuous linear map `L`.
In particular they cover finite-dimensional real source and target spaces.
No fiber chart or implicit-function data is supplied as an input.

Finite-dimensional range supplies a continuous projection onto `L.ker`.
`kernelProjection_retract` proves that it restricts to the identity on the
kernel, and `kernel_complement` identifies its kernel as a complementary
subspace. The production implicit-function theorem applied to
`y ↦ f y - f x` constructs `base`, with coordinate order `F × L.ker`.
Swapping the factors gives `chart : OpenPartialHomeomorph E (L.ker × F)`.
The exact equations are

```text
(chart y).fst = kernelProjection L (y - x)
(chart y).snd = f y - f x
chart x = (0, 0).
```

The center belongs to the chart source. `kernelOpen` is the inverse image
of the open target of `base` under `z ↦ (0,z)`, hence is an open kernel
neighborhood containing zero. Define `param z = base.symm (0,z)`.
`param_image` proves exact equality of its image on `kernelOpen` with the
intersection of the source of `base` and `{y | f y = f x}`. The proof uses
the banked zero-slice image theorem from
`SardImplicitFunctionLevelSetKernelParameterization`.

`fiberHomeomorph` proves both inverse laws and continuity for this local
fiber and the kernel neighborhood. `literalFiberHomeomorph` reexpresses
its source as an open neighborhood in the literal fiber subtype
`{y : E // f y = f x}`. Its inverse agrees exactly with `param`.
`param_zero` gives `param 0 = x`, and `param_derivative` proves the strict
derivative at zero is `L.ker.subtypeL`, the kernel inclusion into `E`.

`smooth_derivative` obtains strict differentiability from `ContDiff` at
smooth order. `smoothFiberHomeomorph` applies the construction with
`L = fderiv ℝ f x` and a surjectivity hypothesis on that actual derivative.
The concrete projection `ℝ × (ℝ × ℝ) → ℝ × ℝ` supplies a codimension-two
example, including smoothness, surjectivity, the local homeomorphism,
inverse-parameter derivative and target dimension two.

This is local regular-fiber geometry. Global manifold assembly, smooth
atlas compatibility, orientation, and transverse-intersection comparisons
remain downstream. No global regular-value theorem, Sard induction or
nullity theorem, or frozen consumer closure is claimed.

The source is an unchanged promotion of `/tmp/RegularFiberChartProbe.lean`,
SHA-256 `565d6e660df9ef1b1b4b167768409f7be33d1d8b073cb51bbb93dd40d871a653`.
Validation compiles the fixture and canonical source, builds this module
with `SardImplicitFunctionLevelSetKernelParameterization`, and reproduces
all eighteen printed axiom audits. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted.
