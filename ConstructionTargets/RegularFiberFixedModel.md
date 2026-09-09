# Fixed Euclidean model for local regular fibers

This module transports the smooth local fiber slice into a Euclidean model
whose dimension depends only on the source and target dimensions:

```text
Model = EuclideanSpace ℝ (Fin (finrank ℝ E - finrank ℝ F)).
```

The hypotheses are finite-dimensional real normed spaces `E` and `F`,
completeness of `E`, a surjective continuous linear map `L`, a smooth map
`f`, and `HasStrictFDerivAt f L x`. No local parameterization is supplied
as a premise.

`kernel_dimension` uses rank-nullity and surjectivity to prove the displayed
dimension equals `finrank ℝ L.ker`. `kernelEquiv` constructs a continuous
linear equivalence from this kernel to `Model`. Composing its inverse with
the kernel inclusion into `E` defines `tangentInclusion`.
`tangent_range` proves the range of this actual linear map is exactly
`L.ker`, with both inclusions proved explicitly.

`exists_parameterization` uses the constructed smooth coordinates from
`SmoothRegularFiberCoordinates`. If `A` is `kernelEquiv`, it defines

```text
V = {z | (0, A.symm z) ∈ e.target}
g z = e.symm (0, A.symm z).
```

The ambient neighborhood `U = e.source` is open and contains `x`.
The model neighborhood `V` is open and contains zero. The theorem proves
`g 0 = x`, smoothness on `V`, injectivity on `V`, and the exact image
equation `g '' V = U ∩ {y | f y = f x}`. Composition of strict derivatives
proves that the derivative of `g` at zero is `tangentInclusion`.

This is a local parameterization result with a fixed model. Actual fiber
charts, smooth overlap maps, common-model `ChartedSpace` and `IsManifold`
instances, smooth embedded inclusion and its manifold tangent-image equation
remain downstream. Empty-fiber handling and concrete global instances remain
in the parent. No global atlas, orientation or frozen consumer closure is
claimed here.

The Lean source is an unchanged promotion of
`/tmp/RegularFiberFixedModel.lean`, SHA-256
`2af7339d912eec2ac12db480a5ba1841a3c39e3074f329eb8be67ebfb1a85e4f`.
The smooth-coordinate dependency was independently reviewed PASS at
`6221b784bbcedc0097be6575a72f8db45847284b`.
Validation compiles the fixture and canonical target, builds this module
with `SmoothRegularFiberCoordinates`, and reproduces the three printed
axiom audits. Only `propext`, `Classical.choice`, and `Quot.sound` are
permitted.
