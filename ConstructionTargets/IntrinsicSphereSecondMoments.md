# Intrinsic sphere symmetry and second moments

This module transports literal sphere-subtype Hausdorff integrals through
constructed isometries and computes coordinate second moments relative to
total intrinsic mass. `Sphere d` is the unit sphere in
`EuclideanSpace ℝ (Fin (d + 1))`, as in `IntrinsicSphereFinite`.

`sphereIsometry` restricts an ambient linear isometry equivalence to this
sphere. Norm preservation supplies the subtype membership proofs; the
ambient inverse supplies both inverse laws. `integral_isometry` uses the
actual induced measurable equivalence and its Hausdorff measure preservation
to identify the integral after precomposition with the original integral.
This transport theorem requires no dimension bound or integrability premise.

`reflection d i` negates coordinate `i` and fixes the others.
`odd_integral` proves zero integral for a function negated by this actual
sphere reflection. `permutation` constructs coordinate permutations, with
the formula using `p.symm` on indices. Applying the swap permutation proves
`square_eq`, equality of all coordinate-square integrals.

Define `mass d` as the real value of Hausdorff measure of the whole sphere.
For `d ≤ 3`, the banked intrinsic finiteness theorem and continuity prove
integrability of each coordinate square. The pointwise sum of these squares
is one. Integrating that finite sum, using `square_eq`, and dividing by the
positive number `d + 1` yields `square_moment`:

```text
∫ x, xᵢ² ∂hausdorffMeasure d = mass d / (d + 1).
```

On the three-sphere, reflection of coordinate zero negates `x₁³ x₀`, so
`mixed_moment_zero` proves its integral is zero. Combining this with the
previously justified density split and the second moment gives
`projective_density_moment`:

```text
∫ x, (x₁³ x₀ - 4 x₀²) ∂hausdorffMeasure 3 = -mass 3.
```

The result does not evaluate `mass 3` numerically. A constructed plane
rotation, fourth and mixed-fourth moments, and expansion of the full flux
polynomial remain downstream. Numerical normalization and frozen consumer
closure are not claimed.

The Lean source is an unchanged promotion of
`/tmp/IntrinsicSphereSecondMomentsProbe.lean`, SHA-256
`243e91987507e34dd3d11e420e10630d70350d62afe4eab625cdda3e0c29b57a`.
The intrinsic-finiteness dependency was independently reviewed PASS at
`fc27383aa4c07f6f5b59760acab43af57c531375`.
Validation compiles the fixture and canonical target, builds this module
with `IntrinsicSphereFinite`, and reproduces all seven printed axiom audits.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
