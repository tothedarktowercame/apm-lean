# Proof Outline: t95J05

`t95J05InclusionPullback_antipodal` proves directly that the encoded density
is invariant under the antipodal map. The subtype therefore contains the
desired projective form, and extensionality proves uniqueness; this is packaged
as `t95J05_existsUnique_projectiveThreeForm`.

`t95J05Integral_eq_sphereIntegral` now performs the pullback rewrite used by
the main proof. `t95J05InclusionPullback_expand` separates the density into its
mixed and square terms, and
`t95J05Integral_eq_neg_pi_sq_of_sphereIntegral` verifies the final quotient
normalization once the sphere integral is known to be `-2π²`.

After rewriting with pullback equality, the quotient integral is half the
Hausdorff-measure integral over the unit `S³` of `(x₁³ - 4x₀)x₀`.
Antipodal/coordinate reflection symmetry kills the mixed term. Rotational
symmetry makes every coordinate-square moment equal, and their sum is one, so
each equals one quarter of the sphere area. Since `area(S³)=2π²`, the result
is `-π²`.

## Remaining boundary

Mathlib has no ready formula for the Hausdorff-measure coordinate moment on a
Euclidean sphere, nor a Stokes theorem directly matching this scalar-density
encoding. The sphere-area normalization and symmetry argument must be assembled
locally.

Ambient radial integration does not provide this bridge: it concerns
Lebesgue measure on the whole Euclidean space, not Hausdorff measure on the
sphere subtype.
