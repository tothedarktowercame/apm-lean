# Proof Outline: t94A09

The compiled restriction lemmas reduce smooth-field construction to giving a
smooth ambient map and proving its pointwise tangency.

For `S³`, use the orthogonal complex-structure field
`(x₀,x₁,x₂,x₃) ↦ (-x₁,x₀,-x₃,x₂)`.  It preserves norm and is
orthogonal to the radius, hence is nowhere zero on the unit sphere.
This construction is now fully compiled as
`apm_t94a09_exists_smoothSphereField_S3`.

For the torus, multiply a fixed circle-tangent direction by
`‖z-1‖² + ‖w-1‖²`.  This scalar is nonnegative and vanishes exactly at
`(1,1)`, producing the required unique zero.

This construction is now fully compiled as
`apm_t94a09_exists_smoothTorusField_unique_zero`. The scalar is expanded into
real and imaginary coordinate squares, its ambient field is proved smooth via
the complex coordinate continuous-linear maps, and tangency and uniqueness
are proved coordinatewise. Both positive conjuncts are wired into the main
theorem.

## Remaining boundary

The first conjunct is the hairy-ball theorem for `S²`. Mathlib has no packaged
Poincaré--Hopf, Euler-class, or sphere-degree theorem from which the stated
nonexistence follows. This is now the sole remaining boundary.
