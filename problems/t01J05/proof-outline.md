# Proof Outline: t01J05

The Lean statement uses a genuine smooth cotangent section and defines Euler
characteristic as the alternating sum of rational singular-homology finranks.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t01J05.md`

## Formal progress

- `apm_t01J05_isEmpty_of_nowhereZero_zeroDim` closes the geometric part of
  the dimension-zero case: every cotangent fiber is zero, so the nowhere-zero
  hypothesis forces the manifold to be empty.

## Remaining boundary

For positive dimension the informal proof constructs a Riemannian metric,
uses it to turn the one-form into a nowhere-zero vector field, and invokes
Poincaré--Hopf. Mathlib has smooth sections and tangent bundles but no packaged
Poincaré--Hopf or Euler-class theorem, nor a comparison with this alternating
singular-homology finrank definition. The zero-dimensional endpoint also needs
normalization of the singular homology of the empty space.
