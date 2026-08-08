# Proof Outline: t03J04

This bundle contains a compiling partial Lean formalization.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t03J04.md`

## Compiled progress

- `apm_t03J04_constantVectorField_ne_zero` proves the displayed global field
  is nowhere zero by evaluating its first coordinate.
- `apm_t03J04_localDiffeomorph_surjective` proves the standard first step of
  the finite-cover route when the connected target is Hausdorff: the range is
  open by local diffeomorphism, compact/closed by compactness and `T2Space`,
  and hence all of the connected target.

## Remaining boundary

- compute the alternating rational singular-homology ranks of `Fin n → Circle`;
- turn the compact-source local diffeomorphism into an appropriate finite
  covering and transport Euler characteristic, or develop the equivalent
  vector-field/Poincaré--Hopf argument.
- The frozen target lacks `T2Space X`; Mathlib's manifold classes do not imply
  it. Thus the compiled surjectivity bridge cannot be applied directly, and a
  non-Hausdorff replacement is additionally required unless the statement is
  later reviewed.
