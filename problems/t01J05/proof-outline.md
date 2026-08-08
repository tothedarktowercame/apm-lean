# Proof Outline: t01J05

The Lean statement uses a genuine smooth cotangent section and defines Euler
characteristic as the alternating sum of rational singular-homology finranks.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t01J05.md`

## Formal progress

- `apm_t01J05_isEmpty_of_nowhereZero_zeroDim` closes the geometric part of
  the dimension-zero case: every cotangent fiber is zero, so the nowhere-zero
  hypothesis forces the manifold to be empty.
- `apm_t01J05_eulerCharacteristic_zero` reduces the frozen sum at `n = 0` to
  the single rational `H₀` finrank, and `apm_t01J05_zeroDim_of_empty_H0`
  completes that endpoint once the empty-space `H₀` normalization is supplied.
- `apm_t01J05_finrank_H0_eq_zero_of_isEmpty` proves that normalization from
  Mathlib's totally-disconnected `H₀` computation and the empty coproduct.
- `apm_t01J05_zeroDim` closes the entire `n = 0` branch, now dispatched by the
  main theorem proof itself.

## Remaining boundary

For positive dimension the informal proof constructs a Riemannian metric,
uses it to turn the one-form into a nowhere-zero vector field, and invokes
Poincaré--Hopf. Mathlib has smooth sections and tangent bundles but no packaged
Poincaré--Hopf or Euler-class theorem, nor a comparison with this alternating
singular-homology finrank definition. The zero-dimensional endpoint is closed.
