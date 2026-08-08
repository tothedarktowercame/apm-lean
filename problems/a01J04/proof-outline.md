# Proof Outline: a01J04

This proof outline was synthesized from legacy Lean files without a paired
proof-frame workspace.

Imported source: `lean-proofs/a01J04`

## Imported Lean Files

- `lean/Main.lean`

## Completed proof

- `apm_a01J04_geom_iteratedDeriv` computes the Taylor coefficients of
  `(1-z)⁻¹`, following the inversion calculation reused in sibling `a96A06`.
- `apm_a01J04_pole_iteratedDeriv` transports that formula by `z ↦ 2-z` and
  scalar multiplication, giving the exact derivatives of `λ/(z-1)` at `2`.
- `apm_a01J04_entire_coeff_superexp` applies the complex Cauchy estimate on
  the circle of radius `2T` centered at `2`. Compactness bounds `g` there, and
  multiplication by `Tⁿ` leaves a geometric `2⁻ⁿ` majorant.
- `apm_a01J04_error_eq_entire` differentiates the frozen decomposition and
  cancels the normalized pole coefficient.
- The main theorem rewrites the error to the entire remainder and applies the
  superexponential estimate.
