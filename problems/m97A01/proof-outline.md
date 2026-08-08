# Proof Outline: m97A01

The frozen theorem has a compiling partial Lean development.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m97A01.md`

## Compiled progress

- `apm_m97A01_modulus_core` constructs the unique positive square root of
  `A†A` and proves positivity, its square identity, and uniqueness.
- `apm_m97A01_modulus_norm` proves `‖|A|x‖ = ‖Ax‖`, completing every field of
  the frozen modulus predicate.
- `apm_m97A01_polarOnRange` constructs the well-defined continuous range map
  `|A|x ↦ Ax` using `LinearMap.compLeftInverse`.
- Its application equation and exact norm preservation are proved by
  `apm_m97A01_polarOnRange_apply` and `apm_m97A01_polarOnRange_norm`.

## Remaining boundary

- bundle `range |A| ↪ closure (range |A|)` as a dense uniform embedding and
  apply `ContinuousLinearMap.extend`, preserving the isometry and uniqueness;
- prove that the adjoint of a compact continuous linear operator on a Hilbert
  space is compact, either directly or through polar decomposition.
