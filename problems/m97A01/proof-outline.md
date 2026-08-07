# Proof Outline: m97A01

The frozen theorem has a compiling partial Lean development.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m97A01.md`

## Compiled progress

- `apm_m97A01_modulus_core` constructs the unique positive square root of
  `A†A` and proves positivity, its square identity, and uniqueness.
- `apm_m97A01_modulus_norm` proves `‖|A|x‖ = ‖Ax‖`, completing every field of
  the frozen modulus predicate.

## Remaining boundary

- extend the isometry `|A|x ↦ Ax` from the dense range into the stated
  codomain without requiring dense codomain range, and prove uniqueness;
- prove that the adjoint of a compact continuous linear operator on a Hilbert
  space is compact, either directly or through polar decomposition.
