# Proof Outline: m95J07

The frozen theorem has a compiling partial Lean development.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m95J07.md`

## Compiled progress

- `apm_m95j07_automatic_continuity` proves the complete second conjunct via
  Mathlib's sequential closed graph theorem.
- The proof needs only continuity and injectivity of `A`; it does not require
  the range of `A` to be closed.
- `apm_m95j07_cusp` bundles the absolute-value cusp in `C([-1,1])`.
- `apm_m95j07_cusp_not_differentiable` proves no ambient extension agreeing
  with that cusp can be differentiable at zero.
- `apm_m95j07_norm_cusp` proves the cusp has unit sup norm.
- `apm_m95j07_smul_cusp_not_differentiable` and
  `apm_m95j07_add_smul_cusp_not_differentiable` provide arbitrarily small cusp
  perturbations and show they destroy differentiability of every function
  differentiable at zero.

## Remaining boundary

- encode differentiability at zero as a countable union of closed
  slope-bounded subsets of `C([-1,1])`;
- prove those subsets have empty interior using small cusp or zigzag
  perturbations near zero;
- invoke the Baire theorem to prove the complement is nonmeagre, while
  reconciling the slope encoding with the ambient-extension predicate.

Closer hop 3 leaves an honest partial: the perturbation/density engine is now
compiled, but the countable closed-set decomposition needed to invoke Baire
remains open.
