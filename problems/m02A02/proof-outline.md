# Proof Outline: m02A02

The canonical Lean attempt is `lean/Main.lean`. It formalizes the abstract
periodic Sobolev structure and has one remaining compactness/variational core.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m02A02.md`

## Compiled progress

- `apm_m02a02_completeSpace_meanZero` proves the mean-zero carrier is complete
  as the closed kernel of the continuous mean functional.
- `apm_m02a02_weak_iff_strong` derives the full weak/strong equivalence from
  Green's identity, the forcing and Laplacian mean conditions, and density of
  the embedded mean-zero tests.

## Remaining boundary

- Derive the Poincaré estimate by contradiction from compactness of `embed`,
  the `H¹` norm identity, and the constant-kernel characterization.
- Bundle the gradient form on the mean-zero subtype, prove coercivity from
  Poincaré, apply Mathlib's `IsCoercive.continuousLinearEquivOfBilin`, and
  transport the result to the affine mean constraint determined by `u₀`.
