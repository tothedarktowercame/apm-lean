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
- `apm_m02a02_grad_jointKernel_meanZero` proves that the two gradient
  components have trivial joint kernel on the mean-zero carrier.
- `apm_m02a02_weak_unique` proves uniqueness on the prescribed affine mean
  slice by testing the difference of two weak solutions against itself. The
  remaining `sorry` now covers only Poincaré and existence.

## Remaining boundary

- Derive the Poincaré estimate by contradiction from compactness of `embed`,
  the `H¹` norm identity, and the constant-kernel characterization.
- Bundle the gradient form on the mean-zero subtype, prove coercivity from
  Poincaré, apply Mathlib's `IsCoercive.continuousLinearEquivOfBilin`, and
  transport the resulting existence witness to the affine mean constraint
  determined by `u₀`; uniqueness is already compiled separately.
- The inspected Fredholm bounded-below theorem is not directly reusable: it
  concerns compact endomorphisms, while the embedding and gradient pair here
  have different codomains.
