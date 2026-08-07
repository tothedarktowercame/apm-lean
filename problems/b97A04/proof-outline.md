# Proof Outline: b97A04

The canonical Lean proof compiles without `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b97A04.md`

## Compiled progress

- `apm_b97a04_module_finite` chooses a nonzero cyclic vector in the simple
  module and transfers finite generation from `R` to `V`.
- `apm_b97a04_schur_and_scalars` proves the three Schur-theoretic conjuncts:
  nonzero endomorphisms are units, the endomorphism space is finite over
  `ℂ`, and every `R`-endomorphism is scalar.

## Completed bridge

- `apm_b97a04_burnside` makes `V` finite over its `R`-endomorphism division
  ring, applies Jacobson density, and uses Schur scalarity to show that every
  complex-linear endomorphism lies in the image of `R`.
- `apm_b97a04_modules_are_copies` identifies the complex endomorphism algebra
  with a full matrix algebra, transports simple-ring structure back to `R`,
  combines it with finite-dimensional Artinianness, and proves every simple
  constituent is equivalent to `V`.
- `IsIsotypicOfType.linearEquiv_finsupp` then gives the requested decomposition
  for arbitrary, possibly infinite, modules.
