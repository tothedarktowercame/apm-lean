# Proof Outline: m02A01

The canonical Lean attempt is `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m02A01.md`

## Formal proof

- Weak-limit uniqueness, strong-to-weak convergence, and failure of strong
  convergence for the `ℓ²` basis are already complete.
- Weak convergence of the `ℓ²` basis is complete. The proof applies the generic
  weak-bilinear convergence criterion, represents each functional using
  `InnerProductSpace.toDual`, obtains coordinate decay from
  `(lp.memℓp y).summable` and `Summable.tendsto_atTop_zero`, and evaluates basis
  pairings with `lp.inner_single_right`.
- Finite-dimensional weak-to-strong convergence is proved using the coordinate
  construction from sibling `m99A05`: `Module.finBasis` gives finitely many
  continuous coordinates, weak convergence gives coordinatewise convergence,
  and `equivFun.toContinuousLinearEquiv.symm` transports it back to norm
  convergence.

There are no remaining proof obligations.
