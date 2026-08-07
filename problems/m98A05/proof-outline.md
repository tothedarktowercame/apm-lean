# Proof Outline: m98A05

The canonical Lean attempt is `lean/Main.lean`. The concrete Dirichlet
existence clause is closed by the zero solution, while reusable differentiable
bridges for the two implicit-function clauses are compiled locally.

- `apm_m98a05_hasStrictFDerivAt_of_contDiff` converts a specified derivative
  of a globally `C¹` map into the strict derivative required by Mathlib's IFT.
- `apm_m98a05_contDiff_perturbation` proves that
  `(x, ε) ↦ F x + ε • G x` is `C¹`.
- The final BVP clause uses `w = dw = d2w = 0`, which satisfies every weak
  derivative, trace, integrability, and equation requirement for all `ε`.

## Remaining Boundary

- Reorient the product domain for `ContDiffAt.implicitFunction` and identify
  the supplied partial derivative equivalence.
- Extract open neighborhoods and a `ContDiffOn` solution from the eventual
  equality and uniqueness statements.
- For the perturbation clause, prove the partial derivative at `(x₀,0)` is
  exactly `A`, then extract a symmetric real interval.
