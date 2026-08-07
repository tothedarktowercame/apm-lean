# Proof Outline: m03J04

The canonical Lean attempt is `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m03J04.md`

## Closer hop 1 progress

- Double transposition and closedness of the custom annihilator are complete.
- The new helper `apm_m03J04_range_subset_dualAnnihilator` proves that every
  range element annihilates the kernel of the flipped pairing.
- Mathlib supplies `ContinuousLinearMap.orthogonal_ker`,
  `Submodule.orthogonal_orthogonal_eq_closure`, and the algebraic
  `Submodule.dualCoannihilator_range_eq_ker_flip`. The remaining closure
  equality must transport orthogonal complements through the Riesz equivalence
  and identify them with the custom continuous-dual annihilator.
- The inf-sup clause additionally needs the signed `sSup` identified with
  `‖B v‖`; only then can the existing antilipschitz and closed-range APIs build
  the requested subtype-valued `ContinuousLinearEquiv`.

## Closer hop 2 research

- `ContinuousLinearMap.sSup_sphere_eq_norm` supplies the norm supremum directly.
  The signed quotient differs only by normalization and sign reversal.
- `ContinuousLinearMap.orthogonal_ker` returns the desired closure-of-adjoint-
  range identity in Hilbert-space form. The remaining blocker is transporting
  it through `InnerProductSpace.toDual` and identifying its orthogonal with the
  custom evaluation-kernel annihilator.
