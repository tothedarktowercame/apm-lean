# Proof Outline: t00J01

The canonical Lean attempt is `lean/Main.lean`. Several elementary and
continuity clauses are compiled; three major topology/analysis bridges remain.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t00J01.md`

## Compiled progress

- The identity on the genuine sphere is bijective.
- The encoded sphere-identity Lefschetz number reduces to `2`, hence is not
  `1`.
- The explicit circle fold `z ↦ z * exp(2 Im z)` is continuous.
- `apm_t00j01_fold_exp` identifies the fold with the exponential of the real
  lift `θ ↦ θ + 2 sin θ`.
- `apm_t00j01_deriv_foldLift` proves that lift has derivative
  `1 + 2 cos θ`.

## Remaining boundary

- Build charts and compactness/connectedness for the explicit Klein quotient,
  then compute the top homology of its product with the circle.
- Compute integral singular homology of the genuine two-sphere in degrees
  zero, one, and two.
- Using the compiled lift and derivative identities, classify the roots of
  `θ + 2 sin θ` modulo `2π` over the two target fibers,
  prove their exact cardinalities, and verify derivative nonvanishing there.
