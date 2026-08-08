# Proof Outline: m93A04

The frozen Lean theorem is present in `lean/Main.lean`. The entire bijectivity
conjunct is now closed. The kernel formula identifies the integral part with
`1 - D x`, its norm is at most `c`, and the abstract Neumann lemma applies.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m93A04.md`

## Remaining boundary

- package differentiation under the parameterized integral, including the
  uniform remainder in the `ContinuousMap` sup norm, measurability, and
  domination hypotheses.

The operator estimate uses compact-domain integrability, the Bochner integral
norm inequality, pointwise control by the continuous-map norm, and the
probability-volume instance on `[0,1]`. Mathlib's dominated parametric-integral
lemmas remain relevant to differentiability, but they do not directly package
the uniform Nemytskii remainder into the continuous-map codomain.
