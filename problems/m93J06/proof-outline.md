# Proof Outline: m93J06

The frozen Lean theorem is present in `lean/Main.lean`. Basic flow projections
are now proved: every flow is the identity at time zero, each trajectory has
the encoded derivative, and the final stability inequality is exact at zero.
The explicit square-root counterexample now has two compiled, distinct global
solutions: the zero curve and `t ↦ t|t|`. Its global exponent-`1/2` Hölder
estimate is also compiled, closing the fourth frozen conjunct completely.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m93J06.md`

## Remaining boundary

- globalize compatible Picard–Lindelöf solutions from compact time intervals;
- prove `C¹` dependence of the flow on initial data;
- apply Gronwall separately for positive and negative time and translate its
  distance estimate to the displayed absolute-value inequality.

`apm_m93j06_abs_sqrt_sub_sqrt_le_sqrt_abs_sub`,
`apm_m93j06_sqrt_field_holder`, and `apm_m93j06_not_holder_unique` contain the
completed Hölder counterexample argument.

Mathlib constructs local flows Lipschitz in initial data and provides ODE
uniqueness/stability. No searched result packages the required globalization
or differentiable parameter dependence.

## Hop 4: precise missing globalization interface

No existing declaration turns the local Picard solutions into a solution on
all of `ℝ`. The required theorem is recorded verbatim in the boundary comment
as `apm_m93j06_global_exists_unique_of_continuous_lipschitz`. Its hypotheses
are exactly global continuity and a uniform Lipschitz constant, and its
conclusion is the custom global solution predicate with uniqueness.

Mathlib's `ODE_solution_unique_univ` handles compatibility once global
solutions exist, but does not construct them. Closing the interface therefore
requires an exhaustion by compact time intervals, a continuation bound, and
gluing by uniqueness. No false or unproved declaration was added.
