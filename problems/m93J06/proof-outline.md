# Proof Outline: m93J06

The frozen Lean theorem is present in `lean/Main.lean`. Basic flow projections
are now proved: every flow is the identity at time zero, each trajectory has
the encoded derivative, and the final stability inequality is exact at zero.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m93J06.md`

## Remaining boundary

- globalize compatible Picard–Lindelöf solutions from compact time intervals;
- prove `C¹` dependence of the flow on initial data;
- formalize two distinct global solutions for a Hölder square-root field;
- apply Gronwall separately for positive and negative time and translate its
  distance estimate to the displayed absolute-value inequality.

Mathlib constructs local flows Lipschitz in initial data and provides ODE
uniqueness/stability. No searched result packages the required globalization
or differentiable parameter dependence.
