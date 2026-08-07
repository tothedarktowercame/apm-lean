# Proof Outline: m00A02

The Lean artifact proves the exponential and oscillatory counterexample decay
claims and now includes the exact derivative computation. Two analytic
boundaries remain.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m00A02.md`

## Formalized

- `exp (-x)` is asymptotically null using exponential domination of powers.
- The counterexample is smooth and asymptotically null by `|sin|≤1`.
- Its derivative is explicitly
  `cos (exp x) - exp (-x) * sin (exp x)`.

## Remaining Boundaries

- Compose a hypothetical zero limit with
  `k ↦ log ((k+1)(2π))`, where the explicit derivative equals one.
- Formalize uniqueness and integration of the custom Poincaré expansions to
  identify the derivative coefficients under the additional expansion
  hypothesis.
