# Proof Outline: m00A02

The Lean artifact proves the exponential and oscillatory counterexample decay
claims, its exact derivative computation, and the derivative's failure to have
the null expansion. One analytic boundary remains.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m00A02.md`

## Formalized

- `exp (-x)` is asymptotically null using exponential domination of powers.
- The counterexample is smooth and asymptotically null by `|sin|≤1`.
- Its derivative is explicitly
  `cos (exp x) - exp (-x) * sin (exp x)`.
- Along `k ↦ log ((k+1)(2π))` the derivative is exactly one; composition with
  a hypothetical zero limit yields a contradiction by uniqueness of limits.

## Remaining Boundaries

- Formalize uniqueness and integration of the custom Poincaré expansions to
  identify the derivative coefficients under the additional expansion
  hypothesis.
