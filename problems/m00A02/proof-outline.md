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
- `apm_m00A02_expansion_coefficients_unique` proves coefficient uniqueness by
  strong induction: after cancelling lower-order terms, the difference of the
  two order-`N` remainders is eventually the constant `c N - a N`, which must
  vanish by uniqueness of limits.

## Remaining Boundaries

- Formalize integration of the derivative expansion from infinity. In
  particular, derive that its first two coefficients vanish, integrate each
  remainder estimate on `[x, +∞)`, and connect the result to `f` through the
  improper fundamental theorem of calculus. Coefficient comparison is now
  supplied by the compiled uniqueness lemma.
