# Proof Outline: a01J06

The frozen theorem states the convergence-exponent bound for a multiplicity-
preserving enumeration of the zeros of a nonzero entire function of
exponential type.

Imported source: `lean-proofs/a01J06`

## Imported Lean Files

- `lean/Main.lean`

## Closer Hop 2 Progress

- Mathlib's current `Analysis.Complex.JensenFormula` does contain Jensen's
  formula and the divisor/log-counting reformulation needed for the analytic
  route.
- `apm_a01J06_apply_eq_zero_of_enumeratesZeros` now compiles. It proves that
  every value of the supplied enumeration is an actual zero, using positivity
  of the finite fiber cardinality and
  `apply_eq_zero_of_analyticOrderNatAt_ne_zero`.
- The historical attempt at commit `a8f8752` is not reusable: its zero-count
  function is definitionally zero and unrelated to the zero sequence, and the
  artifact itself exhibits the resulting counterexample.

## Remaining Bridge

1. Bound Mathlib's logarithmic divisor count using Jensen's formula and the
   exponential-type estimate, then extract an ordinary `O(r)` zero count.
2. Identify divisor multiplicities in a disk with the finite fibers specified
   by `apm_a01J06_EnumeratesZeros`.
3. Convert the linear disk count into summability of the weighted sequence by
   a dyadic-shell estimate and the geometric-series criterion for `α > 1`.
