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

## Closer Hop 3 Progress

- `apm_a01J06_finite_preimage_of_enumeratesZeros` proves that indices mapping
  into any finite set of complex values form a finite set.
- `apm_a01J06_card_preimage_eq_finsum_analyticOrder` proves the exact finite
  multiplicity identity
  `Nat.card {n // ω n ∈ s} = ∑ᶠ z ∈ s, analyticOrderNatAt f z`.
  It decomposes the preimage into pairwise-disjoint fibers and uses
  `Set.Finite.ncard_biUnion` together with the frozen fiber-cardinality
  hypothesis.

Thus the abstract finite-fiber aggregation step is closed. The remaining
divisor work is to extract its finite disk support and identify that support's
mass with the Jensen/log-counting expression before proving the linear bound
and dyadic summability estimate.

## Hop 4: exact missing contracts

The remaining work has been reduced to two precise reusable lemmas:

1. `apm_a01J06_linear_zero_count`: the analytic hypotheses and
   multiplicity-preserving enumeration imply that every disk-index subtype is
   finite and its cardinality is bounded by `C * R` for `R ≥ 1`.
2. `apm_a01J06_summable_of_linear_count`: any complex sequence satisfying
   that finite linear disk-count bound has summable weights
   `(1 + ‖omega n‖) ^ (-α)` for every `α > 1`.

Finiteness is included explicitly in both contracts; relying on `Nat.card`
alone would be invalid because it totalizes infinite types to zero.
