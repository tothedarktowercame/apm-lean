# Proof Outline: a98A04

The Lean formalization is partial, with one theorem-level `sorry` remaining.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a98A04.md`

## Compiled progress

- `apm_a98a04_spike_nonneg` proves every spike is nonnegative.
- `apm_a98a04_spike_eq_zero_of_not_mem` proves its support is contained in
  `(a,b)`.
- `apm_a98a04_spike_measurable` supplies the measurability input needed by the
  integral and convergence APIs.
- `apm_a98a04_spike_pos_iff` strengthens the support result: for `a < b`, the
  spike is strictly positive exactly on `(a,b)`.
- `apm_a98a04_spike_pos_set` makes that equivalence a literal set identity.
- `apm_a98a04_spike_pos_set_measure_pos` proves the positivity set has
  strictly positive Lebesgue measure, beginning the a.e.-robustness argument.

## Remaining bridges

1. Rewrite the spike using `rpow (-1/2)`, transport through translation and
   scaling, and prove its integral is exactly `2`.
2. Enumerate rational subintervals and form a geometrically weighted spike
   series with summable L¹ norms.
3. Strengthen positivity to every finite height-level set having positive
   measure in every interval, making
   the unboundedness invariant under a.e. modification.
