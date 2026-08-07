# Proof Outline: a98A04

The Lean formalization is partial, with one theorem-level `sorry` remaining.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a98A04.md`

## Compiled progress

- `apm_a98a04_spike_nonneg` proves every spike is nonnegative.
- `apm_a98a04_spike_eq_zero_of_not_mem` proves its support is contained in
  `(a,b)`.

## Remaining bridges

1. Rewrite the spike using `rpow (-1/2)`, transport through translation and
   scaling, and prove its integral is exactly `2`.
2. Enumerate rational subintervals and form a geometrically weighted spike
   series with summable L¹ norms.
3. Prove every height-level set has positive measure in every interval, making
   the unboundedness invariant under a.e. modification.
