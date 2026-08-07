# Proof Outline: a99J04

The canonical Lean attempt is `lean/Main.lean`.  Closer hop 1 establishes
three reusable components without changing the theorem statement:

- `apm_a99J04_zero_mutuallySingular`: zero is mutually singular with every
  measure;
- `apm_a99J04_mu3_eq_ac31`: the `x²` density description of `μ₃`;
- `apm_a99J04_mu2_eq_ac21`: the indicator-density description of `μ₂`, using
  `withDensity_indicator_one` and restriction composition.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a99J04.md`

## Remaining boundary

- cancel the reciprocal density against `x²` away from the volume-null point
  zero, using `withDensity_withDensity` and an almost-everywhere identity;
- split `μ₁` and `μ₃` into restrictions to `(0,1)` and its complement;
- prove those complementary restrictions mutually singular with the measures
  supported on `(0,1)`;
- assemble the six conjunctions from these helpers.
