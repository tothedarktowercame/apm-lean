# Proof Outline: a99J04

The canonical Lean proof is complete and sorry-free. It establishes:

- `apm_a99J04_zero_mutuallySingular`: zero is mutually singular with every
  measure;
- `apm_a99J04_mu3_eq_ac31`: the `x²` density description of `μ₃`;
- `apm_a99J04_mu2_eq_ac21`: the indicator-density description of `μ₂`, using
  `withDensity_indicator_one` and restriction composition.
- `apm_a99J04_mu1_eq_ac13`: reciprocal cancellation via
  `withDensity_mul₀`, outside the volume-null singleton `{0}`.
- `apm_a99J04_mu2_eq_ac23`: restriction of the preceding reciprocal identity
  to `(0,1)` and conversion via `withDensity_indicator`.
- `apm_a99J04_mu1_split` and `apm_a99J04_mu3_split`: the two complementary
  restriction decompositions.
- `apm_a99J04_restrict_compl_mutuallySingular`: complementary restrictions
  of arbitrary measures are mutually singular.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a99J04.md`

## Remaining boundary

None.
