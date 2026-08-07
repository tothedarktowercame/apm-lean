# Proof Outline: a99J06

The canonical Lean attempt now completes the analytic reduction to the
simply-connected primitive theorem.

- `apm_a99j06_logDeriv_differentiableOn` proves that `f'/f` is holomorphic on
  the nonvanishing domain.

## Follow-up Needed

- Extend Mathlib's `DifferentiableOn.isExactOn_ball` to arbitrary open simply
  connected subsets of `ℂ`; this extension is explicitly listed as a TODO in
  `Analysis.Complex.HasPrimitives`.
- Apply that theorem to `f'/f` and choose a primitive `G`.
- Prove `f * exp (-G)` has zero derivative and is constant on `Ω`.
- Take a complex logarithm of the resulting nonzero constant and add it to `G`.
