# Proof Outline: a99J06

The canonical Lean attempt now completes the analytic reduction to the
simply-connected primitive theorem.

- `apm_a99j06_logDeriv_differentiableOn` proves that `f'/f` is holomorphic on
  the nonvanishing domain.
- `apm_a99j06_exists_log_of_logDeriv_exact` proves the full conclusion from
  exactness of `f'/f`: normalize a primitive, prove `f * exp (-G)` is constant,
  and absorb the constant using the complex logarithm.

## Follow-up Needed

- Extend Mathlib's `DifferentiableOn.isExactOn_ball` to arbitrary open simply
  connected subsets of `ℂ`; this extension is explicitly listed as a TODO in
  `Analysis.Complex.HasPrimitives`.
- Apply that theorem to `f'/f` and invoke the compiled conditional lemma.
