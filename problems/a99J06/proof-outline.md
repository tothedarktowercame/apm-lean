# Proof Outline: a99J06

The canonical Lean attempt now completes the analytic reduction to the
simply-connected primitive theorem.

- `apm_a99j06_logDeriv_differentiableOn` proves that `f'/f` is holomorphic on
  the nonvanishing domain.
- `apm_a99j06_exists_log_of_logDeriv_exact` proves the full conclusion from
  exactness of `f'/f`: normalize a primitive, prove `f * exp (-G)` is constant,
  and absorb the constant using the complex logarithm.
- `apm_a99j06_exists_continuous_log` uses `Complex.isCoveringMap_exp` and
  `IsCoveringMap.existsUnique_continuousMap_lifts` to construct a global
  continuous logarithm directly from simple connectivity, bypassing the
  missing global-primitives theorem.

## Follow-up Needed

- Upgrade the continuous exponential lift to a holomorphic lift. Locally this
  amounts to identifying the covering-map inverse with an analytic logarithm
  branch; Mathlib currently exposes only a topological local homeomorphism.
- Alternatively, extend `DifferentiableOn.isExactOn_ball` to arbitrary open
  simply connected subsets and invoke the already-compiled exactness route.
