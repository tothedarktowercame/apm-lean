# Proof Outline: m95A04

Closer hop 4 leaves the theorem partial but compiles three independent pieces
of the frozen conjunction and its supporting calculus:

1. `apm_m95A04_regular_iff_ae` proves equality of regular distributions iff
   their locally integrable representatives agree almost everywhere.  The
   forward implication uses `ae_eq_of_integral_contDiff_smul_eq`; the reverse
   implication is integral congruence under a.e. equality.
2. `apm_m95A04_Dtest_injective` proves injectivity of differentiation on test
   functions.  Equal derivatives make the difference constant by
   `is_const_of_deriv_eq_zero`, and compact support forces that constant to be
   zero.
3. `apm_m95A04_integral_deriv_testFunction_eq_zero` splits the real-line
   integral at zero and applies
   `HasCompactSupport.integral_Iic_deriv_eq` and
   `HasCompactSupport.integral_Ioi_deriv_eq`. This supplies the endpoint
   calculation needed for noninjectivity of distributional differentiation.

The remaining boundary is the three explicit distributional integration by
parts identities, their packaging into noninjectivity on distributions, and
completeness of the custom weak derivative graph. The boundary comment now
records the three missing integral equalities verbatim and specifies the exact
completeness proposition under the theorem's graph and norm hypotheses.
Mathlib supplies completeness of `Lp` and its products, but not closedness of
this representative-level graph.
