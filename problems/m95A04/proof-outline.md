# Proof Outline: m95A04

Closer hop 3 compiled two independent pieces of the frozen conjunction:

1. `apm_m95A04_regular_iff_ae` proves equality of regular distributions iff
   their locally integrable representatives agree almost everywhere.  The
   forward implication uses `ae_eq_of_integral_contDiff_smul_eq`; the reverse
   implication is integral congruence under a.e. equality.
2. `apm_m95A04_Dtest_injective` proves injectivity of differentiation on test
   functions.  Equal derivatives make the difference constant by
   `is_const_of_deriv_eq_zero`, and compact support forces that constant to be
   zero.

The remaining boundary is the three explicit distributional integration by
parts identities, noninjectivity on distributions (which needs the integral of
a compactly supported derivative), and completeness of the custom weak
derivative graph.  Mathlib supplies completeness of `Lp` and its products, but
not closedness of this representative-level graph.
