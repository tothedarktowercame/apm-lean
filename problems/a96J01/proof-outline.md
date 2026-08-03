# Proof Outline: a96J01

## Problem

For each positive integer n, let f_n : [0,1] → ℝ be continuous with f_n ≥ 0.
Suppose the partial sums converge uniformly on [0,1], yet Σ sup f_n diverges.
Show such a sequence exists (or prove it cannot).

## Answer: Yes, such a sequence exists.

## Construction

Tent (triangular bump) functions on disjoint intervals. For n : ℕ (indexed
from 0), define:
- I_n = [a_n, b_n] where a_n = 1 - 2^{-n} and b_n = 1 - 2^{-(n+1)}
- So I_0 = [0, 1/2], I_1 = [1/2, 3/4], I_2 = [3/4, 7/8], ...
- f_n is a tent on I_n with peak height 1/(n+1) at the midpoint, zero elsewhere

## Key properties

1. **Continuous and nonneg**: Tent = (1/(n+1)) * max(0, 1 - |x - mid|/hw) is
   continuous (max of continuous functions) and ≥ 0 by construction.

2. **sup f_n = 1/(n+1)**: Peak attained at midpoint (f_n(mid_n) = 1/(n+1)),
   and f_n ≤ 1/(n+1) everywhere since max(0, ...) ≤ 1.

3. **Σ sup f_n diverges**: sup f_n ≥ 1/(n+1), and Σ 1/(n+1) = ∞ (harmonic).
   Formalized via le_ciSup + Summable.of_nonneg_of_le + Real.not_summable_one_div_natCast.

4. **Uniform convergence**: Intervals have pairwise disjoint interiors, so at
   most one f_n(x) > 0 at each x. The tail ∑_{k>N} f_k(x) ≤ 1/(N+2) → 0
   uniformly. Formalized via Metric.tendstoUniformlyOn_iff + eventually_atTop.

## Lean formalization

- **File**: `lean/Main.lean`
- **Status**: Complete (0 sorries, 0 errors)
- **Key Mathlib lemmas used**: `hasSum_single` (for at-most-one-nonzero sums),
  `le_ciSup` + `ciSup_le` (for sup characterization),
  `Summable.sum_add_tsum_nat_add` (for tail decomposition),
  `Real.not_summable_one_div_natCast` (harmonic divergence),
  `Metric.tendstoUniformlyOn_iff` (uniform convergence)
- **Commit**: d1606d0

## References

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a96J01.md`
