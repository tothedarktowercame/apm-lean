# Informal Solution: a96J01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Answer: Such a sequence EXISTS.** We construct it explicitly.

**Construction.** Define f_n on [0,1] as a tent (triangle) function:
- f_n has support on I_n = [1 - 2^{-(n-1)}, 1 - 2^{-n}] (length 2^{-n})
- f_n peaks at the midpoint of I_n with height 1/n
- f_n is 0 outside I_n, linear on each half of I_n

The intervals I₁ = [0, 1/2], I₂ = [1/2, 3/4], I₃ = [3/4, 7/8], ... are pairwise disjoint and cover [0,1) in the limit.

**Verification 1: Continuity + nonnegativity.** Each f_n is piecewise linear (hence continuous) and nonneg by construction. ✓

**Verification 2: Σ sup f_n diverges.** sup f_n = 1/n (the peak height). So Σ sup f_n = Σ 1/n = ∞ (harmonic series). ✓

**Verification 3: Σ f_n converges uniformly.** Fix ε > 0. Choose N > 1/ε. For any x ∈ [0,1]:

- If x ∈ I_n for some n ≤ N: the partial sum S_N(x) = Σ_{k=1}^N f_k(x) = f_n(x) (since the supports are disjoint). The full sum f(x) = f_n(x) too (only one f_k is nonzero at x). So |S_N(x) - f(x)| = 0.

- If x ∈ I_n for some n > N: S_N(x) = 0 (all f_k for k ≤ N vanish at x since x ∉ I_k for k ≤ N). And f(x) = f_n(x) ≤ 1/n < 1/N < ε. So |S_N(x) - f(x)| = f_n(x) < ε.

- If x = 1 (not in any I_n): all f_k(1) = 0, so S_N(1) = f(1) = 0.

In all cases, |S_N(x) - f(x)| < ε for all x ∈ [0,1]. Since N depends only on ε (not on x), the convergence is uniform. ✓ ∎

(The trick: disjoint supports make at most one f_n nonzero at each x. The tail of the series at any point is bounded by the maximum height among the remaining terms, which is 1/(N+1). Uniform convergence follows despite the divergent sup-sum because the functions "spread out" their mass instead of concentrating it.)

**Stage 2 — LEMMA DEPENDENCY GRAPH**

| # | Lemma | Source | Critical? |
|---|-------|--------|-----------|
| 1 | Tent function on [a,b] with height h is continuous and nonneg | Custom construction | YES |
| 2 | Intervals I_n are pairwise disjoint | Geometric series: I_n = [1-2^{-(n-1)}, 1-2^{-n}] | YES |
| 3 | At each x, at most one f_n is nonzero | From disjointness of supports | YES |
| 4 | Harmonic series diverges | Mathlib: `Real.not_summable_one_div_int_cast` or similar | Standard |
| 5 | Tail bound: for n > N, f_n(x) ≤ 1/n < 1/N | From height = 1/n | Key step |

**Stage 3 — LEAN FORMALIZATION**

This is a construction problem — the formal target is an ∃ statement. The construction of the tent functions and verification of disjoint supports is doable but requires ~50 lines of piecewise-linear function definitions + interval arithmetic. The harmonic divergence is in Mathlib. The uniform convergence verification needs the disjoint-support tail bound.

Given the construction complexity, the Lean file provides the statement and the key structural pieces with sorry for the construction details.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The informal proof is clean and self-contained: the tent construction is concrete, the three verifications are each 2-3 lines. The Lean formalization would be heavy on interval arithmetic (showing the I_n are disjoint, showing the tent function is continuous, etc.) but mathematically trivial. The only non-trivial Lean component is the harmonic divergence, which is in Mathlib.

The pedagogical value: this is a counterexample to the converse of the Weierstrass M-test. The M-test says Σ sup|f_n| < ∞ implies uniform convergence. This example shows the converse fails: uniform convergence does NOT imply Σ sup|f_n| < ∞. The mechanism: disjoint supports allow uniform convergence from "spreading" rather than "shrinking."
