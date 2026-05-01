# Informal Solution: a96J01

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

**Stage 1 — THE CLEAN PROOF**

**Answer: Such a sequence EXISTS.**

**Construction.** Define f_n on [0,1] as a tent function:
- f_n supported on I_n = [1 - 2^{-(n-1)}, 1 - 2^{-n}] (length 2^{-n})
- f_n peaks at the midpoint of I_n with height 1/n
- f_n = 0 outside I_n, piecewise linear on each half

The intervals I₁=[0,1/2], I₂=[1/2,3/4], I₃=[3/4,7/8], ... are pairwise disjoint.

**Verification 1: Continuity + nonnegativity.** Each f_n is piecewise linear (continuous) and nonneg. ✓

**Verification 2: Σ sup f_n diverges.** sup f_n = 1/n. So Σ sup f_n = Σ 1/n = ∞. ✓

**Verification 3: Σ f_n converges uniformly.** Fix ε > 0, choose N > 1/ε. For any x ∈ [0,1]:
- If x ∈ I_n for n ≤ N: S_N(x) = f_n(x) = f(x) (disjoint supports), so |S_N(x) - f(x)| = 0.
- If x ∈ I_n for n > N: S_N(x) = 0, f(x) = f_n(x) ≤ 1/n ≤ 1/(N+1) < ε.
- If x = 1: all f_k(1) = 0, so S_N(1) = f(1) = 0.

In all cases |S_N(x) - f(x)| < ε uniformly. ✓ ∎

**Stage 2 — LEMMA DEPENDENCY GRAPH**

| # | Lemma | Source | Critical? |
|---|-------|--------|-----------|
| 1 | Tent on [a,b] continuous nonneg | Custom | YES |
| 2 | I_n pairwise disjoint | Geometric: I_n ∩ I_m = ∅ for n ≠ m | YES |
| 3 | At each x, at most one f_n nonzero | From (2) | YES |
| 4 | Σ 1/n diverges | Mathlib: harmonic | Standard |
| 5 | Tail bound: max_{n>N} f_n(x) ≤ 1/(N+1) | From height + disjointness | Key |

**Stage 3 — LEAN FORMALIZATION**

The construction requires defining the tent function family and proving disjoint support properties. The `intervalLeft_lt_intervalRight` helper (showing the intervals are nonempty) was closed in the previous frame. The main existence theorem has 1 sorry — the full construction verification is ~50 lines of interval arithmetic.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The informal proof is clean: 3 lines of construction, 3 verifications of ~2 lines each. The Lean formalization would be heavy on interval arithmetic but mathematically trivial. The pedagogical insight: this is a counterexample to the converse of the Weierstrass M-test. M-test gives Σ sup < ∞ ⟹ uniform convergence. The converse fails: uniform convergence does NOT require Σ sup < ∞. The mechanism: "spreading" (disjoint supports) instead of "shrinking" (small sups).
