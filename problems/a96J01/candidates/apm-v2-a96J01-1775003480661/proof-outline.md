# Proof Outline: a96J01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal
 "Exhibit a sequence f_n : [0,1] → ℝ of nonneg continuous functions such that Σ f_n converges uniformly on [0,1] but Σ sup f_n diverges."
 :terms
 [{:name "disjoint-support bumps"
   :meaning "f_n has support on [(1-2^{-n+1}), (1-2^{-n})], disjoint from all other f_m"
   :needed-because "disjoint supports make the partial sum equal to the pointwise limit except on one interval"}
  {:name "height 1/n"
   :meaning "sup f_n = 1/n, so Σ sup f_n = Σ 1/n = ∞ (harmonic series)"
   :needed-because "this gives the divergence of the sup-sum"}
  {:name "uniform convergence"
   :meaning "for N large, |Σ_{n>N} f_n(x)| ≤ 1/(N+1) for all x, since at most one f_n is nonzero at each x"
   :needed-because "the disjoint support structure makes the tail bounded by max height = 1/(N+1)"}]
 :strategy
 [{:id :construct-bumps
   :formal-dependency "piecewise linear functions on disjoint intervals"
   :informal-dependency "triangle/tent functions with support on [(1-2^{-(n-1)}), (1-2^{-n})] and height 1/n"
   :why-this-now "the construction is the entire proof — once built, all three properties are immediate"
   :lean-target "def f (n : ℕ) : ℝ → ℝ with the bump on the n-th interval"
   :mathlib-status "custom construction; Mathlib has ContinuousMap but not this specific family"
   :critical-path true}
  {:id :verify-uniform-convergence
   :formal-dependency "UniformCauchyCriterion or direct ε-δ"
   :informal-dependency "disjoint supports ⟹ tail sum bounded by max_{n>N} (1/n) = 1/(N+1)"
   :why-this-now "this is the key verification after construction"
   :lean-target "TendstoUniformly (partial sums) f atTop"
   :mathlib-status "Mathlib has TendstoUniformly; wiring the bound is custom"
   :critical-path true}
  {:id :verify-divergence
   :formal-dependency "harmonic series diverges"
   :informal-dependency "Σ 1/n = ∞ — standard"
   :why-this-now "immediate from height = 1/n"
   :lean-target "¬ Summable (fun n => (1 : ℝ) / n) or ∑' = ⊤"
   :mathlib-status "available: Real.not_summable_one_div_nat_cast or similar"
   :critical-path false}]
 :stage-status
 {:stage1 :done
  :stage2 :done
  :stage3 :in-progress
  :stage4 :done}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id "a96J01"
  :frame-id "apm-v2-a96J01-1775003480661"
  :summary "Created isolated proof frame workspace."
  :full-record? false
  :sorry? false
  :fully-closed? false}
 {:kind :target-check
  :summary "Existence problem: construct disjoint-support tent functions with height 1/n. Sanity check passed: mentions f_n, continuity, nonnegativity, uniform convergence, divergent sups."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Construction: tent functions on I_n = [1-2^{-(n-1)}, 1-2^{-n}] with height 1/(n+1). Three verifications: continuity+nonneg (by construction), Σ sup = Σ 1/n = ∞ (harmonic), uniform convergence (disjoint supports ⟹ tail ≤ 1/(N+1))."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :lean-delta
  :summary "intervalLeft_lt_intervalRight CLOSED (helper for interval structure). Main theorem type-checks with 1 sorry. The construction verification (~50 lines of interval arithmetic + harmonic divergence) is the remaining work."
  :full-record? true
  :sorry? true
  :fully-closed? false}
 {:kind :final-status
  :summary "Classification: partial. Informal proof complete (explicit construction + 3 verifications). Lean: helper closed, main theorem 1 sorry. The sorry is the full construction+verification, which is computationally heavy but mathematically straightforward."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

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
