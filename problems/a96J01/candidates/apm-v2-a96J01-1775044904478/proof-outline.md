# Proof Outline: a96J01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal
 "Exhibit f_n : [0,1] → ℝ nonneg continuous with Σf_n uniformly convergent but Σ sup f_n divergent. Answer: such sequences exist."
 :terms
 [{:name "disjoint-support bumps"
   :meaning "f_n supported on I_n = [1-2^{-(n-1)}, 1-2^{-n}], pairwise disjoint"
   :needed-because "disjoint supports make the tail bounded by max height, not sum of heights"}
  {:name "height 1/n"
   :meaning "sup f_n = 1/n, so Σ sup f_n = harmonic = ∞"
   :needed-because "gives divergent sup-sum"}
  {:name "uniform convergence via disjointness"
   :meaning "at each x, at most one f_n nonzero ⟹ tail ≤ 1/(N+1) → 0 uniformly"
   :needed-because "gives uniform convergence despite divergent sup-sum"}]
 :strategy
 [{:id :construct-tent-bumps
   :formal-dependency "piecewise-linear tent functions on disjoint intervals"
   :informal-dependency "triangle bumps with height 1/n on shrinking disjoint intervals"
   :why-this-now "the construction IS the proof — once built, all properties are immediate"
   :lean-target "def f : ℕ → ℝ → ℝ with disjoint tent bumps"
   :mathlib-status "custom construction"
   :critical-path true}
  {:id :harmonic-diverges
   :formal-dependency "¬ Summable (fun n => 1/(n+1 : ℝ))"
   :informal-dependency "Σ 1/n = ∞"
   :why-this-now "immediate from height = 1/n"
   :lean-target "not_summable_one_div_nat_cast"
   :mathlib-status "available in Mathlib"
   :critical-path false}
  {:id :uniform-convergence-from-disjointness
   :formal-dependency "TendstoUniformlyOn with tail bound ≤ 1/(N+1)"
   :informal-dependency "disjoint supports ⟹ at each x, tail is at most one term ≤ 1/(N+1)"
   :why-this-now "key verification step"
   :lean-target "TendstoUniformlyOn (partial sums) (pointwise limit) atTop (Icc 0 1)"
   :mathlib-status "Mathlib has TendstoUniformlyOn; bound wiring is custom"
   :critical-path true}]
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
  :frame-id "apm-v2-a96J01-1775044904478"
  :summary "Created isolated proof frame workspace."
  :full-record? false
  :sorry? false
  :fully-closed? false}
 {:kind :target-check
  :summary "Existence problem: construct disjoint-support tent functions with height 1/n. Construction is the entire proof."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Clean construction: tent functions on I_n = [1-2^{-(n-1)}, 1-2^{-n}] with height 1/(n+1). Three verifications: continuous+nonneg, Σ sup = harmonic = ∞, uniform convergence via disjoint supports (tail ≤ 1/(N+1))."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :lean-delta
  :summary "iLeft_lt_iRight CLOSED (interval nonemptiness). Main theorem type-checks with 1 sorry. The construction verification is interval arithmetic + harmonic divergence."
  :full-record? true
  :sorry? true
  :fully-closed? false}
 {:kind :final-status
  :summary "Classification: partial. Informal proof complete. Lean: 1 helper closed, 1 sorry (full construction). Counterexample to converse of Weierstrass M-test."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

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
