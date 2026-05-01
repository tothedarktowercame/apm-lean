# Proof Outline: a96J01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:problem-id 'a96J01
 :frame-id 'apm-v2-a96J01-1774994639526
 :goal "Exhibit nonnegative continuous functions on [0,1] whose partial sums converge uniformly but whose sup norms form a divergent series."
 :terms [{:name "tent function"
          :meaning "x ↦ max(0, 1 - |x-c|/r)"
          :needed-because "gives continuous bumps with prescribed height and support"
         }
         {:name "disjoint support"
          :meaning "dyadic intervals I_n share at most endpoints"
          :needed-because "ensures at most one term contributes at each x"
         }
         {:name "harmonic divergence"
          :meaning "∑ 1/n diverges"
          :needed-because "establishes the failure of the M-test"}]
 :strategy [{:id :s1
             :formal-dependency "Continuity of max/abs and linear operations"
             :informal-dependency "Stage 1 definition of f_n"
             :why-this-now "Certify each f_n is continuous and nonnegative"
             :lean-target "continuous_tent_on_interval"
             :mathlib-status "missing; needs manual definition"}
            {:id :s2
             :formal-dependency "Order properties of dyadic intervals"
             :informal-dependency "Disjoint support argument"
             :why-this-now "Prove at most one tent is active at any point"
             :lean-target "tent_supportS_disjoint"
             :mathlib-status "missing"}
            {:id :s3
             :formal-dependency "Tail estimate / harmonic divergence"
             :informal-dependency "Uniform tail bound and divergent ∑‖f_n‖∞"
             :why-this-now "Translate combinatorics to uniform convergence and divergence statements"
             :lean-target "tent_sequence_exists"
             :mathlib-status "blocked by s1/s2"}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}
 :lean {:module-root 'ApmCanaries.Frames.A96J01.Apm_v2_a96J01_1774994639526
        :shared-extension-root "ApmCanaries.Local"}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :summary "Initialized frame and noted tent-function approach."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Documented the dyadic-tent construction and analytic proof in execute.md."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Recorded the supporting lemmas, uniform-tail estimate, and harmonic divergence dependencies."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-blocked
  :summary "Lean work pending: Mathlib lacks a ready-made tent bump; need custom continuity/support lemmas before encoding `tent_sequence_exists`."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

For each `n ≥ 1` choose the disjoint interval `I_n = [2^{-(n+1)}, 2^{-n}] ⊂ (0,1]`. Let `m_n` be its midpoint and `r_n` half its length. Define a “tent”
```
φ_n(x) = max(0, 1 - |x - m_n| / r_n)
```
and set `f_n(x) = φ_n(x)/n`. Each `f_n` is continuous, non-negative, supported in the interior of `I_n`, and satisfies `‖f_n‖_∞ = 1/n` (the peak occurs at `m_n`). Because the supports are disjoint and `φ_n` vanishes at the interval endpoints, at most one `f_n` is non-zero at any `x`. Consequently, if `S_N(x) = ∑_{n=1}^N f_n(x)` and `S(x) = lim_N S_N(x)`, then `S` is continuous, `S_N → S` uniformly, and
```
|S(x) - S_N(x)| = ∑_{n>N} f_n(x) ≤ sup_{n>N} ‖f_n‖_∞ = 1/(N+1).
```
Finally `∑_{n=1}^∞ ‖f_n‖_∞ = ∑_{n=1}^∞ 1/n = +∞`, so the series of sup norms diverges even though the functions converge uniformly.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- **Tent continuity/nonnegativity.** Uses that compositions of continuous functions and `max` stay continuous, and that the tent formula is ≥ 0.
- **Disjoint support.** From the dyadic intervals `I_n`: if both `φ_n(x)`, `φ_m(x)` are positive then the point lies in the intersection, which can only happen at shared endpoints where the tents vanish, so at most one summand contributes.
- **Uniform tail bound.** Disjoint support implies `∑_{n>N} f_n(x) ≤ sup_{n>N} 1/n = 1/(N+1)` uniformly in `x`, giving uniform convergence.
- **Divergent sup norms.** Harmonic series diverges, so `∑ ‖f_n‖_∞ = ∑ 1/n = ∞`.

**Stage 3 — LEAN FORMALIZATION**

Plan: encode the tent explicitly via
```
f n x = (Nat.succ n)⁻¹ * max 0 (1 - |x - mid n| / rad n)
```
where `mid n` and `rad n` describe the dyadic geometry. Needed ingredients: continuity of the tent, a lemma stating that tents on our dyadic family have pairwise disjoint supports, and a tail estimate `∀ x, ∑_{k≥N} f k x ≤ 1/(N+1)`. Once those are available we can conclude uniform convergence via the Cauchy criterion and note `¬ Summable (fun n => 1/(n+1))`. At the moment Mathlib lacks a prepackaged “triangular bump” API, so all these support/continuity calculations must be written manually; this is the blocker that prevented finishing the Lean proof in this pass.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The informal solution already matches the planned Lean construction: both rely on dyadic tents. Once the tent lemmas are formalized, cite the resulting Lean theorem (the target is `tent_sequence_exists` described in Stage 3) in Stage 1, and note explicitly that the harmonic-series divergence uses `Mathlib.Analysis.PSeries.not_summable_one_div_natCast`.
