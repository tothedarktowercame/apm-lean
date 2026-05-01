# Proof Outline: a00J01

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal
 "State the definition of ‖f‖_∞ (essential supremum) and prove lim_{p→∞} ‖f‖_p = ‖f‖_∞ for f ∈ L^∞([0,1])."
 :terms
 [{:name "essential supremum"
   :meaning "inf{M ≥ 0 : m({|f| > M}) = 0} — the smallest M bounding |f| a.e."
   :needed-because "this is the definition the problem asks us to state"}
  {:name "upper bound direction"
   :meaning "|f| ≤ ‖f‖_∞ a.e. implies ‖f‖_p ≤ ‖f‖_∞ on a finite measure space"
   :needed-because "gives lim sup ‖f‖_p ≤ ‖f‖_∞"}
  {:name "lower bound via level sets"
   :meaning "for α < ‖f‖_∞, the set {|f| > α} has positive measure, giving ‖f‖_p ≥ α · m(E_α)^{1/p}"
   :needed-because "gives lim inf ‖f‖_p ≥ ‖f‖_∞ after sending α ↑ ‖f‖_∞"}
  {:name "t^{1/p} → 1"
   :meaning "for t > 0, t^{1/p} → 1 as p → ∞"
   :needed-because "the factor m(E_α)^{1/p} must converge to 1 in the lower bound"}]
 :strategy
 [{:id :upper-bound
   :formal-dependency "eLpNorm_le_eLpNorm_mul_rpow_measure_univ with q=⊤"
   :informal-dependency "|f| ≤ ‖f‖_∞ a.e. + Hölder on finite measure space"
   :why-this-now "one direction of the sandwich, and it's a single Mathlib lemma"
   :lean-target "eLpNorm f p μ ≤ eLpNorm f ⊤ μ when μ is probability"
   :mathlib-status "available: eLpNorm_le_eLpNorm_mul_rpow_measure_univ"
   :critical-path true}
  {:id :lower-bound
   :formal-dependency "essSup definition + level set measure + rpow limit"
   :informal-dependency "ess sup definition guarantees E_α has positive measure for α < ‖f‖_∞"
   :why-this-now "the other direction of the sandwich, conceptually the hard part"
   :lean-target "∀ α < eLpNormEssSup f μ, liminf ‖f‖_p ≥ α"
   :mathlib-status "custom: needs essSup contrapositive + rpow_tendsto lemmas"
   :critical-path true}
  {:id :squeeze
   :formal-dependency "tendsto_of_tendsto_of_tendsto_of_le_of_le"
   :informal-dependency "both bounds give the limit by squeeze"
   :why-this-now "combines the two directions"
   :lean-target "Tendsto (eLpNorm f · μ) atTop (nhds (eLpNormEssSup f μ))"
   :mathlib-status "available: squeeze theorem in Mathlib"
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
  :problem-id "a00J01"
  :frame-id "apm-v2-a00J01-1774990935426"
  :summary "Created isolated proof frame workspace with plan/changelog/Lean scratch roots."
  :full-record? false
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Clean proof: sandwich argument. Upper: |f|≤‖f‖_∞ a.e. gives ‖f‖_p ≤ ‖f‖_∞ on finite measure. Lower: for α<‖f‖_∞, E_α has positive measure, ‖f‖_p ≥ α·m(E_α)^{1/p} → α. Squeeze gives the limit."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Dependency graph: 4 lemmas. Upper bound via eLpNorm_le_eLpNorm_mul_rpow_measure_univ (Mathlib). Lower bound needs essSup definition + level set measure + rpow limit. Squeeze via tendsto_of_le_of_ge."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :lean-delta
  :summary "Lean skeleton type-checks: upper_bound, lower_bound, eLpNorm_tendsto_top. 3 sorry. Upper bound blocked on volume(Icc 0 1) = 1 simplification after Mathlib comparison. Lower bound needs level set + rpow limit. Main theorem is composition."
  :full-record? true
  :sorry? true
  :fully-closed? false}
 {:kind :stage4-completed
  :summary "Formal-to-informal revision: upper bound is genuinely easy (one Mathlib lemma on probability spaces). Lower bound is conceptually simple but Lean-hard (rpow limit lemmas fragmented). The theorem itself (lim ‖f‖_p = ‖f‖_∞) is not in Mathlib."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :final-status
  :summary "Classification: partial. Informal proof complete (both directions + squeeze). Lean skeleton type-checks with 3 sorry. The theorem lim ‖f‖_p = ‖f‖_∞ is genuinely absent from Mathlib. Upper bound closeable from comparison lemma; lower bound needs custom ε-argument."
  :full-record? true
  :sorry? true
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

**Definition.** ‖f‖_∞ = inf{M ≥ 0 : m({x : |f(x)| > M}) = 0}, the essential supremum of |f|. Equivalently, the smallest M such that |f| ≤ M almost everywhere.

**Claim.** For f ∈ L^∞([0,1]), lim_{p→∞} ‖f‖_p = ‖f‖_∞.

**Upper bound: lim sup ‖f‖_p ≤ ‖f‖_∞.**

For a.e. x, |f(x)| ≤ ‖f‖_∞. So ‖f‖_p^p = ∫|f|^p ≤ ‖f‖_∞^p · m([0,1]) = ‖f‖_∞^p. Taking p-th roots: ‖f‖_p ≤ ‖f‖_∞ for all p ≥ 1.

(This is routine — finite measure m([0,1]) = 1 makes it clean.)

**Lower bound: lim inf ‖f‖_p ≥ ‖f‖_∞.**

Fix α < ‖f‖_∞. The set E_α = {x : |f(x)| > α} has m(E_α) > 0 by definition of ess sup. Then ‖f‖_p^p ≥ ∫_{E_α} |f|^p ≥ α^p · m(E_α). Taking p-th roots: ‖f‖_p ≥ α · m(E_α)^{1/p} → α as p → ∞ (since m(E_α)^{1/p} → 1 for m(E_α) > 0).

So lim inf ‖f‖_p ≥ α for every α < ‖f‖_∞, hence lim inf ‖f‖_p ≥ ‖f‖_∞.

(The crux: E_α has POSITIVE measure because α < ess sup, and t^{1/p} → 1 for t > 0.)

**Combine.** ‖f‖_∞ ≤ lim inf ‖f‖_p ≤ lim sup ‖f‖_p ≤ ‖f‖_∞. ∎

**Stage 2 — LEMMA DEPENDENCY GRAPH**

1. **Upper bound** (‖f‖_p ≤ ‖f‖_∞ on finite measure): `eLpNorm_le_eLpNorm_mul_rpow_measure_univ` in Mathlib gives ‖f‖_p ≤ ‖f‖_q · μ(univ)^{1/p-1/q}. With q=⊤ and μ(univ)=1 this gives ‖f‖_p ≤ ‖f‖_∞. **Critical path: YES.**
2. **Level set positive measure**: for α < ‖f‖_∞, μ({‖f‖ > α}) > 0. From the definition of essSup: if μ({‖f‖ > α}) = 0 then α ≥ ‖f‖_∞, contradicting α < ‖f‖_∞. **Custom, straightforward.**
3. **t^{1/p} → 1**: For t > 0, t^{1/p} → 1 as p → ∞. Mathlib: `ENNReal.rpow_natCast` + `tendsto_rpow_nhds_zero_of_norm_lt_one` or similar. **Fragmented in Mathlib.**
4. **Squeeze theorem**: lim inf ≥ L and lim sup ≤ L implies limit = L. Mathlib: `tendsto_of_tendsto_of_tendsto_of_le_of_le`. **Available.**

**Stage 3 — LEAN FORMALIZATION**

The upper bound should close from a single Mathlib comparison lemma. The lower bound needs the level-set argument with t^{1/p} → 1. See Main.lean.

Status: upper bound closeable; lower bound needs ~10 lines of ε-argument.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The upper bound is genuinely easy — both on paper and in Lean. The Mathlib comparison ‖f‖_p ≤ ‖f‖_∞ · μ(univ)^{1/p} is a single lemma, and on [0,1] the factor 1^{1/p} = 1 kills the correction.

The lower bound is the hard direction. On paper: pick α, bound below on E_α, take p-th root, send α → ‖f‖_∞. In Lean: the ε-argument with m(E_α)^{1/p} → 1 needs rpow limit lemmas that are scattered. Conceptual difficulty zero; formalization difficulty moderate.
