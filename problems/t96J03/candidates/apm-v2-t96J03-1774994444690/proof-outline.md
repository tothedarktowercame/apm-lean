# Proof Outline: t96J03

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:problem-id 't96J03
 :frame-id 'apm-v2-t96J03-1774994444690
 :goal "Given a non-empty closed subset of ℝⁿ and an exterior point, produce a point in the set with minimal Euclidean distance to the exterior point."
 :terms [{:name "proper metric space"
          :meaning "every closed ball is compact"
          :needed-because "ensures the distance function attains its infimum on closed sets"}
         {:name "infDist"
          :meaning "Mathlib’s infimum of distances from a point to a set"
          :needed-because "`IsClosed.exists_infDist_eq_dist` supplies the minimizing point"}
         {:name "le_infDist"
          :meaning "characterizes when a real number lies below the infimum distance"
          :needed-because "converts the inf-distance equality into pointwise inequalities"}]
 :strategy [{:id :s1
             :formal-dependency "Heine–Borel / properness of Euclidean space"
             :informal-dependency "Stage 1 compactness argument"
             :why-this-now "Shows the distance function achieves a minimum"
             :lean-target "Metric.isClosed.exists_infDist_eq_dist"
             :mathlib-status "Available"}
            {:id :s2
             :formal-dependency "le_infDist"
             :informal-dependency "Conclude scope-wide inequality"
             :why-this-now "Turns the inf-distance equality into the comparison needed for all x ∈ X"
             :lean-target "Metric.le_infDist"
             :mathlib-status "Available"}]
 :stage-status {:stage1 :done :stage2 :done :stage3 :in-progress :stage4 :pending}
 :lean {:module-root 'ApmCanaries.Frames.T96J03.Apm_v2_t96J03_1774994444690
        :shared-extension-root "ApmCanaries.Local"}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :summary "Initialized frame and pointed execute/proof-plan/formal-alignment placeholders."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage1-completed
  :summary "Wrote the compactness-based nearest-point argument in execute.md."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage2-completed
  :summary "Documented dependency graph and Lean targets in execute.md and proof-plan.edn."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :stage3-completed
  :summary "Formalized `closest_point_exists` in Lean and aligned all artifacts."
  :full-record? true
  :sorry? false
  :fully-closed? false}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

Let `X ⊆ ℝⁿ` be non-empty and closed and take `y₀ ∉ X`. Consider the continuous function `f(x) = ‖x − y₀‖` on `X`. Because `X` might be unbounded, first pick any `x₁ ∈ X` and let `R = ‖x₁ − y₀‖`. Every point that minimizes `f` must lie in the closed ball `B = {x : ‖x − y₀‖ ≤ R}` since `x₁` already has distance `R`. The set `X ∩ B` is closed and bounded, hence compact by Heine–Borel, and `f` is continuous. The extreme value theorem now produces `x₀ ∈ X ∩ B` with `f(x₀) ≤ f(x)` for all `x ∈ X ∩ B`, hence for every `x ∈ X`. Thus the closest point exists. Equivalently, one can argue via infima: the non-empty closed set `X` equals its closure and in a proper metric space every closed set realizes the infimum of the distance function `x ↦ dist(x,X)`. Applying this with `x = y₀` gives the desired minimizer.

**Stage 2 — LEMMA DEPENDENCY GRAPH**

- **Properness of ℝⁿ.** Closed balls are compact so the intersection `X ∩ B` is compact. Needed to invoke extreme value theorem.
- **Continuity of distance.** The map `x ↦ ‖x − y₀‖` is continuous; used to apply the extreme value theorem.
- **Extreme value theorem / inf-distance lemma.** On a compact set a continuous function attains its minimum; in Lean we use the more general `IsClosed.exists_infDist_eq_dist` in proper metric spaces.

**Stage 3 — LEAN FORMALIZATION**

`Main.lean` proves the lemma
```
lemma closest_point_exists
  {X : Set (EuclideanSpace ℝ (Fin n))}
  (hX : IsClosed X) (hne : X.Nonempty) (y₀ : EuclideanSpace ℝ (Fin n))
  (hy₀ : y₀ ∉ X) :
  ∃ x ∈ X, ∀ z ∈ X, dist x y₀ ≤ dist z y₀.
```
We apply the Mathlib theorem `IsClosed.exists_infDist_eq_dist` (valid in every proper metric space) to obtain `x ∈ X` with `dist y₀ x = infDist y₀ X`. Then the characterization `le_infDist` translates this equality into the desired comparison with every other `z ∈ X`. No extra helper lemmas were required beyond Mathlib’s `infDist` API.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

Stage 1 already mirrors the Lean proof: both rely on the “distance-to-a-closed-set attains its infimum” principle. The Lean statement makes the proper-space requirement explicit by working in `EuclideanSpace`. Any future edits should simply cite `closest_point_exists` in Stage 1 and note that the general inf-distance lemma handles the minimization more directly than the compactness argument.
