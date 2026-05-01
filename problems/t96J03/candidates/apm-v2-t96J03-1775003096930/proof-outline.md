# Proof Outline: t96J03

This file packages the formalization-oriented context that should travel
with the Lean files.

## Notes

The content below was imported automatically and may need cleanup.

## Imported Proof Plan

```clojure
{:goal
 "Show nonempty closed X ⊂ ℝⁿ has a closest point to any y₀: ∃ x₀ ∈ X, ‖x₀-y₀‖ ≤ ‖x-y₀‖ ∀ x ∈ X."
 :terms
 [{:name "closed set"
   :meaning "X closed in ℝⁿ"
   :needed-because "closedness + bounded = compact (Heine-Borel) ensures minimizer exists"}
  {:name "infDist"
   :meaning "inf{dist(y₀, x) : x ∈ X}"
   :needed-because "the infimum that must be attained"}
  {:name "proper space"
   :meaning "closed bounded = compact"
   :needed-because "ℝⁿ is proper, making IsClosed.exists_infDist_eq_dist apply"}]
 :strategy
 [{:id :mathlib-closest-point
   :formal-dependency "IsClosed.exists_infDist_eq_dist + infDist_le_dist_of_mem"
   :informal-dependency "closest point theorem for proper metric spaces"
   :why-this-now "two-line Mathlib proof"
   :lean-target "∃ x₀ ∈ X, ∀ x ∈ X, dist y₀ x₀ ≤ dist y₀ x"
   :mathlib-status "available and CLOSED"
   :critical-path true}]
 :stage-status
 {:stage1 :done
  :stage2 :done
  :stage3 :done
  :stage4 :done}}
```

## Imported Changelog

```clojure
[{:kind :workspace-initialized
  :problem-id "t96J03"
  :frame-id "apm-v2-t96J03-1775003096930"
  :summary "Created isolated proof frame workspace."
  :full-record? false
  :sorry? false
  :fully-closed? false}
 {:kind :target-check
  :summary "Identified Mathlib has IsClosed.exists_infDist_eq_dist for ProperSpace. EuclideanSpace ℝ (Fin n) is ProperSpace. Sanity check passed."
  :full-record? true
  :sorry? false
  :fully-closed? false}
 {:kind :lean-delta
  :summary "FULLY CLOSED — zero sorry. Two-line proof: obtain closest point from Mathlib, rewrite infDist = dist, apply infDist_le_dist_of_mem. Builds clean."
  :full-record? true
  :sorry? false
  :fully-closed? true}
 {:kind :final-status
  :summary "Classification: PROVED. Zero sorry. The closest point theorem is a two-line Mathlib application. Third fully-closed problem in the batch (after a02J04 and b94J01)."
  :full-record? true
  :sorry? false
  :fully-closed? true}]
```

## Imported Execution Notes

**Stage 1 — THE CLEAN PROOF**

**Claim.** Let X ⊂ ℝⁿ be nonempty and closed, and let y₀ ∈ ℝⁿ \ X. Then there exists x₀ ∈ X with ‖x₀ - y₀‖ ≤ ‖x - y₀‖ for all x ∈ X.

**Proof.** Let d = inf{‖x - y₀‖ : x ∈ X}. Since X is nonempty, d is finite and d ≥ 0. Choose a sequence {xₖ} ⊂ X with ‖xₖ - y₀‖ → d.

All xₖ lie in the closed ball B̄(y₀, ‖x₁ - y₀‖), which is a closed bounded (hence compact) subset of ℝⁿ. By Bolzano-Weierstrass, {xₖ} has a convergent subsequence xₖⱼ → x₀. Since X is closed, x₀ ∈ X. By continuity of the norm: ‖x₀ - y₀‖ = lim ‖xₖⱼ - y₀‖ = d ≤ ‖x - y₀‖ for all x ∈ X. ∎

(The key is compactness: closed + bounded = compact in ℝⁿ (Heine-Borel). This fails in infinite-dimensional spaces — the closest point theorem for closed convex sets in Hilbert space requires convexity, not just closedness.)

**Stage 2 — LEMMA DEPENDENCY GRAPH**

| # | Lemma | Source | Critical? |
|---|-------|--------|-----------|
| 1 | ℝⁿ is a proper metric space | Mathlib: `EuclideanSpace.instProperSpace` | YES |
| 2 | Closest point in closed set of proper space | Mathlib: `IsClosed.exists_infDist_eq_dist` | YES |
| 3 | infDist is a lower bound | Mathlib: `infDist_le_dist_of_mem` | YES |

**Stage 3 — LEAN FORMALIZATION**

**FULLY CLOSED — ZERO SORRY.**

```lean
theorem closest_point_exists ... :
    ∃ x₀ ∈ X, ∀ x ∈ X, dist y₀ x₀ ≤ dist y₀ x := by
  obtain ⟨x₀, hx₀_mem, hx₀_dist⟩ := hX.exists_infDist_eq_dist hne y₀
  exact ⟨x₀, hx₀_mem, fun x hx => hx₀_dist ▸ infDist_le_dist_of_mem hx⟩
```

Two lines: destructure Mathlib's closest point, then rewrite infDist = dist and apply the lower bound.

**Stage 4 — FORMAL-TO-INFORMAL REVISION**

The Lean proof is genuinely two lines — confirming this is a pure library lookup in Mathlib. The underlying Mathlib proof does exactly the informal argument: intersect X with a closed ball (making it compact), find the minimum on the compact set, and use closedness to ensure the minimizer is in X.

The only subtlety for a student: knowing that ℝⁿ is a "proper metric space" (closed bounded = compact). This is Heine-Borel, which Mathlib encodes as the `ProperSpace` typeclass. In infinite dimensions, this fails — the unit ball in ℓ² is closed bounded but NOT compact, so the closest point theorem needs additional hypotheses (convexity).
