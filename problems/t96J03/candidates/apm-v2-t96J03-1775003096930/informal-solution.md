# Informal Solution: t96J03

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

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
