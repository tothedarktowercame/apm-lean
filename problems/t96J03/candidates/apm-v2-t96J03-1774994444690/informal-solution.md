# Informal Solution: t96J03

This file is the best available worked mathematical solution imported
from the historical proof-frame workspace.

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
