import Mathlib

noncomputable section

namespace ApmCanaries.Frames.T96J03.Apm_v2_t96J03_1775003096930.Main

open Metric Set

/-! # APM t96J03: Closest point in a closed subset of ℝⁿ

  X ⊂ ℝⁿ nonempty closed, y₀ ∉ X. Show ∃ x₀ ∈ X, ‖x₀-y₀‖ ≤ ‖x-y₀‖ ∀ x ∈ X.

  Mathlib: IsClosed.exists_infDist_eq_dist [ProperSpace] gives
  ∃ x₀ ∈ X, infDist y₀ X = dist y₀ x₀.
  Since infDist y₀ X ≤ dist y₀ x for all x ∈ X, we get dist y₀ x₀ ≤ dist y₀ x.
-/

-- CLOSED: The closest point theorem for ℝⁿ
-- EuclideanSpace ℝ (Fin n) is a ProperSpace (Mathlib instance).
theorem closest_point_exists {n : ℕ}
    {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : IsClosed X) (hne : X.Nonempty)
    (y₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ x₀ ∈ X, ∀ x ∈ X, dist y₀ x₀ ≤ dist y₀ x := by
  -- Step 1: Mathlib gives a closest point
  obtain ⟨x₀, hx₀_mem, hx₀_dist⟩ := hX.exists_infDist_eq_dist hne y₀
  -- hx₀_dist : infDist y₀ X = dist y₀ x₀
  -- Step 2: infDist is a lower bound
  exact ⟨x₀, hx₀_mem, fun x hx => hx₀_dist ▸ infDist_le_dist_of_mem hx⟩

end ApmCanaries.Frames.T96J03.Apm_v2_t96J03_1775003096930.Main
