import Mathlib
import ApmCanaries.Frames.T96J03.Apm_v2_t96J03_1774999579956.Scratch

noncomputable section

namespace ApmCanaries.Frames.T96J03.Apm_v2_t96J03_1774999579956.Main

open Metric

variable {n : ℕ}

/-- A nonempty closed subset of `ℝⁿ` contains a point closest to any exterior point. -/
lemma exists_closest_point_closed_subset
    {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : IsClosed X) (hne : X.Nonempty)
    {y₀ : EuclideanSpace ℝ (Fin n)} (hy₀ : y₀ ∉ X) :
    ∃ x ∈ X, ∀ z ∈ X, dist x y₀ ≤ dist z y₀ := by
  classical
  obtain ⟨x, hxX, hx⟩ := hX.exists_infDist_eq_dist hne y₀
  refine ⟨x, hxX, ?_⟩
  intro z hzX
  have hineq : dist y₀ x ≤ infDist y₀ X := by simpa [hx]
  have hcomp := (le_infDist hne).1 hineq z hzX
  simpa [dist_comm] using hcomp

end ApmCanaries.Frames.T96J03.Apm_v2_t96J03_1774999579956.Main
