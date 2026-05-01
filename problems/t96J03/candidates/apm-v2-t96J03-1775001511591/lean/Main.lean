import Mathlib
import ApmCanaries.Frames.T96J03.Apm_v2_t96J03_1775001511591.Scratch

noncomputable section

namespace ApmCanaries.Frames.T96J03.Apm_v2_t96J03_1775001511591.Main

/- Authoritative frame-local Lean development.
   Keep exploratory detours in Scratch.lean.
   Promote reusable lemmas explicitly into ApmCanaries.Local. -/

/-- A closed subset of Euclidean space contains a point closest to any exterior point. -/
theorem closest_point_exists {n : ℕ}
    {X : Set (EuclideanSpace ℝ (Fin n))} (hX : IsClosed X) (hne : X.Nonempty)
    {y₀ : EuclideanSpace ℝ (Fin n)} (hy₀ : y₀ ∉ X) :
    ∃ x₀ ∈ X, ∀ ⦃x⦄, x ∈ X → ‖x - y₀‖ ≥ ‖x₀ - y₀‖ := by
  classical
  have _ := (hX.notMem_iff_infDist_pos hne).mp hy₀
  obtain ⟨x₀, hx₀X, hx₀dist⟩ := hX.exists_infDist_eq_dist hne y₀
  refine ⟨x₀, hx₀X, ?_⟩
  intro x hxX
  have hx₀_le : ‖y₀ - x₀‖ ≤ ‖y₀ - x‖ := by
    have := infDist_le_dist_of_mem hxX
    simpa [hx₀dist, dist_eq_norm] using this
  simpa [norm_sub_rev] using hx₀_le

end ApmCanaries.Frames.T96J03.Apm_v2_t96J03_1775001511591.Main
