import Mathlib

/-!
# APM t96J03 — a closed Euclidean set has a nearest point
-/

theorem apm_t96j03
    (n : ℕ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX_closed : IsClosed X) (hX_nonempty : X.Nonempty)
    (y₀ : EuclideanSpace ℝ (Fin n)) (hy₀ : y₀ ∉ X) :
    ∃ x₀ ∈ X, ∀ x ∈ X, ‖x₀ - y₀‖ ≤ ‖x - y₀‖ := by
  obtain ⟨x₀, hx₀, h⟩ := hX_closed.exists_infDist_eq_dist hX_nonempty y₀
  refine ⟨x₀, hx₀, fun x hx => ?_⟩
  rw [← dist_eq_norm, ← dist_eq_norm, dist_comm x₀, dist_comm x, ← h]
  exact Metric.infDist_le_dist_of_mem hx
