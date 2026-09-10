import ConstructionTargets.PlaneArcEndpointPreservingPerturbation

noncomputable section
open Set

namespace PlaneArcEndpointPerturbationContainment
open PlaneArcEndpointPreservingPerturbation

lemma abs_endpointWeight_le_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |endpointWeight t| ≤ 1 := by
  rw [endpointWeight, abs_mul, abs_of_nonneg ht.1, abs_of_nonneg (sub_nonneg.mpr ht.2)]
  exact (mul_le_of_le_one_right ht.1 (sub_le_self 1 ht.1)).trans ht.2

lemma dist_perturb_le_norm (a : ℝ → Plane) (v : Plane) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (perturb a v t) (a t) ≤ ‖v‖ := by
  rw [dist_eq_norm]
  simp only [perturb, add_sub_cancel_left, norm_smul]
  simpa only [Real.norm_eq_abs, one_mul] using
    mul_le_of_le_one_left (norm_nonneg v) (abs_endpointWeight_le_one ht)

theorem perturb_mem_thickening (a : ℝ → Plane) (v : Plane) (K : Set Plane)
    {e : ℝ} (he : ‖v‖ < e) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (ha : a t ∈ K) :
    perturb a v t ∈ Metric.thickening e K := by
  rw [Metric.mem_thickening_iff]
  exact ⟨a t, ha, (dist_perturb_le_norm a v ht).trans_lt he⟩

#print axioms abs_endpointWeight_le_one
#print axioms dist_perturb_le_norm
#print axioms perturb_mem_thickening

end PlaneArcEndpointPerturbationContainment
