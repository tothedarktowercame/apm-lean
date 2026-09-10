import ConstructionTargets.PlaneArcEndpointPerturbationFamilyContainment

noncomputable section
open Set

namespace PlaneArcEndpointPerturbationInteriorParameter
open PlaneArcEndpointPreservingPerturbation

abbrev Plane := ℝ × ℝ

lemma endpointWeight_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < endpointWeight t := by
  exact mul_pos ht.1 (sub_pos.mpr ht.2)

lemma endpointWeight_ne_zero {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    endpointWeight t ≠ 0 := (endpointWeight_pos ht).ne'

lemma weight_smul_surjective {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Function.Surjective (fun v : Plane => endpointWeight t • v) := by
  intro y
  refine ⟨(endpointWeight t)⁻¹ • y, ?_⟩
  change endpointWeight t • ((endpointWeight t)⁻¹ • y) = y
  rw [smul_smul, mul_inv_cancel₀ (endpointWeight_ne_zero ht), one_smul]

lemma perturb_parameter_surjective (a : ℝ → Plane) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    Function.Surjective (fun v : Plane => perturb a v t - a t) := by
  simpa only [perturb, add_sub_cancel_left] using weight_smul_surjective ht

#print axioms endpointWeight_pos
#print axioms weight_smul_surjective
#print axioms perturb_parameter_surjective

end PlaneArcEndpointPerturbationInteriorParameter
