import ConstructionTargets.PlaneArcEndpointTotalCoincidenceSmooth

noncomputable section
open Set
open scoped ContDiff

namespace PlaneArcEndpointPairParameterDerivative
open PlaneArcEndpointPreservingPerturbation
open PlaneArcEndpointPerturbationInteriorParameter
open PlaneArcEndpointPairParameterSurjectivity

abbrev Plane := ℝ × ℝ

def weightLinear (t : ℝ) : Plane →L[ℝ] Plane :=
  (endpointWeight t) • ContinuousLinearMap.id ℝ Plane

theorem hasFDerivAt_pairDifference_left (a b : ℝ → Plane) (vb va : Plane)
    (t s : ℝ) :
    HasFDerivAt (fun w : Plane => pairDifference a b w vb t s)
      (weightLinear t) va := by
  unfold pairDifference PlaneArcEndpointPreservingPerturbation.perturb weightLinear
  fun_prop

theorem fderiv_pairDifference_left (a b : ℝ → Plane) (vb va : Plane)
    (t s : ℝ) :
    fderiv ℝ (fun w : Plane => pairDifference a b w vb t s) va = weightLinear t :=
  (hasFDerivAt_pairDifference_left a b vb va t s).fderiv

theorem fderiv_pairDifference_left_surjective (a b : ℝ → Plane) (vb va : Plane)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (s : ℝ) :
    Function.Surjective
      (fderiv ℝ (fun w : Plane => pairDifference a b w vb t s) va) := by
  rw [fderiv_pairDifference_left]
  intro y
  obtain ⟨x, hx⟩ := weight_smul_surjective ht y
  exact ⟨x, by simpa [weightLinear] using hx⟩

#print axioms hasFDerivAt_pairDifference_left
#print axioms fderiv_pairDifference_left_surjective

end PlaneArcEndpointPairParameterDerivative
