import ConstructionTargets.PlaneArcEndpointPairParameterDerivative

noncomputable section
open Set
open scoped ContDiff

namespace PlaneArcEndpointPairParameterRightDerivative
open PlaneArcEndpointPreservingPerturbation
open PlaneArcEndpointPerturbationInteriorParameter
open PlaneArcEndpointPairParameterSurjectivity
open PlaneArcEndpointPairParameterDerivative

abbrev Plane := ℝ × ℝ

def negWeightLinear (s : ℝ) : Plane →L[ℝ] Plane :=
  -(weightLinear s)

theorem hasFDerivAt_pairDifference_right (a b : ℝ → Plane) (va vb : Plane)
    (t s : ℝ) :
    HasFDerivAt (fun w : Plane => pairDifference a b va w t s)
      (negWeightLinear s) vb := by
  unfold pairDifference PlaneArcEndpointPreservingPerturbation.perturb
    negWeightLinear weightLinear
  fun_prop

theorem fderiv_pairDifference_right (a b : ℝ → Plane) (va vb : Plane)
    (t s : ℝ) :
    fderiv ℝ (fun w : Plane => pairDifference a b va w t s) vb =
      negWeightLinear s :=
  (hasFDerivAt_pairDifference_right a b va vb t s).fderiv

theorem fderiv_pairDifference_right_surjective (a b : ℝ → Plane) (va vb : Plane)
    (t : ℝ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    Function.Surjective
      (fderiv ℝ (fun w : Plane => pairDifference a b va w t s) vb) := by
  rw [fderiv_pairDifference_right]
  intro y
  obtain ⟨x, hx⟩ := weight_smul_surjective hs (-y)
  refine ⟨x, ?_⟩
  simpa [negWeightLinear, weightLinear] using congrArg Neg.neg hx

#print axioms hasFDerivAt_pairDifference_right
#print axioms fderiv_pairDifference_right_surjective

end PlaneArcEndpointPairParameterRightDerivative
