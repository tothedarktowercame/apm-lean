import ConstructionTargets.PlaneArcEndpointPairParameterRightDerivative

noncomputable section
open Set
open scoped ContDiff

namespace PlaneArcEndpointTotalParameterSubmersive
open PlaneArcEndpointPreservingPerturbation
open PlaneArcEndpointPerturbationInteriorParameter
open PlaneArcEndpointPairParameterSurjectivity
open PlaneArcEndpointPairParameterDerivative
open PlaneArcEndpointPairParameterRightDerivative

abbrev Plane := ℝ × ℝ

def totalParameterLinear (t s : ℝ) : (Plane × Plane) →L[ℝ] Plane :=
  (weightLinear t).comp (ContinuousLinearMap.fst ℝ Plane Plane) +
    (negWeightLinear s).comp (ContinuousLinearMap.snd ℝ Plane Plane)

theorem hasFDerivAt_pairDifference_parameters (a b : ℝ → Plane)
    (va vb : Plane) (t s : ℝ) :
    HasFDerivAt (fun p : Plane × Plane => pairDifference a b p.1 p.2 t s)
      (totalParameterLinear t s) (va, vb) := by
  have hl : HasFDerivAt (fun p : Plane × Plane => endpointWeight t • p.1)
      ((weightLinear t).comp (ContinuousLinearMap.fst ℝ Plane Plane)) (va, vb) := by
    change HasFDerivAt (fun p : Plane × Plane => weightLinear t p.1)
      ((weightLinear t).comp (ContinuousLinearMap.fst ℝ Plane Plane)) (va, vb)
    exact (weightLinear t).hasFDerivAt.comp (va, vb) hasFDerivAt_fst
  have hr : HasFDerivAt (fun p : Plane × Plane => endpointWeight s • p.2)
      ((weightLinear s).comp (ContinuousLinearMap.snd ℝ Plane Plane)) (va, vb) := by
    change HasFDerivAt (fun p : Plane × Plane => weightLinear s p.2)
      ((weightLinear s).comp (ContinuousLinearMap.snd ℝ Plane Plane)) (va, vb)
    exact (weightLinear s).hasFDerivAt.comp (va, vb) hasFDerivAt_snd
  convert (hl.const_add (a t)).sub (hr.const_add (b s)) using 1

theorem fderiv_pairDifference_parameters (a b : ℝ → Plane)
    (va vb : Plane) (t s : ℝ) :
    fderiv ℝ (fun p : Plane × Plane => pairDifference a b p.1 p.2 t s) (va, vb) =
      totalParameterLinear t s :=
  (hasFDerivAt_pairDifference_parameters a b va vb t s).fderiv

theorem fderiv_pairDifference_parameters_surjective_of_left
    (a b : ℝ → Plane) (va vb : Plane) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (s : ℝ) :
    Function.Surjective
      (fderiv ℝ (fun p : Plane × Plane => pairDifference a b p.1 p.2 t s) (va, vb)) := by
  rw [fderiv_pairDifference_parameters]
  intro y
  obtain ⟨x, hx⟩ := weight_smul_surjective ht y
  exact ⟨(x, 0), by simpa [totalParameterLinear, weightLinear, negWeightLinear] using hx⟩

theorem fderiv_pairDifference_parameters_surjective_of_right
    (a b : ℝ → Plane) (va vb : Plane) (t : ℝ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    Function.Surjective
      (fderiv ℝ (fun p : Plane × Plane => pairDifference a b p.1 p.2 t s) (va, vb)) := by
  rw [fderiv_pairDifference_parameters]
  intro y
  obtain ⟨x, hx⟩ := weight_smul_surjective hs (-y)
  refine ⟨(0, x), ?_⟩
  simpa [totalParameterLinear, weightLinear, negWeightLinear] using congrArg Neg.neg hx

#print axioms hasFDerivAt_pairDifference_parameters
#print axioms fderiv_pairDifference_parameters_surjective_of_left
#print axioms fderiv_pairDifference_parameters_surjective_of_right

end PlaneArcEndpointTotalParameterSubmersive
