import ConstructionTargets.PlaneArcEndpointTotalParameterSubmersive

noncomputable section
open Set
open scoped ContDiff

namespace PlaneArcEndpointTotalDifferenceSubmersive
open PlaneArcEndpointTotalCoincidenceSmooth
open PlaneArcEndpointPairParameterSurjectivity
open PlaneArcEndpointTotalParameterSubmersive

abbrev Plane := ℝ × ℝ

def vectorInclusion : (Plane × Plane) →L[ℝ] TotalParameters :=
  (0 : (Plane × Plane) →L[ℝ] (ℝ × ℝ)).prod
    (ContinuousLinearMap.id ℝ (Plane × Plane))

theorem hasFDerivAt_insertVectors (t s : ℝ) (va vb : Plane) :
    HasFDerivAt (fun q : Plane × Plane => ((t, s), q)) vectorInclusion (va, vb) := by
  convert (hasFDerivAt_const (x := (va, vb)) (c := (t, s))).prodMk
    (ContinuousLinearMap.id ℝ (Plane × Plane)).hasFDerivAt

theorem fullDerivative_comp_vectorInclusion (a b : ℝ → Plane)
    (t s : ℝ) (va vb : Plane)
    (h : DifferentiableAt ℝ (totalDifference a b) ((t, s), (va, vb))) :
    (fderiv ℝ (totalDifference a b) ((t, s), (va, vb))).comp vectorInclusion =
      totalParameterLinear t s := by
  have hc := h.hasFDerivAt.comp (va, vb) (hasFDerivAt_insertVectors t s va vb)
  have hp := hasFDerivAt_pairDifference_parameters a b va vb t s
  exact (hp.unique hc).symm

 theorem fderiv_totalDifference_surjective_of_parameter
    (a b : ℝ → Plane) (t s : ℝ) (va vb : Plane)
    (h : DifferentiableAt ℝ (totalDifference a b) ((t, s), (va, vb)))
    (hsurj : Function.Surjective (totalParameterLinear t s)) :
    Function.Surjective (fderiv ℝ (totalDifference a b) ((t, s), (va, vb))) := by
  intro y
  obtain ⟨q, hq⟩ := hsurj y
  refine ⟨vectorInclusion q, ?_⟩
  have hc := congrArg (fun L : (Plane × Plane) →L[ℝ] Plane => L q)
    (fullDerivative_comp_vectorInclusion a b t s va vb h)
  simpa [hq] using hc

theorem fderiv_totalDifference_surjective_of_left (a b : ℝ → Plane)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (s : ℝ) (va vb : Plane)
    (h : DifferentiableAt ℝ (totalDifference a b) ((t, s), (va, vb))) :
    Function.Surjective (fderiv ℝ (totalDifference a b) ((t, s), (va, vb))) :=
  fderiv_totalDifference_surjective_of_parameter a b t s va vb h
    (by simpa [fderiv_pairDifference_parameters] using
      fderiv_pairDifference_parameters_surjective_of_left a b va vb ht s)

theorem fderiv_totalDifference_surjective_of_right (a b : ℝ → Plane)
    (t : ℝ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (va vb : Plane)
    (h : DifferentiableAt ℝ (totalDifference a b) ((t, s), (va, vb))) :
    Function.Surjective (fderiv ℝ (totalDifference a b) ((t, s), (va, vb))) :=
  fderiv_totalDifference_surjective_of_parameter a b t s va vb h
    (by simpa [fderiv_pairDifference_parameters] using
      fderiv_pairDifference_parameters_surjective_of_right a b va vb t hs)

#print axioms fullDerivative_comp_vectorInclusion
#print axioms fderiv_totalDifference_surjective_of_parameter
#print axioms fderiv_totalDifference_surjective_of_left
#print axioms fderiv_totalDifference_surjective_of_right

end PlaneArcEndpointTotalDifferenceSubmersive
