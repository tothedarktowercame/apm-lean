import ConstructionTargets.SardAnnihilatedProjectionNonsurjective

namespace SardProjectedSliceDerivativeNonsurjectiveProbe

variable {G F R : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup R] [NormedSpace ℝ R] [Nontrivial R]

/-- If a surjective projected coordinate of a differentiable map has zero
derivative, then the derivative of the original map is nonsurjective. -/
theorem not_surjective_fderiv_of_projected_hasFDerivAt_zero
    (q : G → F) (z : G) (q' : G →L[ℝ] F) (P : F →L[ℝ] R)
    (hq : HasFDerivAt q q' z)
    (hP : Function.Surjective P)
    (hzero : HasFDerivAt (P ∘ q) (0 : G →L[ℝ] R) z) :
    ¬ Function.Surjective q' := by
  have hcomp : HasFDerivAt (P ∘ q) (P.comp q') z := P.hasFDerivAt.comp z hq
  have hz : P.comp q' = 0 := hcomp.unique hzero
  exact SardAnnihilatedProjectionNonsurjectiveProbe.LinearMap.not_surjective_of_surjective_comp_eq_zero
    q'.toLinearMap P.toLinearMap hP (congrArg ContinuousLinearMap.toLinearMap hz)

#print axioms not_surjective_fderiv_of_projected_hasFDerivAt_zero
end SardProjectedSliceDerivativeNonsurjectiveProbe
