import ConstructionTargets.SardProjectedSmoothLocalRankChart

namespace SardProjectedDerivativeSurjectiveOfRightInverseProbe

variable {E R G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The first block of a product-valued continuous-linear map is surjective
whenever the complete map admits a continuous-linear right inverse. -/
theorem fst_comp_range_eq_top_of_rightInverse
    (D : E →L[ℝ] R × G) (H : (R × G) →L[ℝ] E) (P : E →L[ℝ] R)
    (hP : P = (ContinuousLinearMap.fst ℝ R G).comp D)
    (hright : D.comp H = ContinuousLinearMap.id ℝ (R × G)) :
    P.range = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro r
  refine ⟨H (r, 0), ?_⟩
  rw [hP]
  have h := congrArg (fun T : (R × G) →L[ℝ] (R × G) => T (r, 0)) hright
  exact congrArg Prod.fst h

#print axioms fst_comp_range_eq_top_of_rightInverse

end SardProjectedDerivativeSurjectiveOfRightInverseProbe
