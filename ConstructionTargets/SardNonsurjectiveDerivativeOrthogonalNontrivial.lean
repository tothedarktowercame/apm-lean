import ConstructionTargets.SardDerivativeRangeOrthogonalNontrivial

namespace SardNonsurjectiveDerivativeOrthogonalNontrivialProbe

/-- A nonsurjective derivative has a nontrivial orthogonal residual coordinate. -/
theorem nontrivial_range_orthogonal_of_not_surjective
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E →L[ℝ] F) (hL : ¬ Function.Surjective L) :
    Nontrivial (LinearMap.range L.toLinearMap)ᗮ := by
  apply SardDerivativeRangeOrthogonalNontrivialProbe.nontrivial_orthogonal_of_ne_top
  intro htop
  exact hL (LinearMap.range_eq_top.mp htop)

#print axioms nontrivial_range_orthogonal_of_not_surjective

end SardNonsurjectiveDerivativeOrthogonalNontrivialProbe
