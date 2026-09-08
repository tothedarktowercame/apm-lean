import ConstructionTargets.SardProjectedChartResidualSliceDerivativeZero

namespace SardResidualDerivativeCompositionEqZeroProbe

variable {E F G S : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Pointwise annihilation of every slice direction is exactly the zero
continuous-linear composition needed by the residual slice chain rule. -/
theorem residual_comp_deriv_comp_eq_zero
    (Q : F →L[ℝ] S) (D : E →L[ℝ] F) (J : G →L[ℝ] E)
    (hzero : ∀ v, Q (D (J v)) = 0) :
    Q.comp (D.comp J) = 0 := by
  ext v
  exact hzero v

#print axioms residual_comp_deriv_comp_eq_zero

end SardResidualDerivativeCompositionEqZeroProbe
