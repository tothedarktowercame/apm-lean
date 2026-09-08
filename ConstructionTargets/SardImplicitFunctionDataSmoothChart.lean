import ConstructionTargets.SardOpenPartialHomeomorphSmoothRefinement
import Mathlib.Analysis.Calculus.Implicit

namespace SardImplicitFunctionDataSmoothChartProbe

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Smoothness of both defining fields upgrades an implicit-function chart to
a base-point-preserving chart restriction smooth in both directions. -/
theorem exists_smooth_chart_restriction
    (φ : ImplicitFunctionData ℝ E F G) (n : WithTop ℕ∞)
    (hn : n ≠ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    (hleft : ContDiffAt ℝ n φ.leftFun φ.pt)
    (hright : ContDiffAt ℝ n φ.rightFun φ.pt) :
    ∃ e : OpenPartialHomeomorph E (F × G),
      φ.pt ∈ e.source ∧ (e : E → F × G) = φ.prodFun ∧
      ContDiffOn ℝ n e e.source ∧ ContDiffOn ℝ n e.symm e.target := by
  let D : E ≃L[ℝ] F × G :=
    φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv
      φ.range_leftDeriv φ.range_rightDeriv φ.isCompl_ker
  have hD : HasFDerivAt φ.toOpenPartialHomeomorph (D : E →L[ℝ] F × G) φ.pt := by
    simpa [D, ImplicitFunctionData.toOpenPartialHomeomorph_coe] using
      φ.hasStrictFDerivAt.hasFDerivAt
  have hsmooth : ContDiffAt ℝ n φ.toOpenPartialHomeomorph φ.pt := by
    simpa [ImplicitFunctionData.toOpenPartialHomeomorph_coe,
      ImplicitFunctionData.prodFun] using hleft.prodMk hright
  exact SardOpenPartialHomeomorphSmoothRefinementProbe.exists_smooth_restriction_at
    φ.toOpenPartialHomeomorph n hn φ.pt φ.pt_mem_toOpenPartialHomeomorph_source D hD hsmooth

#print axioms exists_smooth_chart_restriction

end SardImplicitFunctionDataSmoothChartProbe
