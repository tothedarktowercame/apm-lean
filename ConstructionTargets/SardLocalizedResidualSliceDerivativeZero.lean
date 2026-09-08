import ConstructionTargets.SardLocalizedProjectedSliceAnnihilation
import ConstructionTargets.SardProjectedChartResidualSliceDerivativeZero

namespace SardLocalizedResidualSliceDerivativeZeroProbe

variable {E F R G S : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Localized projected rank data promote residual slice annihilation to the
zero Frechet derivative certificate required by fiberwise Sard induction. -/
theorem hasFDerivAt_zero_residualSlice_of_localized_rankUpper
    (f : E → F) (slice : G → E) (z : G)
    (D L : E →L[ℝ] F) (P : F →L[ℝ] R) (Q : F →L[ℝ] S)
    (J : G →L[ℝ] E) (r : ℕ)
    (hbase : Module.finrank ℝ (LinearMap.range L.toLinearMap) = r)
    (hR : Module.finrank ℝ R = Module.finrank ℝ (LinearMap.range L.toLinearMap))
    (hrank : Module.finrank ℝ (LinearMap.range D.toLinearMap) ≤ r)
    (hsurj : (P.comp D).range = ⊤)
    (hprojected : P.comp (D.comp J) = 0)
    (hf : HasFDerivAt f D (slice z)) (hslice : HasFDerivAt slice J z) :
    HasFDerivAt (fun w => Q (f (slice w))) (0 : G →L[ℝ] S) z := by
  apply SardProjectedChartResidualSliceDerivativeZeroProbe.hasFDerivAt_zero_residual_comp_slice
    f slice Q z D J hf hslice
  exact SardLocalizedProjectedSliceAnnihilationProbe.residual_comp_slice_eq_zero_of_localized_rankUpper
    D L P Q J r hbase hR hrank hsurj hprojected

#print axioms hasFDerivAt_zero_residualSlice_of_localized_rankUpper

end SardLocalizedResidualSliceDerivativeZeroProbe
