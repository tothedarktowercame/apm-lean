import ConstructionTargets.SardLocalizedRankUpperBound
import ConstructionTargets.SardRankUpperResidualSliceAnnihilation

namespace SardLocalizedProjectedSliceAnnihilationProbe

variable {E F R G S : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Projected surjectivity and a localized rank-at-most-index hypothesis force
every residual coordinate to annihilate the projected slice derivative. -/
theorem residual_comp_slice_eq_zero_of_localized_rankUpper
    (D L : E →L[ℝ] F) (P : F →L[ℝ] R) (Q : F →L[ℝ] S)
    (J : G →L[ℝ] E) (r : ℕ)
    (hbase : Module.finrank ℝ (LinearMap.range L.toLinearMap) = r)
    (hR : Module.finrank ℝ R = Module.finrank ℝ (LinearMap.range L.toLinearMap))
    (hrank : Module.finrank ℝ (LinearMap.range D.toLinearMap) ≤ r)
    (hsurj : (P.comp D).range = ⊤)
    (hprojected : P.comp (D.comp J) = 0) :
    Q.comp (D.comp J) = 0 := by
  have hrank' : Module.finrank ℝ (LinearMap.range D.toLinearMap) ≤
      Module.finrank ℝ (LinearMap.range L.toLinearMap) :=
    SardLocalizedRankUpperBoundProbe.finrank_range_le_baseRange_of_le_rankIndex
      D.toLinearMap L.toLinearMap r hbase hrank
  have hrankR : Module.finrank ℝ (LinearMap.range D.toLinearMap) ≤ Module.finrank ℝ R :=
    hrank'.trans_eq hR.symm
  ext v
  exact SardRankUpperResidualSliceAnnihilationProbe.residual_annihilates_slice_of_rankUpper
    D.toLinearMap P.toLinearMap Q.toLinearMap J.toLinearMap hsurj hrankR
      (congrArg ContinuousLinearMap.toLinearMap hprojected) v

#print axioms residual_comp_slice_eq_zero_of_localized_rankUpper

end SardLocalizedProjectedSliceAnnihilationProbe
