import ConstructionTargets.SardProjectedSmoothLocalRankChart
import ConstructionTargets.SardRangeProjectionDerivativeSurjectiveOnSmoothChart
import ConstructionTargets.SardTargetOrthogonalCoordinateEquiv

noncomputable section
namespace SardFiniteOrderProjectedSmoothChartTargetDataProbe

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_projected_finiteOrderChart_target_data
    (f : E → F) (x : E) (L : E →L[ℝ] F) (order : ℕ) (horder : order ≠ 0)
    (hf : HasStrictFDerivAt f L x) (hfsmooth : ContDiffAt ℝ order f x) :
    let R := LinearMap.range L.toLinearMap
    let G := (R.orthogonalProjection.comp L).ker
    ∃ chart : OpenPartialHomeomorph E (R × G),
      x ∈ chart.source ∧
      (fun y => (chart y).1) =
        (fun y => (SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates R (f y)).1) ∧
      ContDiffOn ℝ order chart chart.source ∧
      ContDiffOn ℝ order chart.symm chart.target ∧
      ∀ z ∈ chart.source, ∀ D : E →L[ℝ] F, HasFDerivAt f D z →
        (R.orthogonalProjection.comp D).range = ⊤ := by
  dsimp only
  obtain ⟨chart, hx, hformula, hchart, hinv⟩ :=
    SardProjectedSmoothLocalRankChartProbe.exists_projected_smooth_localRankChart
      f x L order (by simp) hf hfsmooth
  refine ⟨chart, hx, ?_, hchart, hinv, ?_⟩
  · funext y
    rw [congrFun hformula y]
    simp only [SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates_apply]
  · intro z hz D hD
    apply SardRangeProjectionDerivativeSurjectiveOnSmoothChartProbe.rangeProjection_comp_range_eq_top_on_smoothChart
      f L D chart (hchart.of_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr horder))
      (hinv.of_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr horder))
      (fun y => ((LinearMap.range L.toLinearMap).orthogonalProjection.comp L).ker.orthogonalProjection y)
      hformula z hz hD

#print axioms exists_projected_finiteOrderChart_target_data

end SardFiniteOrderProjectedSmoothChartTargetDataProbe
