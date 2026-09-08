import ConstructionTargets.SardProjectedSmoothLocalRankChart
import ConstructionTargets.SardRangeProjectionDerivativeSurjectiveOnSmoothChart

noncomputable section
namespace SardProjectedSmoothLocalRankChartSurjectivityProbe

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The smooth projected local-rank chart may be chosen so that its
derivative-range coordinate derivative is surjective at every source point. -/
theorem exists_projected_smooth_localRankChart_with_surjective_rangeDerivative
    (f : E → F) (x : E) (L : E →L[ℝ] F)
    (hf : HasStrictFDerivAt f L x) (hfsmooth : ContDiffAt ℝ 1 f x) :
    let R := LinearMap.range L.toLinearMap
    let G := (R.orthogonalProjection.comp L).ker
    ∃ chart : OpenPartialHomeomorph E (R × G),
      x ∈ chart.source ∧
      (chart : E → R × G) =
        (fun y => (R.orthogonalProjection (f y), G.orthogonalProjection y)) ∧
      ContDiffOn ℝ 1 chart chart.source ∧
      ContDiffOn ℝ 1 chart.symm chart.target ∧
      ∀ z ∈ chart.source, ∀ D : E →L[ℝ] F, HasFDerivAt f D z →
        (R.orthogonalProjection.comp D).range = ⊤ := by
  dsimp only
  obtain ⟨chart, hx, hformula, hchart, hinv⟩ :=
    SardProjectedSmoothLocalRankChartProbe.exists_projected_smooth_localRankChart
      f x L 1 (by simp) hf hfsmooth
  refine ⟨chart, hx, hformula, hchart, hinv, ?_⟩
  intro z hz D hD
  exact SardRangeProjectionDerivativeSurjectiveOnSmoothChartProbe.rangeProjection_comp_range_eq_top_on_smoothChart
      f L D chart hchart hinv
      (fun y => ((LinearMap.range L.toLinearMap).orthogonalProjection.comp L).ker.orthogonalProjection y)
      hformula z hz hD

#print axioms exists_projected_smooth_localRankChart_with_surjective_rangeDerivative

end SardProjectedSmoothLocalRankChartSurjectivityProbe
