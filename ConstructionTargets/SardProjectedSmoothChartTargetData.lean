import ConstructionTargets.SardProjectedSmoothLocalRankChartSurjectivity
import ConstructionTargets.SardTargetOrthogonalCoordinateEquiv

noncomputable section

namespace SardProjectedSmoothChartTargetDataProbe

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A smooth projected rank chart carries the target-coordinate first-component
identity, two-sided regularity, and pointwise range-coordinate surjectivity. -/
theorem exists_projected_smoothChart_target_data
    (f : E → F) (x : E) (L : E →L[ℝ] F)
    (hf : HasStrictFDerivAt f L x) (hfsmooth : ContDiffAt ℝ 1 f x) :
    let R := LinearMap.range L.toLinearMap
    let G := (R.orthogonalProjection.comp L).ker
    ∃ chart : OpenPartialHomeomorph E (R × G),
      x ∈ chart.source ∧
      (fun y => (chart y).1) =
        (fun y => (SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates R (f y)).1) ∧
      ContDiffOn ℝ 1 chart chart.source ∧
      ContDiffOn ℝ 1 chart.symm chart.target ∧
      ∀ z ∈ chart.source, ∀ D : E →L[ℝ] F, HasFDerivAt f D z →
        (R.orthogonalProjection.comp D).range = ⊤ := by
  dsimp only
  obtain ⟨chart, hx, hformula, hchart, hinv, hsurj⟩ :=
    SardProjectedSmoothLocalRankChartSurjectivityProbe.exists_projected_smooth_localRankChart_with_surjective_rangeDerivative
        f x L hf hfsmooth
  refine ⟨chart, hx, ?_, hchart, hinv, hsurj⟩
  funext y
  rw [congrFun hformula y]
  simp only [SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates_apply]

#print axioms exists_projected_smoothChart_target_data

end SardProjectedSmoothChartTargetDataProbe
