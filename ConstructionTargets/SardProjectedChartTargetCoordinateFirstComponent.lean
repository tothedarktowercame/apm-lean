import ConstructionTargets.SardFirstDerivativeProjectedChartFormula
import ConstructionTargets.SardTargetOrthogonalCoordinateEquiv

noncomputable section

namespace SardProjectedChartTargetCoordinateFirstComponentProbe

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The first coordinate of the projected local-rank chart is exactly the first
orthogonal target coordinate of the mapped point. -/
theorem exists_projectedChart_first_eq_targetCoordinates_first
    (f : E → F) (x : E) (L : E →L[ℝ] F) (hf : HasStrictFDerivAt f L x) :
    let R := LinearMap.range L.toLinearMap
    let G := (R.orthogonalProjection.comp L).ker
    ∃ e : OpenPartialHomeomorph E (R × G),
      x ∈ e.source ∧
      (fun y => (e y).1) =
        fun y => (SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates R (f y)).1 := by
  dsimp only
  obtain ⟨e, hxe, he⟩ :=
    SardFirstDerivativeProjectedImplicitFunctionDataProbe.exists_projected_localRankNormalForm_with_formula
      f x L hf
  refine ⟨e, hxe, ?_⟩
  funext y
  rw [congrFun he y]
  simp only [SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates_apply]

#print axioms exists_projectedChart_first_eq_targetCoordinates_first

end SardProjectedChartTargetCoordinateFirstComponentProbe
