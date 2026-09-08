import ConstructionTargets.SardProjectedChartIndexedResidualSliceZero
import ConstructionTargets.SardRangeProjectionCoordinateDerivative

noncomputable section

namespace SardProjectedChartOrthogonalResidualSliceZeroProbe

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Exact base rank, localized rank bounds, and projected surjectivity force
every orthogonal-residual inverse slice derivative to vanish. -/
theorem forall_hasFDerivAt_zero_orthogonalResidual_inverseSlice
    (f : E → F) (L : E →L[ℝ] F) (r : ℕ)
    (chart : OpenPartialHomeomorph E ((LinearMap.range L.toLinearMap) × G))
    (hfirst : (fun x => (chart x).1) =
      fun x => (LinearMap.range L.toLinearMap).orthogonalProjection (f x))
    (hsymm : ContDiffOn ℝ 1 chart.symm chart.target)
    (hf : ContDiffOn ℝ 1 f chart.source)
    (hbase : Module.finrank ℝ (LinearMap.range L.toLinearMap) = r)
    (hrank : ∀ x ∈ chart.source,
      Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) ≤ r)
    (hsurj : ∀ x ∈ chart.source,
      ((LinearMap.range L.toLinearMap).orthogonalProjection.comp
        (fderiv ℝ f x)).range = ⊤) :
    ∀ c z, (c, z) ∈ chart.target →
      HasFDerivAt
        (fun w : G => (LinearMap.range L.toLinearMap)ᗮ.orthogonalProjection
          (f (chart.symm (c, w))))
        (0 : G →L[ℝ] (LinearMap.range L.toLinearMap)ᗮ) z := by
  let R := LinearMap.range L.toLinearMap
  let p : E → R := fun x => R.orthogonalProjection (f x)
  have hp : ContDiffOn ℝ 1 p chart.source :=
    R.orthogonalProjection.contDiff.comp_contDiffOn hf
  have hcoord : ∀ x ∈ chart.source,
      fderiv ℝ p x = R.orthogonalProjection.comp (fderiv ℝ f x) := by
    intro x hx
    have hfx : HasFDerivAt f (fderiv ℝ f x) x :=
      (hf.differentiableOn_one.differentiableAt (chart.open_source.mem_nhds hx)).hasFDerivAt
    exact (SardRangeProjectionCoordinateDerivativeProbe.hasFDerivAt_rangeProjection_comp
      f x (fderiv ℝ f x) L hfx).fderiv
  exact SardProjectedChartIndexedResidualSliceZeroProbe.forall_hasFDerivAt_zero_residual_inverseSlice
    chart f p hfirst hsymm hf hp L R.orthogonalProjection Rᗮ.orthogonalProjection r
    hbase rfl hrank hcoord hsurj

#print axioms forall_hasFDerivAt_zero_orthogonalResidual_inverseSlice

end SardProjectedChartOrthogonalResidualSliceZeroProbe
