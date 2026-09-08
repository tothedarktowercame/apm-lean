import ConstructionTargets.SardProjectedChartOrthogonalResidualSliceZero

noncomputable section
namespace SardFiniteOrderProjectedChartOrthogonalResidualSliceZeroProbe

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem forall_hasFDerivAt_zero_orthogonalResidual_inverseSlice_finiteOrder
    (f : E → F) (L : E →L[ℝ] F) (r order : ℕ) (horder : order ≠ 0)
    (chart : OpenPartialHomeomorph E ((LinearMap.range L.toLinearMap) × G))
    (hfirst : (fun x => (chart x).1) =
      fun x => (LinearMap.range L.toLinearMap).orthogonalProjection (f x))
    (hsymm : ContDiffOn ℝ order chart.symm chart.target)
    (hf : ContDiffOn ℝ order f chart.source)
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
  apply SardProjectedChartOrthogonalResidualSliceZeroProbe.forall_hasFDerivAt_zero_orthogonalResidual_inverseSlice
    f L r chart hfirst
    (hsymm.of_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr horder))
    (hf.of_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr horder))
    hbase hrank hsurj

#print axioms forall_hasFDerivAt_zero_orthogonalResidual_inverseSlice_finiteOrder

end SardFiniteOrderProjectedChartOrthogonalResidualSliceZeroProbe
