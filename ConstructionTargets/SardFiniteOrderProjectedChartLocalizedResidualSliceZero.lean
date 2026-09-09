import ConstructionTargets.SardProjectedChartLocalizedResidualSliceZero

namespace SardFiniteOrderProjectedChartLocalizedResidualSliceZeroProbe

variable {E F R G S : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

theorem forall_hasFDerivAt_zero_residual_inverseSlice_on_locus_finiteOrder
    (order : ℕ) (horder : order ≠ 0)
    (chart : OpenPartialHomeomorph E (R × G)) (f : E → F) (p : E → R)
    (A U : Set E) (hfirst : (fun x => (chart x).1) = p)
    (hsymm : ContDiffOn ℝ order chart.symm chart.target)
    (hf : ContDiffOn ℝ order f chart.source) (hp : ContDiffOn ℝ order p chart.source)
    (L : E →L[ℝ] F) (P : F →L[ℝ] R) (Q : F →L[ℝ] S) (r : ℕ)
    (hbase : Module.finrank ℝ (LinearMap.range L.toLinearMap) = r)
    (hR : Module.finrank ℝ R = Module.finrank ℝ (LinearMap.range L.toLinearMap))
    (hrank : ∀ x ∈ chart.source, x ∈ A ∩ U →
      Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) ≤ r)
    (hcoord : ∀ x ∈ chart.source, fderiv ℝ p x = P.comp (fderiv ℝ f x))
    (hsurj : ∀ x ∈ chart.source, (P.comp (fderiv ℝ f x)).range = ⊤) :
    ∀ c z, (c, z) ∈ chart.target → chart.symm (c, z) ∈ A ∩ U →
      HasFDerivAt (fun w : G => Q (f (chart.symm (c, w)))) (0 : G →L[ℝ] S) z := by
  apply SardProjectedChartLocalizedResidualSliceZeroProbe.forall_hasFDerivAt_zero_residual_inverseSlice_on_locus
    chart f p A U hfirst (hsymm.of_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr horder))
      (hf.of_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr horder))
      (hp.of_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr horder))
      L P Q r hbase hR hrank hcoord hsurj

#print axioms forall_hasFDerivAt_zero_residual_inverseSlice_on_locus_finiteOrder

end SardFiniteOrderProjectedChartLocalizedResidualSliceZeroProbe
