import ConstructionTargets.SardLocalizedResidualSliceDerivativeZero
import ConstructionTargets.SardProjectedChartSliceProjectedDerivativeZero
import ConstructionTargets.SardProjectedChartInverseSliceHasFDerivAt

namespace SardProjectedChartLocalizedResidualSliceZeroProbe

variable {E F R G S : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- The indexed residual-slice zero theorem with the rank bound required only
on an explicit locus inside the chart source. -/
theorem forall_hasFDerivAt_zero_residual_inverseSlice_on_locus
    (chart : OpenPartialHomeomorph E (R × G)) (f : E → F) (p : E → R)
    (A U : Set E)
    (hfirst : (fun x => (chart x).1) = p)
    (hsymm : ContDiffOn ℝ 1 chart.symm chart.target)
    (hf : ContDiffOn ℝ 1 f chart.source) (hp : ContDiffOn ℝ 1 p chart.source)
    (L : E →L[ℝ] F) (P : F →L[ℝ] R) (Q : F →L[ℝ] S) (r : ℕ)
    (hbase : Module.finrank ℝ (LinearMap.range L.toLinearMap) = r)
    (hR : Module.finrank ℝ R = Module.finrank ℝ (LinearMap.range L.toLinearMap))
    (hrank : ∀ x ∈ chart.source, x ∈ A ∩ U →
      Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) ≤ r)
    (hcoord : ∀ x ∈ chart.source, fderiv ℝ p x = P.comp (fderiv ℝ f x))
    (hsurj : ∀ x ∈ chart.source, (P.comp (fderiv ℝ f x)).range = ⊤) :
    ∀ c z, (c, z) ∈ chart.target → chart.symm (c, z) ∈ A ∩ U →
      HasFDerivAt (fun w : G => Q (f (chart.symm (c, w)))) (0 : G →L[ℝ] S) z := by
  intro c z hz hlocus
  have hx : chart.symm (c, z) ∈ chart.source := chart.map_target hz
  have hf' : HasFDerivAt f (fderiv ℝ f (chart.symm (c, z))) (chart.symm (c, z)) :=
    (hf.differentiableOn_one.differentiableAt (chart.open_source.mem_nhds hx)).hasFDerivAt
  have hp' : HasFDerivAt p (fderiv ℝ p (chart.symm (c, z))) (chart.symm (c, z)) :=
    (hp.differentiableOn_one.differentiableAt (chart.open_source.mem_nhds hx)).hasFDerivAt
  obtain ⟨J, hJ⟩ :=
    SardProjectedChartInverseSliceHasFDerivAtProbe.exists_hasFDerivAt_inverseSlice_of_contDiffOn_symm
      chart hsymm c z hz
  have hprojected : (fderiv ℝ p (chart.symm (c, z))).comp J = 0 :=
    SardProjectedChartSliceProjectedDerivativeZeroProbe.projected_deriv_comp_sliceDeriv_eq_zero
      chart p hfirst c z hz (fderiv ℝ p (chart.symm (c, z))) J hp' hJ
  rw [hcoord _ hx] at hprojected
  exact SardLocalizedResidualSliceDerivativeZeroProbe.hasFDerivAt_zero_residualSlice_of_localized_rankUpper
    (f := f) (slice := fun w : G => chart.symm (c, w)) (z := z)
    (D := fderiv ℝ f (chart.symm (c, z))) (L := L)
    (P := P) (Q := Q) (J := J) (r := r)
    hbase hR (hrank _ hx hlocus) (hsurj _ hx) hprojected hf' hJ

#print axioms forall_hasFDerivAt_zero_residual_inverseSlice_on_locus

end SardProjectedChartLocalizedResidualSliceZeroProbe
