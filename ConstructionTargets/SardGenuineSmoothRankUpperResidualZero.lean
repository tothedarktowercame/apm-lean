import ConstructionTargets.SardGenuineSmoothProjectedRankChart
import ConstructionTargets.SardSmoothProjectedChartFirstDerivativeSurjective
import ConstructionTargets.SardProjectedChartSliceProjectedDerivativeZero
import ConstructionTargets.SardProjectedChartResidualSliceDerivativeZero

open scoped ContDiff
noncomputable section
namespace SardGenuineSmoothRankUpperResidualZeroProbe
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem exists_rank_upper_residual_zero
    (f : E → F) (x : E) (hf : ContDiff ℝ ∞ f) :
    let L := fderiv ℝ f x
    let R := LinearMap.range L.toLinearMap
    let G := (R.orthogonalProjection.comp L).ker
    ∃ e : OpenPartialHomeomorph E (R × G),
      x ∈ e.source ∧
      (∀ y, (e y).1 = R.orthogonalProjection (f y)) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ r z, (r,z) ∈ e.target →
        ContDiffAt ℝ ∞ (fun w : G => Rᗮ.orthogonalProjection (f (e.symm (r,w)))) z) ∧
      (∀ r z, (r,z) ∈ e.target →
        Module.finrank ℝ (LinearMap.range (fderiv ℝ f (e.symm (r,z))).toLinearMap) ≤ Module.finrank ℝ R →
        HasFDerivAt (fun w : G => Rᗮ.orthogonalProjection (f (e.symm (r,w))))
          (0 : G →L[ℝ] Rᗮ) z) := by
  dsimp only
  let L := fderiv ℝ f x
  let R := LinearMap.range L.toLinearMap
  let G := (R.orthogonalProjection.comp L).ker
  obtain ⟨φ,e,_,_,_,_,_,he,_,_,_,hsm,hsi,hfirst,hreg⟩ :=
    SardGenuineSmoothProjectedRankChartProbe.exists_genuine_smooth_projected_rank_chart f x hf
  refine ⟨e,he,hfirst,hsm,hsi,hreg,?_⟩
  intro r z hz hrank
  let y := e.symm (r,z)
  let D := fderiv ℝ f y
  let slice := fun w : G => e.symm (r,w)
  let J := fderiv ℝ slice z
  have hd : HasFDerivAt f D y := (hf.differentiable (by simp) y).hasFDerivAt
  have hj : HasFDerivAt slice J z :=
    (SardProjectedChartInverseSliceContDiffOnProbe.contDiffAt_inverseSlice_of_contDiffOn_symm
      e ∞ hsi r z hz).differentiableAt (by simp) |>.hasFDerivAt
  have hp : HasFDerivAt (fun a => R.orthogonalProjection (f a))
      (R.orthogonalProjection.comp D) y := R.orthogonalProjection.hasFDerivAt.comp y hd
  have hsurj : (R.orthogonalProjection.comp D).range = ⊤ :=
    SardSmoothProjectedChartFirstDerivativeSurjectiveProbe.range_eq_top_of_eq_fst_smooth_chart
      e (hsm.of_le (by simp)) (hsi.of_le (by simp))
      (fun a => R.orthogonalProjection (f a)) y (e.map_target hz)
      (R.orthogonalProjection.comp D) hp (funext fun a => (hfirst a).symm)
  have hpj : (R.orthogonalProjection.comp D).comp J = 0 :=
    SardProjectedChartSliceProjectedDerivativeZeroProbe.projected_deriv_comp_sliceDeriv_eq_zero
      e (fun a => R.orthogonalProjection (f a)) (funext hfirst) r z hz
      (R.orthogonalProjection.comp D) J hp hj
  have hzero : Rᗮ.orthogonalProjection.comp (D.comp J) = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    apply SardRankUpperResidualSliceAnnihilationProbe.residual_annihilates_slice_of_rankUpper
      D.toLinearMap R.orthogonalProjection.toLinearMap Rᗮ.orthogonalProjection.toLinearMap
      J.toLinearMap hsurj hrank
    exact congrArg ContinuousLinearMap.toLinearMap hpj
  exact SardProjectedChartResidualSliceDerivativeZeroProbe.hasFDerivAt_zero_residual_comp_slice
    f slice Rᗮ.orthogonalProjection z D J hd hj hzero

#print axioms exists_rank_upper_residual_zero
end SardGenuineSmoothRankUpperResidualZeroProbe
