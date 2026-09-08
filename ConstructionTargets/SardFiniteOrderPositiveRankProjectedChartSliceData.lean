import ConstructionTargets.SardFiniteOrderProjectedSmoothChartTargetData
import ConstructionTargets.SardFiniteOrderProjectedChartOrthogonalResidualSliceZero

open Set

noncomputable section
namespace SardFiniteOrderPositiveRankProjectedChartSliceDataProbe

theorem exists_finiteOrder_projectedChart_residualSliceZero
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E → F) (x : E) (L : E →L[ℝ] F) (U : Set E) (r order : ℕ)
    (hU : IsOpen U) (hxU : x ∈ U)
    (horder : order ≠ 0) (hstrict : HasStrictFDerivAt f L x)
    (hf : ContDiffOn ℝ order f univ)
    (hrank : Module.finrank ℝ (LinearMap.range L.toLinearMap) = r)
    (hrankUpper : ∀ z ∈ U, Module.finrank ℝ
      (LinearMap.range (fderiv ℝ f z).toLinearMap) ≤ r) :
    let R := LinearMap.range L.toLinearMap
    let G := (R.orthogonalProjection.comp L).ker
    ∃ chart : OpenPartialHomeomorph E (R × G),
      x ∈ chart.source ∧
      (fun y => (chart y).1) = (fun y => R.orthogonalProjection (f y)) ∧
      ContDiffOn ℝ order chart.symm chart.target ∧
      ∀ c z, (c, z) ∈ chart.target →
        HasFDerivAt
          (fun w : G => Rᗮ.orthogonalProjection (f (chart.symm (c, w))))
          (0 : G →L[ℝ] Rᗮ) z := by
  dsimp only
  obtain ⟨chart₀, hx, hfirst, _hchart, hsymm, hsurj⟩ :=
    SardFiniteOrderProjectedSmoothChartTargetDataProbe.exists_projected_finiteOrderChart_target_data
      f x L order horder hstrict (hf.contDiffAt (by simp))
  let chart := chart₀.restr U
  have hsource : chart.source = chart₀.source ∩ U := chart₀.restr_source' U hU
  have hx' : x ∈ chart.source := by rw [hsource]; exact ⟨hx, hxU⟩
  have hfirst' : (fun y => (chart y).1) =
      fun y => (LinearMap.range L.toLinearMap).orthogonalProjection (f y) := by
    simpa only [SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates_apply] using hfirst
  have htarget : chart.target ⊆ chart₀.target := by
    intro y hy
    change y ∈ (chart₀.restr U).target at hy
    rw [show (chart₀.restr U).target =
      chart₀.target ∩ chart₀.symm ⁻¹' interior U by rfl] at hy
    exact hy.1
  refine ⟨chart, hx', hfirst', hsymm.mono htarget, ?_⟩
  apply SardFiniteOrderProjectedChartOrthogonalResidualSliceZeroProbe.forall_hasFDerivAt_zero_orthogonalResidual_inverseSlice_finiteOrder
    f L r order horder chart hfirst' (hsymm.mono htarget)
      (hf.mono (fun _ _ => mem_univ _)) hrank
    (fun z hz => by rw [hsource] at hz; exact hrankUpper z hz.2)
  intro z hz
  rw [hsource] at hz
  exact hsurj z hz.1 (fderiv ℝ f z)
    ((hf.differentiableOn (by exact_mod_cast horder)).differentiableAt (by simp)).hasFDerivAt

#print axioms exists_finiteOrder_projectedChart_residualSliceZero

end SardFiniteOrderPositiveRankProjectedChartSliceDataProbe
