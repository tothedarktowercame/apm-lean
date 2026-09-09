import ConstructionTargets.SardDerivativeRangeCoordinateTopologyPackage
import ConstructionTargets.SardDerivativeRangeInheritedBorelSpace
import ConstructionTargets.SardGenuineSmoothPositiveRankSliceNullity
import ConstructionTargets.SardCompactCoordinateFiberImageNullity
import ConstructionTargets.SardTargetOrthogonalCoordinateEquiv

open Set MeasureTheory
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 800000
namespace SardGenuineSmoothCompactPositiveRankImageNullityProbe
universe u v
variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem exists_compact_positive_rank_image_null
    (f : E → F) (x : E) (hf : ContDiff ℝ ∞ f)
    (hpos : 0 < Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap))
    (hlt : Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) < Module.finrank ℝ F) :
    let L := fderiv ℝ f x
    let R := LinearMap.range L.toLinearMap
    let G := (R.orthogonalProjection.comp L).ker
    ∀ (μF : Measure F) [μF.IsAddHaarMeasure] (μR : Measure R) [μR.IsAddHaarMeasure],
    ∀ (μ : Measure Rᗮ) [μ.IsAddHaarMeasure],
    (∀ (H : Type u) [NormedAddCommGroup H] [NormedSpace ℝ H]
      [FiniteDimensional ℝ H] [CompleteSpace H],
      Module.finrank ℝ H < Module.finrank ℝ E →
      ∀ (q : H → Rᗮ) (s : Set H),
        (∀ z ∈ s, ContDiffAt ℝ ∞ q z) →
        μ (q '' (s ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0) →
    ∃ e : OpenPartialHomeomorph E (R × G),
      x ∈ e.source ∧
      (∀ y, (e y).1 = R.orthogonalProjection (f y)) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ (K : Set E), IsCompact K → K ⊆ e.source →
        (∀ y ∈ K, Module.finrank ℝ (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ Module.finrank ℝ R) →
        μF (f '' K) = 0 := by
  dsimp only
  let L := fderiv ℝ f x
  let R := LinearMap.range L.toLinearMap
  let G := (R.orthogonalProjection.comp L).ker
  obtain ⟨hPR,hSCR,hPS,hSCS⟩ :=
    SardDerivativeRangeCoordinateTopologyPackageProbe.range_orthogonal_topology_package L
  letI : ProperSpace R := hPR
  letI : ProperSpace Rᗮ := hPS
  let hLCR : LocallyCompactSpace R := inferInstance
  let hLCS : LocallyCompactSpace Rᗮ := inferInstance
  have hb := SardDerivativeRangeInheritedBorelSpaceProbe.range_orthogonal_inherited_borelSpace L
  letI : BorelSpace R := hb.1
  letI : BorelSpace Rᗮ := hb.2
  intro μF hμF μR hμR μ hμ hind
  obtain ⟨e,he,hdim,hnt,hfirst,hsm,hsi,hslices⟩ :=
    SardGenuineSmoothPositiveRankSliceNullityProbe.exists_positive_rank_slice_image_null
      f x hf hpos hlt μ hind
  refine ⟨e,he,hfirst,hsm,hsi,?_⟩
  intro K hK hKs hrank
  let coord := SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates R
  apply @SardCompactCoordinateFiberImageNullityProbe.measure_image_zero_of_compact_coordinate_fibers
    E F R Rᗮ inferInstance
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance hb.1 hLCR hSCR
    inferInstance inferInstance inferInstance hb.2 hLCS hSCS
    μF μR μ hμF hμR hμ coord f K hK hf.continuous.continuousOn
  intro r
  apply measure_mono_null _ (hslices r)
  rintro v ⟨y,⟨hy,hyfirst⟩,rfl⟩
  have hey := hKs hy
  have hp : (e y).1 = r := by
    rw [hfirst]
    have hc : coord (f y) = (R.orthogonalProjection (f y), Rᗮ.orthogonalProjection (f y)) :=
      SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates_apply R (f y)
    exact (congrArg Prod.fst hc).symm.trans hyfirst
  have hpair : (r,(e y).2) = e y := by
    rw [← hp]
  have hinv : e.symm (r,(e y).2) = y := by
    rw [hpair]
    exact e.left_inv hey
  refine ⟨(e y).2, ⟨?_,?_⟩,?_⟩
  · rw [hpair]
    exact e.map_source hey
  · rw [hinv]
    exact hrank y hy
  · change Rᗮ.orthogonalProjection (f (e.symm (r,(e y).2))) = (coord (f y)).2
    rw [hinv]
    simp [coord]

#print axioms exists_compact_positive_rank_image_null
end SardGenuineSmoothCompactPositiveRankImageNullityProbe
