import ConstructionTargets.SardDerivativeRangeCoordinateTopologyPackage
import ConstructionTargets.SardDerivativeRangeInheritedBorelSpace
import ConstructionTargets.SardCompactCoordinateFiberImageNullity
import ConstructionTargets.SardTargetOrthogonalCoordinateEquiv
import ConstructionTargets.SardClosedOpenCompactExhaustion
import ConstructionTargets.SardCountableCompactImageNullity
import ConstructionTargets.SardFiniteOrderRankLocusLocalAggregation
import ConstructionTargets.SardPositiveRankSliceOpenInductionContract

open Set MeasureTheory
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 800000
namespace SardOpenContractCompactProbe
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
    (∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      [FiniteDimensional ℝ H] [CompleteSpace H],
      Module.finrank ℝ H < Module.finrank ℝ E →
      ∀ (q : H → Rᗮ) (U s : Set H),
        IsOpen U → s ⊆ U → ContDiffOn ℝ ∞ q U →
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
    SardPositiveRankSliceOpenInductionContractProbe.exists_positive_rank_slice_image_null
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
end SardOpenContractCompactProbe


open Set MeasureTheory
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 800000
namespace SardOpenContractChartProbe
universe u v
variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem exists_open_rank_upper_image_null
    (f : E → F) (x : E) (hf : ContDiff ℝ ∞ f)
    (hpos : 0 < Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap))
    (hlt : Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) < Module.finrank ℝ F) :
    let L := fderiv ℝ f x
    let R := LinearMap.range L.toLinearMap
    let G := (R.orthogonalProjection.comp L).ker
    ∀ (μF : Measure F) [μF.IsAddHaarMeasure] (μR : Measure R) [μR.IsAddHaarMeasure],
    ∀ (μ : Measure Rᗮ) [μ.IsAddHaarMeasure],
    (∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      [FiniteDimensional ℝ H] [CompleteSpace H],
      Module.finrank ℝ H < Module.finrank ℝ E →
      ∀ (q : H → Rᗮ) (U s : Set H),
        IsOpen U → s ⊆ U → ContDiffOn ℝ ∞ q U →
        μ (q '' (s ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0) →
    ∃ e : OpenPartialHomeomorph E (R × G),
      x ∈ e.source ∧
      (∀ y, (e y).1 = R.orthogonalProjection (f y)) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      μF (f '' ({y | Module.finrank ℝ (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ Module.finrank ℝ R} ∩ e.source)) = 0 := by
  dsimp only
  let L := fderiv ℝ f x
  let R := LinearMap.range L.toLinearMap
  intro μF hμF μR hμR μ hμ hind
  obtain ⟨e,he,hfirst,hsm,hsi,hcompact⟩ :=
    SardOpenContractCompactProbe.exists_compact_positive_rank_image_null
      f x hf hpos hlt μF μR μ hind
  refine ⟨e,he,hfirst,hsm,hsi,?_⟩
  let s : Set E := {y | Module.finrank ℝ (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ Module.finrank ℝ R}
  have hs : IsClosed s :=
    SardDerivativeRankUpperLocusClosedProbe.isClosed_derivativeRankAtMost f
      (Module.finrank ℝ R) (hf.of_le (by simp))
  obtain ⟨K,hK,hcover⟩ :=
    SardClosedOpenCompactExhaustionProbe.exists_compact_cover_inter_of_isClosed_isOpen
      s e.source hs e.open_source
  have hsub : ∀ n, K n ⊆ s ∩ e.source := by
    intro n y hy
    rw [← hcover]
    exact mem_iUnion_of_mem n hy
  apply SardCountableCompactImageNullityProbe.measure_image_zero_of_countable_compact_cover
    μF f (s ∩ e.source) K hK (by rw [hcover])
  intro n
  exact hcompact (K n) (hK n) (fun y hy => (hsub n hy).2)
    (fun y hy => (hsub n hy).1)

#print axioms exists_open_rank_upper_image_null
end SardOpenContractChartProbe


open Set MeasureTheory
open scoped ContDiff
noncomputable section
namespace SardPositiveRankStratumOpenContractAssemblyProbe
universe u v

theorem measure_image_zero_positive_rank_stratum
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μF : Measure F) [μF.IsAddHaarMeasure]
    (f : E → F) (hf : ContDiff ℝ ∞ f) (r : ℕ)
    (hr : 0 < r) (hrF : r < Module.finrank ℝ F)
    (hind : ∀ (V : Type v) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V],
      ∀ (μ : Measure V) [μ.IsAddHaarMeasure],
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [FiniteDimensional ℝ H] [CompleteSpace H],
        Module.finrank ℝ H < Module.finrank ℝ E →
        ∀ (q : H → V) (U s : Set H),
          IsOpen U → s ⊆ U → ContDiffOn ℝ ∞ q U →
          μ (q '' (s ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0) :
    μF (f '' rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r) = 0 := by
  letI : ProperSpace E := FiniteDimensional.proper ℝ E
  letI : SecondCountableTopology E := inferInstance
  apply SardFiniteOrderRankLocusLocalAggregationProbe.measure_image_zero_of_rankLocus_pointwise_open
  intro x hx
  have hxrank : Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) = r := hx
  let L := fderiv ℝ f x
  let R := LinearMap.range L.toLinearMap
  obtain ⟨hBR,hBS⟩ :=
    SardDerivativeRangeInheritedBorelSpaceProbe.range_orthogonal_inherited_borelSpace L
  letI : BorelSpace R := hBR
  letI : BorelSpace Rᗮ := hBS
  obtain ⟨hPR,hSCR,hPS,hSCS⟩ :=
    SardDerivativeRangeCoordinateTopologyPackageProbe.range_orthogonal_topology_package L
  letI : ProperSpace R := hPR
  letI : ProperSpace Rᗮ := hPS
  let μR : Measure R := Measure.addHaar
  let μS : Measure Rᗮ := Measure.addHaar
  have hμS : μS.IsAddHaarMeasure := inferInstance
  obtain ⟨e,he,hfirst,hsm,hsi,hnull⟩ :=
    SardOpenContractChartProbe.exists_open_rank_upper_image_null
      f x hf (by rw [hxrank]; exact hr) (by rw [hxrank]; exact hrF)
      μF μR μS (@hind Rᗮ _ _ _ _ hBS μS hμS)
  refine ⟨e.source,e.open_source,he,measure_mono_null ?_ hnull⟩
  rintro y ⟨z,⟨hz,hze⟩,rfl⟩
  refine ⟨z,⟨?_,hze⟩,rfl⟩
  change Module.finrank ℝ (LinearMap.range (fderiv ℝ f z).toLinearMap) ≤
    Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap)
  rw [hxrank]
  exact hz.le

#print axioms measure_image_zero_positive_rank_stratum
theorem measure_image_zero_positive_rank_stratum_of_global_induction
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μF : Measure F) [μF.IsAddHaarMeasure]
    (f : E → F) (hf : ContDiff ℝ ∞ f) (r : ℕ)
    (hr : 0 < r) (hrF : r < Module.finrank ℝ F)
    (hind : ∀ (V : Type v) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V],
      ∀ (μ : Measure V) [μ.IsAddHaarMeasure],
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [FiniteDimensional ℝ H] [CompleteSpace H],
        Module.finrank ℝ H < Module.finrank ℝ E →
        ∀ q : H → V, ContDiff ℝ ∞ q →
          μ (q '' {z | ¬ Function.Surjective (fderiv ℝ q z)}) = 0) :
    μF (f '' rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r) = 0 := by
  apply measure_image_zero_positive_rank_stratum μF f hf r hr hrF
  intro V hN hI hD hM hB μ hμ
  exact SardPositiveRankSliceOpenInductionContractProbe.open_induction_of_global
    (E := E) μ (@hind V hN hI hD hM hB μ hμ)
#print axioms measure_image_zero_positive_rank_stratum_of_global_induction
end SardPositiveRankStratumOpenContractAssemblyProbe
