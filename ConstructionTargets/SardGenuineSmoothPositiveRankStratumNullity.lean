import ConstructionTargets.SardGenuineSmoothOpenRankUpperImageNullity
import ConstructionTargets.SardFiniteOrderRankLocusLocalAggregation

open Set MeasureTheory
open scoped ContDiff
noncomputable section
namespace SardGenuineSmoothPositiveRankStratumNullityProbe
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
      ∀ (H : Type u) [NormedAddCommGroup H] [NormedSpace ℝ H]
        [FiniteDimensional ℝ H] [CompleteSpace H],
        Module.finrank ℝ H < Module.finrank ℝ E →
        ∀ (q : H → V) (s : Set H),
          (∀ z ∈ s, ContDiffAt ℝ ∞ q z) →
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
    SardGenuineSmoothOpenRankUpperImageNullityProbe.exists_open_rank_upper_image_null
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
end SardGenuineSmoothPositiveRankStratumNullityProbe
