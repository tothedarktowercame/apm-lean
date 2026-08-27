import ConstructionTargets.VaryingTargetChartNullityAssembly

/-! # Global dimension-drop nullity in one fixed target chart -/

open Set MeasureTheory
open scoped ContDiff Manifold
noncomputable section

namespace ConstructionTargets.FixedTargetChartDimensionDropNullity

open CountableExtendedChartRangeDecomposition
open EuclideanDimensionDropImageNullity
open VaryingTargetChartNullityAssembly

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace H'] (J : ModelWithCorners ℝ F H')
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [SecondCountableTopology M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]

/-- The image of one chart-pair patch is null in the target chart centered at
the image of the patch center.  The Euclidean representative is used only on
the literal source-chart image of the patch. -/
theorem chartPairPatch_extChartCoordinateNull
    (f : M → N) (hf : ContMDiff I J 1 f)
    (hdim : Module.finrank ℝ E < Module.finrank ℝ F)
    (μ : Measure F) [μ.IsAddHaarMeasure] (x : M) :
    ExtChartCoordinateNull J μ (f x) (f '' chartPairPatch I J f x) := by
  let patch := chartPairPatch I J f x
  let coord : E → F := extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm
  have hpatch_source : patch ⊆ (extChartAt I x).source := inter_subset_left
  have hpatch_target : MapsTo f patch (extChartAt J (f x)).source := by
    intro y hy
    exact hy.2
  have hcoord_contDiff : ContDiffOn ℝ 1 coord (extChartAt I x '' patch) :=
    (contMDiffOn_iff_of_subset_source' hpatch_source hpatch_target).mp
      hf.contMDiffOn
  have hcoord_diff : DifferentiableOn ℝ coord (extChartAt I x '' patch) :=
    hcoord_contDiff.differentiableOn one_ne_zero
  have hcoord_null : μ (coord '' (extChartAt I x '' patch)) = 0 :=
    addHaar_image_eq_zero_of_finrank_lt_differentiableOn
      hdim coord (extChartAt I x '' patch) hcoord_diff μ
  have himage :
      extChartAt J (f x) '' (f '' patch) =
        coord '' (extChartAt I x '' patch) := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨extChartAt I x y, ⟨y, hy, rfl⟩,
        (chartPairPatch_coordinate_equation I J f x y hy).symm⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨f y, ⟨y, hy, rfl⟩,
        chartPairPatch_coordinate_equation I J f x y hy⟩
  refine ⟨?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hpatch_target hy
  · rw [himage]
    exact hcoord_null

/-- A smooth strict-dimension-drop map has null range in every fixed target
extended chart.  The conclusion concerns the explicit add-Haar measure in
that chart's model space; it does not construct a measure on the manifold. -/
theorem fixed_extChartAt_range_inter_source_null
    (f : M → N) (hf : ContMDiff I J 1 f)
    (hdim : Module.finrank ℝ E < Module.finrank ℝ F)
    (μ : Measure F) [μ.IsAddHaarMeasure] (q : N) :
    μ (extChartAt J q '' (range f ∩ (extChartAt J q).source)) = 0 := by
  obtain ⟨centers, hcount, _, hrange⟩ :=
    exists_countable_chartPairPatch_range_decomposition I J f hf.continuous
  exact (fixed_extChartAt_null_of_chartPairPatch_range J μ I f centers hcount
    hrange (fun x _ ↦ chartPairPatch_extChartCoordinateNull I J f hf hdim μ x) q).2

#print axioms chartPairPatch_extChartCoordinateNull
#print axioms fixed_extChartAt_range_inter_source_null

end ConstructionTargets.FixedTargetChartDimensionDropNullity
