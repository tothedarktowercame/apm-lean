import ConstructionTargets.SardGenuineSmoothGlobalCriticalInductionStep
import ConstructionTargets.SardFiniteOrderRankLocusLocalAggregation
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
open Set MeasureTheory Filter
open scoped ContDiff Topology
noncomputable section
namespace SardGenuineSmoothOpenDomainLocalizationProbe
universe u v
variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem exists_smooth_extension_near (f : E → F) (U : Set E) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (x : E) (hx : x ∈ U) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 x] f := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU x hx
  let b : ContDiffBump x := ⟨ε/4, ε/2, by positivity, by linarith⟩
  let g : E → F := fun y => b y • f y
  refine ⟨g, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · exact b.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hy))
    · have hn : y ∉ tsupport b := by
        rw [b.tsupport_eq]
        intro hb
        exact hy (hball (by
          change dist y x ≤ ε/2 at hb
          change dist y x < ε
          linarith))
      have he : g =ᶠ[𝓝 y] (fun _ => 0) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hn] with z hz
        have hz0 : b z = 0 := Function.notMem_support.mp (fun h => hz (subset_closure h))
        simp [g,hz0]
      exact contDiffAt_const.congr_of_eventuallyEq he
  · filter_upwards [b.eventuallyEq_one] with y hy
    simp [g,hy]


theorem local_image_null_of_global
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (hglobal : ∀ g : E → F, ContDiff ℝ ∞ g →
      μ (g '' {x | ¬ Function.Surjective (fderiv ℝ g x)}) = 0)
    (f : E → F) (U s : Set E) (hU : IsOpen U) (hs : s ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) :
    μ (f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)})) = 0 := by
  letI : ProperSpace E := FiniteDimensional.proper ℝ E
  apply SardFiniteOrderRankLocusLocalAggregationProbe.measure_image_zero_of_rankLocus_pointwise_open
  intro x hx
  obtain ⟨g,hg,he⟩ := exists_smooth_extension_near f U hU hf x (hs hx.1)
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp he
  refine ⟨V,hVo,hxV,measure_mono_null ?_ (hglobal g hg)⟩
  rintro y ⟨z,⟨hz,hzV⟩,rfl⟩
  have hez : g =ᶠ[𝓝 z] f := Filter.mem_of_superset (hVo.mem_nhds hzV) hV
  refine ⟨z, ?_, hV hzV⟩
  change ¬ Function.Surjective (fderiv ℝ g z)
  rw [hez.fderiv_eq]
  exact hz.2
#print axioms exists_smooth_extension_near
#print axioms local_image_null_of_global

theorem local_image_null_of_induction
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μF : Measure F) [μF.IsAddHaarMeasure]
    (f : E → F) (U s : Set E) (hU : IsOpen U) (hs : s ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hind : ∀ (V : Type v) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V],
      ∀ (μ : Measure V) [μ.IsAddHaarMeasure],
      ∀ (H : Type u) [NormedAddCommGroup H] [NormedSpace ℝ H]
        [FiniteDimensional ℝ H] [CompleteSpace H],
        Module.finrank ℝ H < Module.finrank ℝ E →
        ∀ (q : H → V) (s : Set H),
          (∀ z ∈ s, ContDiffAt ℝ ∞ q z) →
          μ (q '' (s ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0) :
    μF (f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)})) = 0  := by
  apply local_image_null_of_global μF _ f U s hU hs hf
  intro g hg
  exact SardGenuineSmoothGlobalCriticalInductionStepProbe.critical_image_null_of_local_smooth_induction
    μF g hg hind
#print axioms local_image_null_of_induction
end SardGenuineSmoothOpenDomainLocalizationProbe
