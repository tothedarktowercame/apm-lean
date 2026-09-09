import ConstructionTargets.SardGenuineSmoothPositiveRankStratumNullity
import ConstructionTargets.SardSmoothCompactRankZeroInduction
import ConstructionTargets.SardClosedOpenImageNullity
import ConstructionTargets.SardCriticalRankStrataNull
import ConstructionTargets.SardZeroDimensionalBorelCriticalImage
open Set MeasureTheory
open scoped ContDiff
noncomputable section
namespace SardGenuineSmoothGlobalCriticalInductionStepProbe
universe u v

theorem critical_image_null_of_local_smooth_induction
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μF : Measure F) [μF.IsAddHaarMeasure]
    (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hind : ∀ (V : Type v) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V],
      ∀ (μ : Measure V) [μ.IsAddHaarMeasure],
      ∀ (H : Type u) [NormedAddCommGroup H] [NormedSpace ℝ H]
        [FiniteDimensional ℝ H] [CompleteSpace H],
        Module.finrank ℝ H < Module.finrank ℝ E →
        ∀ (q : H → V) (s : Set H),
          (∀ z ∈ s, ContDiffAt ℝ ∞ q z) →
          μ (q '' (s ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0) :
    μF (f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  classical
  cases subsingleton_or_nontrivial F with
  | inl hF =>
    letI := hF
    have he : {x | ¬ Function.Surjective (fderiv ℝ f x)} = (∅ : Set E) := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      exact fun y => ⟨0, Subsingleton.elim _ _⟩
    simp [he]
  | inr hF =>
    letI := hF
    cases subsingleton_or_nontrivial E with
    | inl hE =>
      letI := hE
      simpa using criticalImage_zero_of_source_finrank_zero_borel μF f univ
        ((finrank_zero_iff_forall_zero).2 (fun x => Subsingleton.elim x 0))
    | inr hE =>
      letI := hE
      letI : MeasurableSpace E := borel E
      letI : BorelSpace E := ⟨rfl⟩
      letI : ProperSpace E := FiniteDimensional.proper ℝ E
      have hzero : μF (f '' rankStratum (fun x => (fderiv ℝ f x).toLinearMap) 0) = 0 := by
        have hs : IsClosed (rankStratum (fun x => (fderiv ℝ f x).toLinearMap) 0) := by
          simpa [rankStratum, Nat.le_zero] using
            SardDerivativeRankUpperLocusClosedProbe.isClosed_derivativeRankAtMost f 0 (hf.of_le (by simp))
        have hn := SardClosedOpenImageNullityProbe.measure_image_zero_of_closed_inter_open
          μF f (rankStratum (fun x => (fderiv ℝ f x).toLinearMap) 0) univ hs isOpen_univ
          (fun K hK hsub => ?_)
        · simpa using hn
        apply SardSmoothCompactRankZeroInductionProbe.compact_rankZero_image_null_of_smooth_local_induction
          μF f K hK hf _ (hind F μF)
        intro y hy
        have hz : Module.finrank ℝ (LinearMap.range (fderiv ℝ f y).toLinearMap) = 0 := (hsub hy).1
        have hb : LinearMap.range (fderiv ℝ f y).toLinearMap = ⊥ :=
          Submodule.finrank_eq_zero.mp hz
        apply ContinuousLinearMap.coe_injective
        exact LinearMap.range_eq_bot.mp hb
      change μF (f '' criticalSet (fun x => (fderiv ℝ f x).toLinearMap)) = 0
      apply criticalImage_null_of_rankStrata_null
      intro r
      rcases Nat.eq_zero_or_pos r.val with hr | hr
      · simpa [hr] using hzero
      · exact SardGenuineSmoothPositiveRankStratumNullityProbe.measure_image_zero_positive_rank_stratum
          μF f hf r.val hr r.isLt hind
#print axioms critical_image_null_of_local_smooth_induction
end SardGenuineSmoothGlobalCriticalInductionStepProbe
