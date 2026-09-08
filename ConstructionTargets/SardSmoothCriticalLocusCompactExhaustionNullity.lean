import ConstructionTargets.SardCompactSmoothInductionNullity
import ConstructionTargets.SardClosedSetCompactExhaustion
import ConstructionTargets.SardCountableCompactImageNullity
import ConstructionTargets.SardDerivativeRankUpperLocusClosed

open Set MeasureTheory

noncomputable section
namespace SardSmoothCriticalLocusCompactExhaustionNullityProbe

theorem smooth_criticalLocus_image_zero_of_compact_induction
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
    [SecondCountableTopology E] [SigmaCompactSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μF : Measure F) [μF.IsAddHaarMeasure]
    (f : E → F) (hf : ContDiff ℝ (⊤ : WithTop ℕ∞) f)
    (hcompact : ∀ K : Set E, IsCompact K →
      K ⊆ {x | ¬ Function.Surjective (fderiv ℝ f x)} → μF (f '' K) = 0) :
    μF (f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  let r := Module.finrank ℝ F - 1
  have hcritical : {x | ¬ Function.Surjective (fderiv ℝ f x)} =
      {x | Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) ≤ r} := by
    ext x
    simp only [mem_setOf_eq]
    change (¬ Function.Surjective (fderiv ℝ f x).toLinearMap) ↔ _
    rw [← LinearMap.range_eq_top]
    have hpos : 0 < Module.finrank ℝ F := Module.finrank_pos
    constructor
    · intro hne
      have hlt : Module.finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap) <
          Module.finrank ℝ F := by
        simpa using Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hne)
      omega
    · intro hle htop
      rw [htop, finrank_top] at hle
      omega
  obtain ⟨K, hKcompact, hKcover⟩ :=
    SardClosedSetCompactExhaustionProbe.exists_countable_compact_cover_of_isClosed
      {x | ¬ Function.Surjective (fderiv ℝ f x)}
      (hcritical.symm ▸ SardDerivativeRankUpperLocusClosedProbe.isClosed_derivativeRankAtMost
        f r (hf.of_le le_top))
  apply SardCountableCompactImageNullityProbe.measure_image_zero_of_countable_compact_cover
    μF f {x | ¬ Function.Surjective (fderiv ℝ f x)} K hKcompact
  · rw [hKcover]
  · intro i
    apply hcompact (K i) (hKcompact i)
    rw [← hKcover]
    exact subset_iUnion K i

#print axioms smooth_criticalLocus_image_zero_of_compact_induction

end SardSmoothCriticalLocusCompactExhaustionNullityProbe
