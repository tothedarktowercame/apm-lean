import ConstructionTargets.SardGenuineSmoothCompactPositiveRankImageNullity
import ConstructionTargets.SardClosedOpenCompactExhaustion
import ConstructionTargets.SardCountableCompactImageNullity

open Set MeasureTheory
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 800000
namespace SardGenuineSmoothOpenRankUpperImageNullityProbe
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
      μF (f '' ({y | Module.finrank ℝ (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ Module.finrank ℝ R} ∩ e.source)) = 0 := by
  dsimp only
  let L := fderiv ℝ f x
  let R := LinearMap.range L.toLinearMap
  intro μF hμF μR hμR μ hμ hind
  obtain ⟨e,he,hfirst,hsm,hsi,hcompact⟩ :=
    SardGenuineSmoothCompactPositiveRankImageNullityProbe.exists_compact_positive_rank_image_null
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
end SardGenuineSmoothOpenRankUpperImageNullityProbe
