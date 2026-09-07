import ConstructionTargets.SardMaximalSeparatedFiniteDimensionalCoverCardinality
import ConstructionTargets.SardFlatTaylorBallImage
import ConstructionTargets.SardFiniteCoverMeasureBound
import ConstructionTargets.SardFiniteCoverCardinalityMeasure
import ConstructionTargets.SardFiniteDimensionalBallVolume

open Metric Set MeasureTheory
open scoped ENNReal NNReal

/-- A finite source cover, together with a uniform flat Taylor remainder at its
centres, gives a finite target-ball cover and its cardinality-times-volume
measure estimate. -/
theorem finiteCover_taylor_image_measure_le_card_mul_ballVolume
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (f : E → F) (K : Set E) (centres : Finset E) (ρ : ℝ≥0)
    (C : ℝ) (k : ℕ) (hC : 0 ≤ C)
    (hcover : IsCover ρ K (↑centres : Set E))
    (hrem : ∀ a ∈ centres, ∀ x ∈ K,
      ‖f x - f a‖ ≤ C * ‖x - a‖ ^ (k + 1)) :
    f '' K ⊆ ⋃ a ∈ centres,
        closedBall (f a) (C * (ρ : ℝ) ^ (k + 1)) ∧
      volume (f '' K) ≤
        centres.card *
          (ENNReal.ofReal (C * (ρ : ℝ) ^ (k + 1)) ^ Module.finrank ℝ F *
            ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ F /
              Real.Gamma (Module.finrank ℝ F / 2 + 1))) := by
  have hsource : K ⊆ ⋃ a ∈ centres, closedBall a (ρ : ℝ) := by
    simpa only [NNReal.smul_def] using
      (Metric.isCover_iff_subset_iUnion_closedBall.mp hcover)
  have htarget : f '' K ⊆ ⋃ a ∈ centres,
      closedBall (f a) (C * (ρ : ℝ) ^ (k + 1)) := by
    rintro y ⟨x, hxK, rfl⟩
    obtain ⟨a, haC, hxa⟩ := Set.mem_iUnion₂.mp (hsource hxK)
    apply Set.mem_iUnion_of_mem a
    apply Set.mem_iUnion_of_mem haC
    exact flatTaylor_image_inter_closedBall_subset f K a C (ρ : ℝ) k hC
      (hrem a haC) ⟨x, ⟨hxK, hxa⟩, rfl⟩
  refine ⟨htarget, (measure_le_finset_sum_of_subset_biUnion volume
    (f '' K) centres
    (fun a ↦ closedBall (f a) (C * (ρ : ℝ) ^ (k + 1))) htarget).trans ?_⟩
  apply finset_sum_le_card_mul
  intro a ha
  exact le_of_eq (InnerProductSpace.volume_closedBall (f a)
    (C * (ρ : ℝ) ^ (k + 1)))

#print axioms finiteCover_taylor_image_measure_le_card_mul_ballVolume
