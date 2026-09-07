import ConstructionTargets.SardSeparatedHalfBallsDisjoint
import ConstructionTargets.SardCenteredBallBoundedEnlargement
import ConstructionTargets.SardFinitePackingCardinalityBound
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

open MeasureTheory Metric Set

/-- Separated centers in a bounded ball give the finite packing inequality for
their half-radius balls inside the corresponding bounded enlargement. -/
theorem finset_card_mul_le_measure_ball_of_separated
    {X ι : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (s : Finset ι) (c : ι → X) (z : X) (R ρ : ℝ) (v : ENNReal)
    (hcenters : ∀ i ∈ s, c i ∈ closedBall z R)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ρ ≤ dist (c i) (c j))
    (hlow : ∀ i ∈ s, v ≤ μ (ball (c i) (ρ / 2))) :
    (s.card : ENNReal) * v ≤ μ (ball z (R + ρ / 2)) := by
  apply finset_card_mul_le_measure_of_disjoint μ s
    (fun i ↦ ball (c i) (ρ / 2)) (ball z (R + ρ / 2)) v
  · intro i hi
    exact measurableSet_ball
  · exact pairwiseDisjoint_ball_half_of_separated s c ρ hsep
  · exact hlow
  · intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    obtain ⟨his, hxi⟩ := hi
    exact ball_subset_ball_enlargement_of_center_mem_closedBall
      (hcenters i his) hxi

#print axioms finset_card_mul_le_measure_ball_of_separated
