import ConstructionTargets.SardFiniteDimensionalPackingCoverBound
import ConstructionTargets.SardMaximalSeparatedFinsetCover
import ConstructionTargets.SardCompactPackingNumberFinite
import ConstructionTargets.SardSeparatedENNRealToRealDist

open Metric Set MeasureTheory
open scoped ENNReal NNReal

/-- A compact subset of a finite-dimensional real inner-product space admits a
finite radius-separated radius-cover whose cardinality has the explicit
Euclidean polynomial bound. -/
theorem exists_finiteDimensional_maximalSeparated_cover_card_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    (K : Set E) (hK : IsCompact K) (z : E) (R : ℝ)
    (hbounded : K ⊆ closedBall z R) (ρ : ℝ≥0) (hρ : 0 < ρ)
    (hk0 : ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E /
      Real.Gamma (Module.finrank ℝ E / 2 + 1)) ≠ 0)
    (hkt : ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E /
      Real.Gamma (Module.finrank ℝ E / 2 + 1)) ≠ ⊤) :
    ∃ C : Finset E, (↑C : Set E) ⊆ K ∧
      IsSeparated (ρ : ENNReal) (↑C : Set E) ∧
      IsCover ρ K (↑C : Set E) ∧
      (C.card : ENNReal) ≤
        ENNReal.ofReal ((2 * R + (ρ : ℝ)) / (ρ : ℝ)) ^ Module.finrank ℝ E := by
  have hp : packingNumber ρ K ≠ ⊤ := hK.packingNumber_ne_top ρ (ne_of_gt hρ)
  obtain ⟨C, hCK, hsep, hcover⟩ := exists_finset_maximal_separated_cover ρ hp
  refine ⟨C, hCK, hsep, hcover, ?_⟩
  apply finiteDimensional_card_le_enlarged_halfRadius_power
    C id z R (ρ : ℝ) (by exact_mod_cast hρ) _ _ hk0 hkt
  · intro i hi
    exact hbounded (hCK hi)
  · intro i hi j hj hij
    have hs : IsSeparated (ρ : ENNReal) (id '' (↑C : Set E)) := by
      simpa using hsep
    exact _root_.IsSeparated.real_dist_le hs hi hj (by simpa using hij)

#print axioms exists_finiteDimensional_maximalSeparated_cover_card_le
