import ConstructionTargets.SardSeparatedBoundedBallPacking
import ConstructionTargets.SardPolynomialPackingCardinality
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- A separated finite family in a bounded finite-dimensional real inner-product
space has the explicit polynomial cardinality bound obtained from ball volumes. -/
theorem finiteDimensional_card_le_enlarged_halfRadius_power
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (s : Finset ι) (c : ι → E) (z : E) (R ρ : ℝ)
    (hρ : 0 < ρ)
    (hcenters : ∀ i ∈ s, c i ∈ closedBall z R)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ρ ≤ dist (c i) (c j))
    (hk0 : ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E /
      Real.Gamma (Module.finrank ℝ E / 2 + 1)) ≠ 0)
    (hkt : ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E /
      Real.Gamma (Module.finrank ℝ E / 2 + 1)) ≠ ⊤) :
    (s.card : ENNReal) ≤
      ENNReal.ofReal ((2 * R + ρ) / ρ) ^ Module.finrank ℝ E := by
  let k : ENNReal := ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E /
    Real.Gamma (Module.finrank ℝ E / 2 + 1))
  have hpack : (s.card : ENNReal) *
      (ENNReal.ofReal (ρ / 2) ^ Module.finrank ℝ E * k) ≤
      ENNReal.ofReal (R + ρ / 2) ^ Module.finrank ℝ E * k := by
    have h := finset_card_mul_le_measure_ball_of_separated
      volume s c z R ρ
      (ENNReal.ofReal (ρ / 2) ^ Module.finrank ℝ E * k)
      hcenters hsep
      (fun i hi ↦ le_of_eq (InnerProductSpace.volume_ball (c i) (ρ / 2)).symm)
    simpa [k, InnerProductSpace.volume_ball] using h
  exact finset_card_le_enlarged_halfRadius_power s R ρ k
    (Module.finrank ℝ E) hρ hk0 hkt hpack

#print axioms finiteDimensional_card_le_enlarged_halfRadius_power
