import ConstructionTargets.SardFiniteOrderLocalEndpointTaylorCoefficientBound
import ConstructionTargets.SardArbitrarilySmallMeasureLimit

open Metric Set MeasureTheory
open scoped ENNReal NNReal

noncomputable section

def LocalEndpointSmallCoefficientCoverData
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (f : E → F) (K : Set E) (R : ℝ) (k : ℕ) (ε : ENNReal) : Prop :=
  ∃ (C : ℝ) (ρ : ℝ≥0) (centres : Finset E),
    0 ≤ C ∧ 0 < ρ ∧ (ρ : ℝ) ≤ 1 ∧
    IsCover ρ K (↑centres : Set E) ∧
    (centres.card : ENNReal) ≤
      ENNReal.ofReal ((2 * R + (ρ : ℝ)) / (ρ : ℝ)) ^ Module.finrank ℝ E ∧
    (∀ a ∈ centres, ∀ x ∈ K ∩ closedBall a (ρ : ℝ),
      ‖f x - f a‖ ≤ C * ‖x - a‖ ^ (k + 1)) ∧
    (ENNReal.ofReal (2 * R + 1) ^ Module.finrank ℝ E *
      ENNReal.ofReal C ^ Module.finrank ℝ F) *
        ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ F /
          Real.Gamma (Module.finrank ℝ F / 2 + 1)) < ε

theorem endpoint_image_volume_eq_zero_of_localSmallCoefficientCoverData
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (f : E → F) (K : Set E) (R : ℝ) (k : ℕ)
    (hexp : (k + 1) * Module.finrank ℝ F = Module.finrank ℝ E)
    (hdata : ∀ ε : ENNReal, 0 < ε →
      LocalEndpointSmallCoefficientCoverData f K R k ε) :
    volume (f '' K) = 0 := by
  apply measure_eq_zero_of_le_inv_nat volume (f '' K)
  intro n
  cases n with
  | zero => simp
  | succ n =>
      have hε : 0 < ((n + 1 : ℕ) : ENNReal)⁻¹ :=
        ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _)
      obtain ⟨C, ρ, centres, hC, hρ0, hρ1, hcover, hcard, hrem, hsmall⟩ :=
        hdata _ hε
      exact (endpoint_localTaylor_image_measure_le_coefficient
        f K centres R C ρ k hC hρ0 hρ1 hexp hcover hcard hrem).trans hsmall.le

#print axioms endpoint_image_volume_eq_zero_of_localSmallCoefficientCoverData
