import ConstructionTargets.SardFiniteOrderLocalEndpointSmallCoefficientNullity
import ConstructionTargets.SardMaximalSeparatedFiniteDimensionalCoverCardinality

open Metric Set MeasureTheory
open scoped ENNReal NNReal

theorem localEndpoint_coverData_of_compact_remainder
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (f : E → F) (K : Set E) (hK : IsCompact K) (z : E) (R C δ : ℝ)
    (k : ℕ) (ε : ENNReal) (hbounded : K ⊆ closedBall z R)
    (hC : 0 ≤ C) (hδ : 0 < δ)
    (hk0 : ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E /
      Real.Gamma (Module.finrank ℝ E / 2 + 1)) ≠ 0)
    (hrem : ∀ a ∈ K, ∀ x ∈ K, dist x a < δ →
      ‖f x - f a‖ ≤ C * ‖x - a‖ ^ (k + 1))
    (hsmall : (ENNReal.ofReal (2 * R + 1) ^ Module.finrank ℝ E *
      ENNReal.ofReal C ^ Module.finrank ℝ F) *
        ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ F /
          Real.Gamma (Module.finrank ℝ F / 2 + 1)) < ε) :
    LocalEndpointSmallCoefficientCoverData f K R k ε := by
  let r : ℝ := min 1 (δ / 2)
  have hr : 0 < r := lt_min (by norm_num) (half_pos hδ)
  let ρ : ℝ≥0 := ⟨r, hr.le⟩
  have hρ : 0 < ρ := hr
  obtain ⟨centres, hsub, _, hcover, hcard⟩ :=
    exists_finiteDimensional_maximalSeparated_cover_card_le K hK z R hbounded
      ρ hρ hk0 ENNReal.ofReal_ne_top
  refine ⟨C, ρ, centres, hC, hρ, min_le_left _ _, hcover, hcard, ?_, hsmall⟩
  intro a ha x hx
  apply hrem a (hsub ha) x hx.1
  exact (mem_closedBall.mp hx.2).trans_lt
    ((min_le_right 1 (δ / 2)).trans_lt (half_lt_self hδ))

#print axioms localEndpoint_coverData_of_compact_remainder
