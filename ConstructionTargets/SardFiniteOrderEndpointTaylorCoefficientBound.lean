import ConstructionTargets.SardTaylorFiniteTargetCoverMeasure
import ConstructionTargets.SardTaylorPackingExponentNormalization

open Metric Set MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace SardFiniteOrderEndpointTaylorCoefficientBoundProbe

theorem endpoint_taylor_image_measure_le_coefficient
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (f : E → F) (K : Set E) (centres : Finset E)
    (R C : ℝ) (ρ : ℝ≥0) (k : ℕ)
    (hC : 0 ≤ C) (hρ0 : 0 < ρ) (hρ1 : (ρ : ℝ) ≤ 1)
    (hexp : (k + 1) * Module.finrank ℝ F = Module.finrank ℝ E)
    (hcover : IsCover ρ K (↑centres : Set E))
    (hcard : (centres.card : ENNReal) ≤
      ENNReal.ofReal ((2 * R + (ρ : ℝ)) / (ρ : ℝ)) ^ Module.finrank ℝ E)
    (hrem : ∀ a ∈ centres, ∀ x ∈ K,
      ‖f x - f a‖ ≤ C * ‖x - a‖ ^ (k + 1)) :
    volume (f '' K) ≤
      (ENNReal.ofReal (2 * R + 1) ^ Module.finrank ℝ E *
        ENNReal.ofReal C ^ Module.finrank ℝ F) *
          ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ F /
            Real.Gamma (Module.finrank ℝ F / 2 + 1)) := by
  let kF : ENNReal := ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ F /
    Real.Gamma (Module.finrank ℝ F / 2 + 1))
  have htaylor := finiteCover_taylor_image_measure_le_card_mul_ballVolume
    f K centres ρ C k hC hcover hrem
  calc
    volume (f '' K) ≤ centres.card *
        (ENNReal.ofReal (C * (ρ : ℝ) ^ (k + 1)) ^ Module.finrank ℝ F * kF) :=
      htaylor.2
    _ ≤ ENNReal.ofReal ((2 * R + (ρ : ℝ)) / (ρ : ℝ)) ^ Module.finrank ℝ E *
        (ENNReal.ofReal (C * (ρ : ℝ) ^ (k + 1)) ^ Module.finrank ℝ F * kF) := by
      exact mul_le_mul_left hcard _
    _ = (ENNReal.ofReal ((2 * R + (ρ : ℝ)) / (ρ : ℝ)) ^ Module.finrank ℝ E *
        ENNReal.ofReal (C * (ρ : ℝ) ^ (k + 1)) ^ Module.finrank ℝ F) * kF := by
      ac_rfl
    _ ≤ (ENNReal.ofReal (2 * R + 1) ^ Module.finrank ℝ E *
        ENNReal.ofReal C ^ Module.finrank ℝ F * ENNReal.ofReal (ρ : ℝ) ^ 0) * kF := by
      exact mul_le_mul_left
        (ENNReal.raw_taylor_packing_product_le R C (ρ : ℝ)
          (Module.finrank ℝ E) (Module.finrank ℝ F) k 0 hC
          (by exact_mod_cast hρ0) hρ1 (by simpa using hexp)) _
    _ = (ENNReal.ofReal (2 * R + 1) ^ Module.finrank ℝ E *
        ENNReal.ofReal C ^ Module.finrank ℝ F) * kF := by simp
    _ = _ := rfl

#print axioms endpoint_taylor_image_measure_le_coefficient

end SardFiniteOrderEndpointTaylorCoefficientBoundProbe
