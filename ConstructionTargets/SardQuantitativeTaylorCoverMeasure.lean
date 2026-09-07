import ConstructionTargets.SardMaximalSeparatedFiniteDimensionalCoverCardinality
import ConstructionTargets.SardTaylorFiniteTargetCoverMeasure
import ConstructionTargets.SardTaylorPackingExponentNormalization
import ConstructionTargets.SardNNRealGeometricScaleTolerance

open Metric Set MeasureTheory
open scoped ENNReal NNReal

/-- Quantitative finite-dimensional Taylor covering: under the positive
Morse--Sard exponent surplus, every positive tolerance admits a finite source
cover whose Taylor target-ball cover has image volume below that tolerance. -/
theorem exists_taylor_cover_measure_lt
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (f : E → F) (K : Set E) (hK : IsCompact K) (z : E) (R C : ℝ)
    (hbounded : K ⊆ closedBall z R) (hC : 0 ≤ C)
    (k d : ℕ) (hd : 0 < d)
    (hexp : (k + 1) * Module.finrank ℝ F = Module.finrank ℝ E + d)
    (hrem : ∀ a ∈ K, ∀ x ∈ K,
      ‖f x - f a‖ ≤ C * ‖x - a‖ ^ (k + 1))
    (hk0 : ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E /
      Real.Gamma (Module.finrank ℝ E / 2 + 1)) ≠ 0)
    (hkt : ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ E /
      Real.Gamma (Module.finrank ℝ E / 2 + 1)) ≠ ⊤)
    (q : ℝ≥0) (hq0 : 0 < q) (hq1 : q < 1)
    (ε : ENNReal) (hε : 0 < ε) :
    ∃ (j : ℕ) (centres : Finset E),
      (↑centres : Set E) ⊆ K ∧
      IsSeparated ((q ^ j : ℝ≥0) : ENNReal) (↑centres : Set E) ∧
      IsCover (q ^ j) K (↑centres : Set E) ∧
      (f '' K ⊆ ⋃ a ∈ centres,
        closedBall (f a) (C * ((q ^ j : ℝ≥0) : ℝ) ^ (k + 1))) ∧
      volume (f '' K) < ε := by
  let kF : ENNReal := ENNReal.ofReal (√Real.pi ^ Module.finrank ℝ F /
    Real.Gamma (Module.finrank ℝ F / 2 + 1))
  let D : ENNReal :=
    ENNReal.ofReal (2 * R + 1) ^ Module.finrank ℝ E *
      ENNReal.ofReal C ^ Module.finrank ℝ F * kF
  have hD : D ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) ENNReal.ofReal_ne_top
  obtain ⟨j, hj⟩ := ENNReal.exists_nnreal_geometric_scale_pow_lt
    D ε q d hq0 hq1 hd hε hD
  let ρ : ℝ≥0 := q ^ j
  have hρ0 : 0 < ρ := by simp [ρ, hq0]
  have hρ1 : (ρ : ℝ) ≤ 1 := by
    exact_mod_cast (pow_le_one₀ (by positivity : 0 ≤ q) (le_of_lt hq1) : q ^ j ≤ 1)
  obtain ⟨centres, hcentres, hsep, hcover, hcard⟩ :=
    exists_finiteDimensional_maximalSeparated_cover_card_le
      K hK z R hbounded ρ hρ0 hk0 hkt
  have htaylor := finiteCover_taylor_image_measure_le_card_mul_ballVolume
    f K centres ρ C k hC hcover (fun a ha ↦ hrem a (hcentres ha))
  refine ⟨j, centres, hcentres, ?_, ?_, htaylor.1, ?_⟩
  · simpa [ρ] using hsep
  · simpa [ρ] using hcover
  · calc
      volume (f '' K) ≤ centres.card *
          (ENNReal.ofReal (C * (ρ : ℝ) ^ (k + 1)) ^ Module.finrank ℝ F * kF) := by
            simpa [kF] using htaylor.2
      _ ≤ ENNReal.ofReal ((2 * R + (ρ : ℝ)) / (ρ : ℝ)) ^
            Module.finrank ℝ E *
          (ENNReal.ofReal (C * (ρ : ℝ) ^ (k + 1)) ^ Module.finrank ℝ F * kF) := by
        exact mul_le_mul_left hcard _
      _ = (ENNReal.ofReal ((2 * R + (ρ : ℝ)) / (ρ : ℝ)) ^
            Module.finrank ℝ E *
          ENNReal.ofReal (C * (ρ : ℝ) ^ (k + 1)) ^ Module.finrank ℝ F) * kF := by
        ac_rfl
      _ ≤ (ENNReal.ofReal (2 * R + 1) ^ Module.finrank ℝ E *
          ENNReal.ofReal C ^ Module.finrank ℝ F * ENNReal.ofReal (ρ : ℝ) ^ d) * kF :=
        by
          exact mul_le_mul_left
            (ENNReal.raw_taylor_packing_product_le R C (ρ : ℝ)
            (Module.finrank ℝ E) (Module.finrank ℝ F) k d hC
            (by exact_mod_cast hρ0) hρ1 hexp) _
      _ = D * ENNReal.ofReal ((q : ℝ) ^ j) ^ d := by
        simp only [D, kF, ρ, NNReal.coe_pow]
        ac_rfl
      _ < ε := hj

#print axioms exists_taylor_cover_measure_lt
