import ConstructionTargets.SardENNRealPackingQuotient
import ConstructionTargets.SardENNRealBallVolumeRatio
import ConstructionTargets.SardENNRealEnlargedHalfRadiusRatio
import Mathlib.Data.Finset.Card

open scoped ENNReal

/-- A packing estimate expressed through exact power-law ball volumes gives the
explicit polynomial cardinality bound at a positive radius. -/
theorem finset_card_le_enlarged_halfRadius_power
    {X : Type*} (s : Finset X) (R ρ : ℝ) (k : ENNReal) (d : ℕ)
    (hρ : 0 < ρ) (hk0 : k ≠ 0) (hkt : k ≠ ⊤)
    (hpack : (s.card : ENNReal) *
        (ENNReal.ofReal (ρ / 2) ^ d * k) ≤
        ENNReal.ofReal (R + ρ / 2) ^ d * k) :
    (s.card : ENNReal) ≤ ENNReal.ofReal ((2 * R + ρ) / ρ) ^ d := by
  have hsmall0 : ENNReal.ofReal (ρ / 2) ^ d * k ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.mpr (half_pos hρ))) hk0
  have hsmallt : ENNReal.ofReal (ρ / 2) ^ d * k ≠ ⊤ := by
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hkt
  calc
    (s.card : ENNReal) ≤
        (ENNReal.ofReal (R + ρ / 2) ^ d * k) /
          (ENNReal.ofReal (ρ / 2) ^ d * k) :=
      ENNReal.le_div_of_mul_le hsmall0 hsmallt hpack
    _ = (ENNReal.ofReal (R + ρ / 2) /
          ENNReal.ofReal (ρ / 2)) ^ d :=
      ENNReal.power_volume_ratio _ _ _ _ hk0 hkt
    _ = ENNReal.ofReal ((2 * R + ρ) / ρ) ^ d := by
      rw [ENNReal.enlarged_halfRadius_ratio R ρ hρ]

#print axioms finset_card_le_enlarged_halfRadius_power
