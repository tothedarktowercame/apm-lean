import Mathlib.Data.ENNReal.Inv

/-! # ENNReal enlarged half-radius ratio -/

/-- Express the ratio of an enlarged radius to a positive half-radius as one
`ENNReal.ofReal` coercion, exposing its inverse-radius dependence. -/
theorem ENNReal.enlarged_halfRadius_ratio
    (R ρ : ℝ) (hρ : 0 < ρ) :
    ENNReal.ofReal (R + ρ / 2) / ENNReal.ofReal (ρ / 2) =
      ENNReal.ofReal ((2 * R + ρ) / ρ) := by
  rw [← ENNReal.ofReal_div_of_pos (half_pos hρ)]
  congr 1
  field_simp

#print axioms ENNReal.enlarged_halfRadius_ratio
