import Mathlib.Data.ENNReal.Inv

/-! # ENNReal ball-volume ratio -/

/-- Cancel a common nonzero finite volume constant and combine the remaining
quotient of powers into the corresponding power of a quotient. -/
theorem ENNReal.power_volume_ratio
    (a b k : ENNReal) (d : ℕ) (hk0 : k ≠ 0) (hkt : k ≠ ⊤) :
    (a ^ d * k) / (b ^ d * k) = (a / b) ^ d := by
  rw [ENNReal.mul_div_mul_right _ _ hk0 hkt]
  rw [div_eq_mul_inv, ENNReal.inv_pow, ← mul_pow, ← div_eq_mul_inv]

#print axioms ENNReal.power_volume_ratio
