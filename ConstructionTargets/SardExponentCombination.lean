import Mathlib.Data.ENNReal.Inv

/-! # Combine source-cover and target-ball exponents -/

/-- Multiplying an inverse `m`-dimensional cover bound by an `(m + d)`-power
target bound cancels the dimension exponent, leaving the positive surplus `d`. -/
theorem ENNReal.mul_bounds_cancel_dimension
    {card per A B r : ENNReal} {m d : ℕ}
    (hr0 : r ≠ 0) (hrt : r ≠ ⊤)
    (hcard : card ≤ A * r⁻¹ ^ m)
    (hper : per ≤ B * r ^ (m + d)) :
    card * per ≤ A * B * r ^ d := by
  calc
    card * per ≤ (A * r⁻¹ ^ m) * (B * r ^ (m + d)) :=
      mul_le_mul' hcard hper
    _ = A * B * ((r⁻¹ * r) ^ m) * r ^ d := by
      rw [pow_add, mul_pow]
      simp only [mul_assoc, mul_left_comm, mul_comm]
    _ = A * B * r ^ d := by rw [ENNReal.inv_mul_cancel hr0 hrt, one_pow, mul_one]

#print axioms ENNReal.mul_bounds_cancel_dimension
