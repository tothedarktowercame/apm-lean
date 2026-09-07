import ConstructionTargets.SardExponentCombination

open scoped ENNReal

/-- The raw Euclidean packing factor and order-`k+1` Taylor-ball factor
combine to a positive residual power once the Morse--Sard exponent equation is
supplied.  Restricting the scale to at most one makes the numerator uniform. -/
theorem ENNReal.raw_taylor_packing_product_le
    (R C r : ℝ) (m n k d : ℕ)
    (hC : 0 ≤ C) (hr : 0 < r) (hr1 : r ≤ 1)
    (hexp : (k + 1) * n = m + d) :
    ENNReal.ofReal ((2 * R + r) / r) ^ m *
        ENNReal.ofReal (C * r ^ (k + 1)) ^ n ≤
      ENNReal.ofReal (2 * R + 1) ^ m * ENNReal.ofReal C ^ n *
        ENNReal.ofReal r ^ d := by
  have hr0 : ENNReal.ofReal r ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le.mpr hr]
  have hrt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  apply ENNReal.mul_bounds_cancel_dimension hr0 hrt
  · rw [ENNReal.ofReal_div_of_pos hr, div_eq_mul_inv, mul_pow]
    gcongr
  · rw [ENNReal.ofReal_mul hC, mul_pow, ENNReal.ofReal_pow (le_of_lt hr), ← pow_mul,
      hexp]

#print axioms ENNReal.raw_taylor_packing_product_le
