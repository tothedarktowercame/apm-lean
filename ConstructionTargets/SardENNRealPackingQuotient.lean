import Mathlib.Data.ENNReal.Inv

/-! # Divide a finite packing inequality in ENNReal

This adapter turns the multiplicative estimate produced by a packing argument
into the quotient estimate used by the subsequent cardinality calculation.
-/

/-- If `b` is nonzero and finite, an upper bound on `a * b` gives the
corresponding quotient bound on `a`. -/
theorem ENNReal.le_div_of_mul_le
    {a b c : ENNReal} (hb0 : b ≠ 0) (hbt : b ≠ ⊤)
    (h : a * b ≤ c) : a ≤ c / b := by
  exact (ENNReal.le_div_iff_mul_le (Or.inl hb0) (Or.inl hbt)).2 h

#print axioms ENNReal.le_div_of_mul_le
