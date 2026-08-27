import Mathlib

/- F△ deliberately removes mathematical difficulty from the live apparatus test. -/
theorem apm_ftriangle_pythagoras (a b : ℝ) (h : a = 3) (k : b = 4) :
    a ^ 2 + b ^ 2 = 25 := by
  -- Mathlib's `norm_num` closes the numerical equality after the frozen
  -- hypotheses rewrite the two real variables.
  norm_num [h, k]

#print axioms apm_ftriangle_pythagoras
