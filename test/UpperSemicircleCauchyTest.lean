import ConstructionTargets.UpperSemicircleCauchy

open Complex Real

noncomputable section

open ConstructionTargets.UpperSemicircleCauchy

/-- A constant entire integrand exercises both the diameter and arc terms of
the upper-semicircle identity. -/
example (R : ℝ) :
    (∫ _x : ℝ in -R..R, (1 : ℂ)) +
      ∫ θ : ℝ in 0..π,
        (1 : ℂ) * (I * R * Complex.exp (I * θ)) = 0 := by
  exact intervalIntegral_add_upperSemicircle_eq_zero
    (fun _ : ℂ => 1) (by fun_prop (disch := assumption)) R

#print axioms intervalIntegral_add_upperSemicircle_eq_zero
