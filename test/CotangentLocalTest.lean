import ConstructionTargets.CotangentLocal

open Complex Real
open ConstructionTargets.CotangentLocal

noncomputable section

example (z : ℂ) : Complex.cot ((Real.pi : ℂ) * (z + (3 : ℂ))) =
    Complex.cot ((Real.pi : ℂ) * z) := by
  simpa using cot_pi_add_int z 3

example : ((1 : ℂ) / 2) ∈ Complex.integerComplement := by
  apply mem_integerComplement_of_norm_lt_one
  · norm_num
  · norm_num

/-- The local calculation exposes the linear cotangent coefficient used by
the `ζ(2)` contour. -/
example : deriv regularCot 0 = -(Real.pi : ℂ) ^ 2 / 3 :=
  deriv_regularCot_zero

/-- The same calculation exposes the residue coefficient used by the
`ζ(4)` contour. -/
example : iteratedDeriv 3 regularCot 0 / 6 = -(Real.pi : ℂ) ^ 4 / 45 :=
  cot_cubic_coefficient

/-- The fourth-order quotient used to remove the pole at zero is represented
by an analytic function, not by an assumed Laurent expansion. -/
example {z : ℂ} (hz : z ≠ 0) :
    cotFourthRemainder z = cotFourthNumerator z / z ^ 4 :=
  cotFourthRemainder_eq_div hz

#print axioms ConstructionTargets.CotangentLocal.differentiable_sincPi
#print axioms ConstructionTargets.CotangentLocal.deriv_regularCot_zero
#print axioms ConstructionTargets.CotangentLocal.cot_cubic_coefficient
#print axioms ConstructionTargets.CotangentLocal.cotFourthRemainder_eq_div
#print axioms ConstructionTargets.CotangentLocal.regularCot_eq_cot_sub_inv
