import ConstructionTargets.CotangentLocal

open Complex Real
open ConstructionTargets.CotangentLocal

noncomputable section

/-- The local calculation exposes the linear cotangent coefficient used by
the `ζ(2)` contour. -/
example : deriv regularCot 0 = -(Real.pi : ℂ) ^ 2 / 3 :=
  deriv_regularCot_zero

/-- The same calculation exposes the residue coefficient used by the
`ζ(4)` contour. -/
example : iteratedDeriv 3 regularCot 0 / 6 = -(Real.pi : ℂ) ^ 4 / 45 :=
  cot_cubic_coefficient

#print axioms ConstructionTargets.CotangentLocal.differentiable_sincPi
#print axioms ConstructionTargets.CotangentLocal.deriv_regularCot_zero
#print axioms ConstructionTargets.CotangentLocal.cot_cubic_coefficient
#print axioms ConstructionTargets.CotangentLocal.regularCot_eq_cot_sub_inv
