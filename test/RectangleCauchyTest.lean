import ConstructionTargets.RectangleCauchy

open Complex
open ConstructionTargets.RectangleCauchy

noncomputable section

/-- The packaged four-side expression agrees with Cauchy's theorem on the
nonconstant entire function `u ↦ u²`. -/
example (z w : ℂ) :
    rectangleBoundaryIntegral (fun u : ℂ => u ^ 2) z w = 0 := by
  exact rectangleBoundaryIntegral_eq_zero _ (by fun_prop) z w

/-- Linearity is checked on integrable polynomial boundary data. -/
example (z w : ℂ) :
    rectangleBoundaryIntegral (fun u : ℂ => 2 * u + u ^ 2) z w =
      rectangleBoundaryIntegral (fun u : ℂ => 2 * u) z w +
        rectangleBoundaryIntegral (fun u : ℂ => u ^ 2) z w := by
  have boundaryIntegrable_of_continuous (f : ℂ → ℂ) (hf : Continuous f) :
      RectangleBoundaryIntegrable f z w := by
    exact ⟨(hf.comp (by fun_prop)).intervalIntegrable _ _,
      (hf.comp (by fun_prop)).intervalIntegrable _ _,
      (hf.comp (by fun_prop)).intervalIntegrable _ _,
      (hf.comp (by fun_prop)).intervalIntegrable _ _⟩
  exact rectangleBoundaryIntegral_add
    (boundaryIntegrable_of_continuous _ (by fun_prop))
    (boundaryIntegrable_of_continuous _ (by fun_prop))

/-- The square winds once around each real point in its interior. -/
example :
    centeredSquareBoundaryIntegral (fun z => (z - (1 : ℂ))⁻¹) 2 =
      2 * Real.pi * I := by
  exact centeredSquareBoundaryIntegral_sub_inv 1 2 (by norm_num)

#print axioms ConstructionTargets.RectangleCauchy.rectangleBoundaryIntegral_eq_zero
#print axioms ConstructionTargets.RectangleCauchy.centeredSquareBoundaryIntegral_sub_inv
