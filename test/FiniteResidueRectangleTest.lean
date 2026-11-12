import ConstructionTargets.FiniteResidueRectangle

open Complex
open ConstructionTargets.RectangleCauchy
open ConstructionTargets.FiniteResidueRectangle

noncomputable section

/-- Two explicitly listed simple poles give the sum of their residues. -/
example : centeredSquareBoundaryIntegral
    (fun z : ℂ => 3 * (z - (1 : ℂ))⁻¹ + 5 * (z - (-1 : ℂ))⁻¹) 2 =
    2 * Real.pi * I * (3 + 5) := by
  let s : Finset ℝ := {1, -1}
  let c : ℝ → ℂ := fun a => if a = 1 then 3 else 5
  have h := centeredSquareBoundaryIntegral_eq_finset_residues
    (fun z : ℂ => 3 * (z - (1 : ℂ))⁻¹ + 5 * (z - (-1 : ℂ))⁻¹)
    (fun _ => 0) s c 2 (by norm_num)
    (by intro a ha; simp [s] at ha ⊢; rcases ha with rfl | rfl <;> norm_num)
    (by fun_prop)
    (by
      intro z hz
      norm_num [s, c, Finset.sum_insert])
  norm_num [s, c, Finset.sum_insert] at h ⊢
  exact h

#print axioms ConstructionTargets.FiniteResidueRectangle.centeredSquareBoundaryIntegral_eq_finset_residues
