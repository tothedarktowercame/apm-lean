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

/-- The domain-restricted theorem applies when the remainder is only supplied
on the closed square. -/
example : centeredSquareBoundaryIntegral (fun z : ℂ => z + z⁻¹) 2 =
    2 * Real.pi * I := by
  have h := centeredSquareBoundaryIntegral_eq_finset_residues_of_differentiableOn
    (fun z : ℂ => z + z⁻¹) (fun z : ℂ => z) ({0} : Finset ℝ)
    (fun _ => 1) 2 (by norm_num) (by simp) (by fun_prop)
    (by
      exact ⟨(by fun_prop : Continuous (fun x : ℝ =>
          ((x : ℂ) + (-2 - 2 * I).im * I))).intervalIntegrable _ _,
        (by fun_prop : Continuous (fun x : ℝ =>
          ((x : ℂ) + (2 + 2 * I).im * I))).intervalIntegrable _ _,
        (by fun_prop : Continuous (fun y : ℝ =>
          ((2 + 2 * I).re : ℂ) + y * I)).intervalIntegrable _ _,
        (by fun_prop : Continuous (fun y : ℝ =>
          ((-2 - 2 * I).re : ℂ) + y * I)).intervalIntegrable _ _⟩)
    (by intro z hz; simp)
  simpa using h

#print axioms ConstructionTargets.FiniteResidueRectangle.centeredSquareBoundaryIntegral_eq_finset_residues_of_differentiableOn
