import ConstructionTargets.ProductSimplexUnitSteps

open CategoryTheory Simplicial MonoidalCategory

namespace ConstructionTargets.ProductSimplexStepWord

universe u
open SSet
open ConstructionTargets.ProductSimplexMaximalPaths
open ConstructionTargets.ProductSimplexShuffleParity
open ConstructionTargets.ProductSimplexUnitSteps

/-- Boolean word of horizontal (`true`) and vertical (`false`) path steps. -/
noncomputable def stepWord {p q : ℕ}
    (z : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)) :
    Fin (p + q) → Bool := by
  classical
  exact fun i => if IsHorizontal z i then true else false

@[simp] theorem stepWord_eq_true_iff {p q : ℕ}
    (z : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)) (i : Fin (p + q)) :
    stepWord z i = true ↔ IsHorizontal z i := by
  classical
  simp [stepWord]

@[simp] theorem stepWord_eq_false_iff {p q : ℕ}
    (z : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)) (i : Fin (p + q)) :
    stepWord z i = false ↔ ¬ IsHorizontal z i := by
  classical
  simp [stepWord]

/-- A `true` letter has the exact horizontal coordinate behavior. -/
theorem stepWord_true_coordinates {p q : ℕ}
    (z : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)) (i : Fin (p + q))
    (hi : stepWord z i = true) :
    (((SSet.prodStdSimplex.objEquiv z.1 i.succ).1 : ℕ) =
        (SSet.prodStdSimplex.objEquiv z.1 i.castSucc).1 + 1 ∧
      ((SSet.prodStdSimplex.objEquiv z.1 i.succ).2 : ℕ) =
        (SSet.prodStdSimplex.objEquiv z.1 i.castSucc).2) := by
  have hh := (stepWord_eq_true_iff z i).mp hi
  rcases horizontal_or_vertical_unit_step z i with h | h
  · exact h
  · have hs := (isHorizontal_iff_first_coordinate_succ z i).mp hh
    omega

/-- A `false` letter has the exact vertical coordinate behavior. -/
theorem stepWord_false_coordinates {p q : ℕ}
    (z : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (p + q)) (i : Fin (p + q))
    (hi : stepWord z i = false) :
    (((SSet.prodStdSimplex.objEquiv z.1 i.succ).1 : ℕ) =
        (SSet.prodStdSimplex.objEquiv z.1 i.castSucc).1 ∧
      ((SSet.prodStdSimplex.objEquiv z.1 i.succ).2 : ℕ) =
        (SSet.prodStdSimplex.objEquiv z.1 i.castSucc).2 + 1) := by
  have hh := (stepWord_eq_false_iff z i).mp hi
  rcases horizontal_or_vertical_unit_step z i with h | h
  · have hs := (isHorizontal_iff_first_coordinate_succ z i).not.mp hh
    omega
  · exact h


end ConstructionTargets.ProductSimplexStepWord
