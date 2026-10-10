import ConstructionTargets.PolygonThreeLoopHalfOpenNormalForm

noncomputable section

namespace ConstructionTargets.PointWedgeExactEquality

open PointWedgeQuotient

universe u v
variable {X : Type u} {Y : Type v}

private def leftCoordinate (x₀ : X) : Sum X Y → X
  | .inl x => x
  | .inr _ => x₀

private def rightCoordinate (y₀ : Y) : Sum X Y → Y
  | .inl _ => y₀
  | .inr y => y

private theorem leftCoordinate_eq_of_eqvGen (x₀ : X) (y₀ : Y)
    {a b : Sum X Y} (h : Relation.EqvGen (Rel x₀ y₀) a b) :
    leftCoordinate (Y := Y) x₀ a = leftCoordinate x₀ b := by
  induction h with
  | rel a b hab => cases hab; rfl
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem rightCoordinate_eq_of_eqvGen (x₀ : X) (y₀ : Y)
    {a b : Sum X Y} (h : Relation.EqvGen (Rel x₀ y₀) a b) :
    rightCoordinate (X := X) y₀ a = rightCoordinate y₀ b := by
  induction h with
  | rel a b hab => cases hab; rfl
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem quotientMap_inl_injective (x₀ : X) (y₀ : Y) :
    Function.Injective (fun x => quotientMap x₀ y₀ (.inl x)) := by
  intro x x' h
  exact leftCoordinate_eq_of_eqvGen x₀ y₀ (Quotient.exact h)

theorem quotientMap_inr_injective (x₀ : X) (y₀ : Y) :
    Function.Injective (fun y => quotientMap x₀ y₀ (.inr y)) := by
  intro y y' h
  exact rightCoordinate_eq_of_eqvGen x₀ y₀ (Quotient.exact h)

theorem quotientMap_inl_eq_inr_iff (x₀ : X) (y₀ : Y) (x : X) (y : Y) :
    quotientMap x₀ y₀ (.inl x) = quotientMap x₀ y₀ (.inr y) ↔
      x = x₀ ∧ y = y₀ := by
  constructor
  · intro h
    exact ⟨leftCoordinate_eq_of_eqvGen x₀ y₀ (Quotient.exact h),
      (rightCoordinate_eq_of_eqvGen x₀ y₀ (Quotient.exact h)).symm⟩
  · rintro ⟨rfl, rfl⟩
    exact Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)

end ConstructionTargets.PointWedgeExactEquality
