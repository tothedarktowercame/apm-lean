import Mathlib.CategoryTheory.Category.Preorder

/-!
# Typed transport of functor maps from thin categories
-/

open CategoryTheory

namespace ConstructionTargets.FunctorMapPreorderTransport

universe u v w

variable {P : Type u} [Preorder P]
variable {C : Type v} [Category.{w} C]

/-- A functor map out of a preorder, rewritten after propositionally changing
both endpoints.  The endpoint transports are part of the statement, so no
dependent rewrite beneath `Functor.map` is required. -/
theorem map_eq_eqToHom_comp_map_comp_eqToHom
    (F : P ⥤ C) {a b a' b' : P} (u : a ⟶ b) (u' : a' ⟶ b')
    (ha : a = a') (hb : b = b') :
    F.map u = eqToHom (congrArg F.obj ha) ≫ F.map u' ≫
      eqToHom (congrArg F.obj hb).symm := by
  subst a'
  subst b'
  simpa using congrArg F.map (Subsingleton.elim u u')

variable {Q : Type*} [Preorder Q]

/-- The corresponding statement for a functor restricted along a functor
between preorders. -/
theorem comp_map_eq_eqToHom_comp_map_comp_eqToHom
    (E : P ⥤ Q) (F : Q ⥤ C) {a b : P} {a' b' : Q}
    (u : a ⟶ b) (u' : a' ⟶ b')
    (ha : E.obj a = a') (hb : E.obj b = b') :
    (E ⋙ F).map u = eqToHom (congrArg F.obj ha) ≫ F.map u' ≫
      eqToHom (congrArg F.obj hb).symm := by
  change F.map (E.map u) = _
  exact map_eq_eqToHom_comp_map_comp_eqToHom F (E.map u) u' ha hb

#print axioms map_eq_eqToHom_comp_map_comp_eqToHom
#print axioms comp_map_eq_eqToHom_comp_map_comp_eqToHom

end ConstructionTargets.FunctorMapPreorderTransport
