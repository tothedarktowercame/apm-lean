import ConstructionTargets.PolygonThreeLoopHalfOpenEquality

noncomputable section

namespace ConstructionTargets.RelationQuotientLeftInverse

universe u v
variable {A : Type u} {X : Type v} (R : A → A → Prop)

theorem eqvGen_respects (g : A → X)
    (hg : ∀ ⦃a b⦄, R a b → g a = g b)
    ⦃a b : A⦄ (h : Relation.EqvGen R a b) : g a = g b := by
  induction h with
  | rel a b hab => exact hg hab
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def descend (g : A → X) (hg : ∀ ⦃a b⦄, R a b → g a = g b) :
    Quotient (Relation.EqvGen.setoid R) → X :=
  Quotient.lift g (eqvGen_respects R g hg)

@[simp] theorem descend_mk (g : A → X)
    (hg : ∀ ⦃a b⦄, R a b → g a = g b) (a : A) :
    descend R g hg (Quotient.mk _ a) = g a := rfl

theorem quotient_mk_comp_injective_of_decoder
    (f : X → A) (g : A → X)
    (hg : ∀ ⦃a b⦄, R a b → g a = g b)
    (hgf : Function.LeftInverse g f) :
    Function.Injective (fun x : X => Quotient.mk (Relation.EqvGen.setoid R) (f x)) := by
  intro x y hxy
  have := congrArg (descend R g hg) hxy
  simpa [hgf x, hgf y] using this

theorem injective_of_quotient_formula
    (F : X → Quotient (Relation.EqvGen.setoid R))
    (f : X → A) (g : A → X)
    (hF : ∀ x, F x = Quotient.mk _ (f x))
    (hg : ∀ ⦃a b⦄, R a b → g a = g b)
    (hgf : Function.LeftInverse g f) : Function.Injective F := by
  intro x y hxy
  apply quotient_mk_comp_injective_of_decoder R f g hg hgf
  exact (hF x).symm.trans (hxy.trans (hF y))

end ConstructionTargets.RelationQuotientLeftInverse
