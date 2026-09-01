import ConstructionTargets.PointWedgeQuotient
import ConstructionTargets.PointedPuncturedCircleContraction
import Mathlib.Topology.CompactOpen

open Set
open unitInterval
open scoped ContinuousMap

noncomputable section

namespace ConstructionTargets.PointWedgePointedContractionDescent

open ConstructionTargets.PointWedgeQuotient
open ConstructionTargets.PointedPuncturedCircleContraction

universe u v

variable {X : Type u} {Y : Type v}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable {x₀ : X} {y₀ : Y}

omit [TopologicalSpace X] [TopologicalSpace Y] in
private theorem collapse_respects
    (a b : Sum X Y) (hab : Relation.EqvGen (Rel x₀ y₀) a b) :
    Sum.elim id (fun _ => x₀) a = Sum.elim id (fun _ => x₀) b := by
  induction hab with
  | rel a b hab => cases hab; rfl
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Collapse the right summand of a point wedge to the left basepoint. -/
def collapse : C(Wedge x₀ y₀, X) where
  toFun := Quotient.lift (Sum.elim id (fun _ => x₀)) collapse_respects
  continuous_toFun := by
    apply Continuous.quotient_lift
    rw [continuous_sum_dom]
    exact ⟨continuous_id, continuous_const⟩

/-- Include the left summand in the point wedge. -/
def includeLeft : C(X, Wedge x₀ y₀) where
  toFun x := quotientMap x₀ y₀ (.inl x)
  continuous_toFun := (continuous_quotientMap x₀ y₀).comp continuous_inl

def deformSum (h : PointedContraction Y y₀) (t : I) :
    Sum X Y → Wedge x₀ y₀
  | .inl x => quotientMap x₀ y₀ (.inl x)
  | .inr y => quotientMap x₀ y₀ (.inr (h.homotopy (t, y)))

omit [TopologicalSpace X] in
private theorem deform_respects
    (h : PointedContraction Y y₀) (t : I)
    (a b : Sum X Y) (hab : Relation.EqvGen (Rel x₀ y₀) a b) :
    deformSum (x₀ := x₀) h t a = deformSum (x₀ := x₀) h t b := by
  induction hab with
  | rel a b hab =>
      cases hab
      change quotientMap x₀ y₀ (.inl x₀) =
        quotientMap x₀ y₀ (.inr (h.homotopy (t, y₀)))
      rw [h.fixed]
      exact Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def deform (h : PointedContraction Y y₀) : I × Wedge x₀ y₀ → Wedge x₀ y₀ :=
  fun p => Quotient.lift
    (deformSum (x₀ := x₀) h p.1)
    (deform_respects h p.1) p.2

theorem deform_continuous (h : PointedContraction Y y₀) :
    Continuous (deform (x₀ := x₀) h) := by
  have hq : Topology.IsQuotientMap (quotientMap x₀ y₀) :=
    isQuotientMap_quotient_mk'
  apply hq.continuous_lift_prod_right
  let g : (I × X) ⊕ (I × Y) → Wedge x₀ y₀
    | .inl p => quotientMap x₀ y₀ (.inl p.2)
    | .inr p => quotientMap x₀ y₀ (.inr (h.homotopy p))
  have hg : Continuous g := by
    rw [continuous_sum_dom]
    exact ⟨(continuous_quotientMap x₀ y₀).comp
      (continuous_inl.comp continuous_snd),
      (continuous_quotientMap x₀ y₀).comp
        (continuous_inr.comp h.homotopy.continuous)⟩
  have heq : (fun p : I × Sum X Y =>
      deform (x₀ := x₀) h (p.1, quotientMap x₀ y₀ p.2)) =
      g ∘ Homeomorph.prodSumDistrib := by
    funext p
    rcases p with ⟨t, s⟩
    cases s <;> rfl
  rw [heq]
  exact hg.comp Homeomorph.prodSumDistrib.continuous

/-- The quotient-descended homotopy from the identity to collapse followed by
left inclusion. -/
def wedgeContractionHomotopy (h : PointedContraction Y y₀) :
    ContinuousMap.Homotopy (ContinuousMap.id (Wedge x₀ y₀))
      ((includeLeft (x₀ := x₀) (y₀ := y₀)).comp
        (collapse (x₀ := x₀) (y₀ := y₀))) where
  toFun := deform (x₀ := x₀) h
  continuous_toFun := deform_continuous (x₀ := x₀) h
  map_zero_left := by
    rintro ⟨a⟩
    cases a with
    | inl x => rfl
    | inr y =>
        exact congrArg (fun z => quotientMap x₀ y₀ (.inr z))
          (h.homotopy.map_zero_left y)
  map_one_left := by
    rintro ⟨a⟩
    cases a with
    | inl x => rfl
    | inr y =>
        change quotientMap x₀ y₀ (.inr (h.homotopy (1, y))) =
          quotientMap x₀ y₀ (.inl x₀)
        calc
          _ = quotientMap x₀ y₀ (.inr y₀) := congrArg
            (fun z => quotientMap x₀ y₀ (.inr z))
            (h.homotopy.map_one_left y)
          _ = quotientMap x₀ y₀ (.inl x₀) := (Quotient.sound
            (Relation.EqvGen.rel _ _ Rel.base)).symm

/-- A pointed contraction of the right summand descends through the point-wedge
quotient and deformation-retracts the wedge onto the whole left summand. -/
def wedgeHomotopyEquivLeft
    (h : PointedContraction Y y₀) : Wedge x₀ y₀ ≃ₕ X where
  toFun := collapse (x₀ := x₀) (y₀ := y₀)
  invFun := includeLeft (x₀ := x₀) (y₀ := y₀)
  left_inv := ⟨(wedgeContractionHomotopy (x₀ := x₀) h).symm⟩
  right_inv := by
    rw [show (collapse (x₀ := x₀) (y₀ := y₀)).comp
        (includeLeft (x₀ := x₀) (y₀ := y₀)) = ContinuousMap.id X by
      ext x
      rfl]

@[simp] theorem wedgeHomotopyEquivLeft_toFun_mk_left
    (h : PointedContraction Y y₀) (x : X) :
    wedgeHomotopyEquivLeft h (quotientMap x₀ y₀ (.inl x)) = x := rfl

@[simp] theorem wedgeHomotopyEquivLeft_toFun_mk_right
    (h : PointedContraction Y y₀) (y : Y) :
    wedgeHomotopyEquivLeft h (quotientMap x₀ y₀ (.inr y)) = x₀ := rfl

#print axioms wedgeHomotopyEquivLeft
#print axioms wedgeHomotopyEquivLeft_toFun_mk_left
#print axioms wedgeHomotopyEquivLeft_toFun_mk_right
#print axioms wedgeContractionHomotopy

end ConstructionTargets.PointWedgePointedContractionDescent
