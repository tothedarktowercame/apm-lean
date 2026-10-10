import ConstructionTargets.StatementSurfaceModels

open ConstructionTargets
open ConstructionTargets.PointWedgeQuotient
open ConstructionTargets.StatementSurfaceModels

noncomputable section

namespace ConstructionTargets.CyclicThreeCirclesCollapse

def collapse : ThreeCircles → Circle :=
  Quotient.lift (Sum.elim (fun _ : TwoCircles => (1 : Circle)) id) (by
    intro a b h
    induction h with
    | rel a b hab => cases hab; rfl
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

@[simp] theorem collapse_left (x : TwoCircles) :
    collapse (quotientMap twoCirclesPoint (1 : Circle) (.inl x)) = 1 := rfl

@[simp] theorem collapse_right (z : Circle) :
    collapse (quotientMap twoCirclesPoint (1 : Circle) (.inr z)) = z := rfl

theorem continuous_collapse : Continuous collapse := by
  apply Continuous.quotient_lift
  exact continuous_const.sumElim continuous_id

def firstCircle : Circle → ThreeCircles :=
  fun z => quotientMap twoCirclesPoint (1 : Circle) (.inr z)

theorem continuous_firstCircle : Continuous firstCircle :=
  (continuous_quotientMap twoCirclesPoint (1 : Circle)).comp continuous_inr

@[simp] theorem collapse_firstCircle (z : Circle) : collapse (firstCircle z) = z := rfl

#print axioms collapse_left
#print axioms collapse_right
#print axioms continuous_collapse
#print axioms continuous_firstCircle
#print axioms collapse_firstCircle

end ConstructionTargets.CyclicThreeCirclesCollapse
