import ConstructionTargets.TwoOpenDescentFunctorLaws
import ConstructionTargets.ConcatSubdivisionShrinkingFoldRecurrence

/-!
# The ambient functor descended from two-open path data
-/

open Set CategoryTheory
noncomputable section

namespace ConstructionTargets.TwoOpenDescentFunctor

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.TwoOpenDescentQuotient
open ConstructionTargets.TwoOpenDescentFunctorLaws
open ConstructionTargets.ConcatSubdivisionShrinkingFoldRecurrence

variable {X : Type*} [TopologicalSpace X]
variable {U V : Set X}
variable {C : Type*} [Category C]

/-- The functor on the ambient fundamental groupoid obtained by evaluating
subordinate two-open subdivisions. -/
def twoOpenDescentFunctor (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    (D : @TwoOpenDescentDatum X _ U V C _) : FundamentalGroupoid X ⥤ C where
  obj x := D.obj x.as
  map f := quotientEvaluation hU hV hcover D f
  map_id x := quotientEvaluation_refl hU hV hcover D x.as
  map_comp := by
    rintro x y z ⟨p⟩ ⟨q⟩
    exact quotientEvaluation_trans hU hV hcover D
      (chosenSubdivision hU hV hcover p)
      (chosenSubdivision hU hV hcover q)

@[simp] theorem twoOpenDescentFunctor_obj (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    (D : @TwoOpenDescentDatum X _ U V C _) (x : FundamentalGroupoid X) :
    (twoOpenDescentFunctor hU hV hcover D).obj x = D.obj x.as := rfl

/-- Representative formula using any supplied subordinate subdivision. -/
@[simp] theorem twoOpenDescentFunctor_map_mk (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    (D : @TwoOpenDescentDatum X _ U V C _) {x y : X}
    (p : Path x y) (S : PathTwoOpenSubdivision p U V) :
    (twoOpenDescentFunctor hU hV hcover D).map
        (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk p)) =
      D.evaluate S :=
  quotientEvaluation_mk hU hV hcover D p S

#print axioms twoOpenDescentFunctor
#print axioms twoOpenDescentFunctor_obj
#print axioms twoOpenDescentFunctor_map_mk

end ConstructionTargets.TwoOpenDescentFunctor
