import ConstructionTargets.TwoOpenDescentHomotopyInvariance

/-!
# Quotient descent of two-open path evaluation
-/

open Set CategoryTheory
noncomputable section

namespace ConstructionTargets.TwoOpenDescentQuotient

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.PathSubdivisionEvaluationIndependence
open ConstructionTargets.TwoOpenDescentHomotopyInvariance

variable {X : Type*} [TopologicalSpace X]
variable {U V : Set X}
variable {C : Type*} [Category C]

/-- A subordinate certificate selected only to define the quotient map.  Its
choice disappears from the representative formula below. -/
def chosenSubdivision (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) {x y : X} (p : Path x y) :
    PathTwoOpenSubdivision p U V :=
  Classical.choice (exists_pathTwoOpenSubdivision p hU hV hcover)

/-- The common-coordinate morphism assigned to an endpoint-relative path
homotopy class. -/
def quotientEvaluation (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    (D : @TwoOpenDescentDatum X _ U V C _) {x y : X} :
    Path.Homotopic.Quotient x y → (D.obj x ⟶ D.obj y) :=
  Quotient.lift
    (fun p ↦ D.evaluate (chosenSubdivision hU hV hcover p))
    (fun p q hpq ↦ by
      change Path.Homotopic p q at hpq
      exact evaluate_eq_of_homotopic hU hV hcover hpq D
        (chosenSubdivision hU hV hcover p)
        (chosenSubdivision hU hV hcover q))

/-- The descended value at any representative is the evaluation of every
supplied subordinate certificate, not merely of the selected one. -/
theorem quotientEvaluation_mk (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    (D : @TwoOpenDescentDatum X _ U V C _) {x y : X}
    (p : Path x y) (S : PathTwoOpenSubdivision p U V) :
    quotientEvaluation hU hV hcover D (Path.Homotopic.Quotient.mk p) =
      D.evaluate S := by
  change D.evaluate (chosenSubdivision hU hV hcover p) = D.evaluate S
  exact evaluate_eq_of_subdivisions D _ _

#print axioms chosenSubdivision
#print axioms quotientEvaluation
#print axioms quotientEvaluation_mk

end ConstructionTargets.TwoOpenDescentQuotient
