import ConstructionTargets.FundamentalGroupoidInsertionChainComparison
import ConstructionTargets.PathSubdivisionCommonRefinement

/-!
# Finite insertion reachability for subordinate path subdivisions
-/

open Set CategoryTheory
open scoped unitInterval

noncomputable section

namespace ConstructionTargets.PathSubdivisionInsertionReachability

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenInsertion
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.FundamentalGroupoidInsertionChainComparison

variable {X : Type*} [TopologicalSpace X]
variable {x y : X} {p : Path x y} {U V : Set X}

/-- `InsertionReachable S R` records an actual finite sequence of
`SingleVertexInsertion`s beginning at `S` and ending at `R`.  In particular,
both vertex coordinates and Boolean side labels are those produced by the
insertion operation at every step. -/
inductive InsertionReachable :
    PathTwoOpenSubdivision p U V → PathTwoOpenSubdivision p U V → Prop
  | refl (S) : InsertionReachable S S
  | step {S R} (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
      (tail : InsertionReachable ins.refined R) : InsertionReachable S R

namespace InsertionReachable

theorem trans {S R Q : PathTwoOpenSubdivision p U V}
    (hSR : InsertionReachable S R) (hRQ : InsertionReachable R Q) :
    InsertionReachable S Q := by
  induction hSR with
  | refl => exact hRQ
  | step ins tail ih => exact .step ins (ih hRQ)

theorem of_single {S : PathTwoOpenSubdivision p U V}
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    InsertionReachable S ins.refined :=
  .step ins (.refl _)

/-- A target presented as propositionally equal to one explicit refinement is
reachable.  This is the useful one-step interface for coordinate proofs. -/
theorem of_refined_eq {S R : PathTwoOpenSubdivision p U V}
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S)
    (hR : ins.refined = R) : InsertionReachable S R := by
  subst R
  exact of_single ins

/-- Insertion reachability can only increase the number of internal
subdivision vertices. -/
theorem n_le {S R : PathTwoOpenSubdivision p U V}
    (h : InsertionReachable S R) : S.n ≤ R.n := by
  induction h with
  | refl => exact le_rfl
  | step ins tail ih =>
      rw [PathTwoOpenSubdivision.SingleVertexInsertion.refined_n] at ih
      omega

variable {C : Type*} [Category C]

/-- Evaluation is invariant along every proof-carrying finite insertion
sequence. -/
theorem evaluate_eq
    (D : @TwoOpenDescentDatum X _ U V C _)
    {S R : PathTwoOpenSubdivision p U V}
    (h : InsertionReachable S R) : D.evaluate R = D.evaluate S := by
  induction h with
  | refl => rfl
  | step ins tail ih =>
      exact ih.trans
        (FundamentalGroupoidInsertionChainComparison.TwoOpenDescentDatum.evaluate_refined_eq
          D ins)

/-- Reversed orientation, convenient when rewriting an evaluation of the
source subdivision. -/
theorem evaluate_eq_source
    (D : @TwoOpenDescentDatum X _ U V C _)
    {S R : PathTwoOpenSubdivision p U V}
    (h : InsertionReachable S R) : D.evaluate S = D.evaluate R :=
  (evaluate_eq D h).symm

end InsertionReachable

/-- Exact data sufficient to recognize a one-step refinement.  Requiring an
equality with `ins.refined` keeps all dependent vertex, membership, and side
coordinates honest. -/
structure SingleInsertionPresentation
    (S R : PathTwoOpenSubdivision p U V) where
  insertion : PathTwoOpenSubdivision.SingleVertexInsertion S
  refined_eq : insertion.refined = R

namespace SingleInsertionPresentation

theorem reachable {S R : PathTwoOpenSubdivision p U V}
    (h : SingleInsertionPresentation S R) : InsertionReachable S R :=
  InsertionReachable.of_refined_eq h.insertion h.refined_eq

end SingleInsertionPresentation

#print axioms InsertionReachable.trans
#print axioms InsertionReachable.n_le
#print axioms InsertionReachable.evaluate_eq
#print axioms InsertionReachable.evaluate_eq_source
#print axioms SingleInsertionPresentation.reachable

end ConstructionTargets.PathSubdivisionInsertionReachability
