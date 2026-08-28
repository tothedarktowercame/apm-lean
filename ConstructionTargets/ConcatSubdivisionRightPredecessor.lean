import ConstructionTargets.ConcatSubdivisionRightSuffixPeel

/-!
# Predecessor coordinates in the concatenated right block
-/

open CategoryTheory
noncomputable section

namespace ConstructionTargets.ConcatSubdivisionRightPredecessor

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.PathSubdivisionConcatenation
open ConstructionTargets.ConcatSubdivisionRightSuffix
open ConstructionTargets.ComposeFinAppend

variable {X : Type*} [TopologicalSpace X]
variable {x y z : X} {p : Path x y} {q : Path y z} {U V : Set X}

/-- Consecutive right segments share their structural ambient vertex. -/
theorem rightSegment_succ_castSucc
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (j : Fin T.n) :
    (rightSegment S T j.castSucc).succ =
      (rightSegment S T j.succ).castSucc := by
  apply Fin.ext
  rfl

/-- The right-block vertex between consecutive right segments is both the
target of the predecessor and the source of the successor. -/
theorem rightBlockVertex_internal
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (j : Fin T.n) :
    rightBlockVertex S T j.castSucc.succ =
      (rightSegment S T j.castSucc).succ ∧
    rightBlockVertex S T j.succ.castSucc =
      (rightSegment S T j.succ).castSucc := by
  constructor
  · exact rightBlockVertex_succ S T j.castSucc
  · exact rightBlockVertex_castSucc S T j.succ

/-- A proof-carrying predecessor coordinate transports the terminal arrow of
any restricted prefix to the corresponding literal right-block arrow.  This
is the induction-step analogue of `finalConcatArrow_eq_transported_rightBlock`.
-/
theorem predecessorConcatArrow_eq_transported_rightBlock
    {C : Type*} [Category C]
    (D : @FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V)
    (j : Fin (T.n + 1))
    (k : Fin ((concatSubdivision S T).n + 1))
    (hk : k = rightSegment S T j) :
    D.mappedPiece (concatSubdivision S T) k =
      eqToHom (congrArg
          (fun r ↦ D.obj ((concatSubdivision S T).point r))
          (congrArg Fin.castSucc hk)) ≫
        D.mappedPiece (concatSubdivision S T) (rightSegment S T j) ≫
        eqToHom (congrArg
          (fun r ↦ D.obj ((concatSubdivision S T).point r))
          (congrArg Fin.succ hk)).symm := by
  exact dependentArrow_conjugation
    (fun r ↦ D.obj ((concatSubdivision S T).point r))
    (D.mappedPiece (concatSubdivision S T)) hk

#print axioms rightSegment_succ_castSucc
#print axioms rightBlockVertex_internal
#print axioms predecessorConcatArrow_eq_transported_rightBlock

end ConstructionTargets.ConcatSubdivisionRightPredecessor
