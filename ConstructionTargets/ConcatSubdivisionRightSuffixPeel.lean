import ConstructionTargets.ConcatSubdivisionRightFold
import ConstructionTargets.ComposeFinArbitrarySplit

/-!
# Final-arrow peel for the concatenated right block
-/

open CategoryTheory
noncomputable section

namespace ConstructionTargets.ConcatSubdivisionRightSuffixPeel

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.PathSubdivisionConcatenation
open ConstructionTargets.ConcatSubdivisionRightSuffix
open ConstructionTargets.ConcatSubdivisionRightFold
open ConstructionTargets.ComposeFinAppend

variable {X : Type*} [TopologicalSpace X]
variable {x y z : X} {p : Path x y} {q : Path y z} {U V : Set X}

/-- The final right segment is literally the final segment index of the full
concatenated subdivision, propositionally rather than definitionally. -/
theorem rightSegment_last_eq_concat_last
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    rightSegment S T (Fin.last T.n) =
      Fin.last ((concatSubdivision S T).n) := by
  apply Fin.ext
  simp [rightSegment, concatSubdivision]
  omega

/-- The terminal structural right-block vertex is the terminal full-chain
vertex. -/
theorem rightBlockVertex_last_eq_concat_last
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    rightBlockVertex S T (Fin.last (T.n + 1)) =
      Fin.last ((concatSubdivision S T).n + 1) := by
  rw [show Fin.last (T.n + 1) = (Fin.last T.n).succ by apply Fin.ext; rfl,
    rightBlockVertex_succ, rightSegment_last_eq_concat_last]
  apply Fin.ext
  rfl

/-- The final arrow exposed by `composeFin_succ` is the final right-block
arrow after displaying the endpoint index transports. -/
theorem finalConcatArrow_eq_transported_rightBlock
    {C : Type*} [Category C]
    (D : @FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    D.mappedPiece (concatSubdivision S T)
        (Fin.last ((concatSubdivision S T).n)) =
      eqToHom (congrArg
          (fun k ↦ D.obj ((concatSubdivision S T).point k))
          (congrArg Fin.castSucc
            (rightSegment_last_eq_concat_last S T)).symm) ≫
        D.mappedPiece (concatSubdivision S T)
          (rightSegment S T (Fin.last T.n)) ≫
        eqToHom (congrArg
          (fun k ↦ D.obj ((concatSubdivision S T).point k))
          (congrArg Fin.succ
            (rightSegment_last_eq_concat_last S T)).symm).symm := by
  exact dependentArrow_conjugation
    (fun k ↦ D.obj ((concatSubdivision S T).point k))
    (D.mappedPiece (concatSubdivision S T))
    (rightSegment_last_eq_concat_last S T).symm

#print axioms rightSegment_last_eq_concat_last
#print axioms rightBlockVertex_last_eq_concat_last
#print axioms finalConcatArrow_eq_transported_rightBlock

end ConstructionTargets.ConcatSubdivisionRightSuffixPeel
