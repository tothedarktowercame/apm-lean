import ConstructionTargets.ConcatSubdivisionRightSuffix
import ConstructionTargets.ComposeFinConjugation

/-!
# The right-block fold of a concatenated subdivision
-/

open CategoryTheory
noncomputable section

namespace ConstructionTargets.ConcatSubdivisionRightFold

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.PathSubdivisionConcatenation
open ConstructionTargets.ConcatSubdivisionRightSuffix
open ConstructionTargets.ComposeFinConjugation

variable {X : Type*} [TopologicalSpace X]
variable {x y z : X} {p : Path x y} {q : Path y z} {U V : Set X}
variable {C : Type*} [Category C]

/-- Objects of the literal right block, retained in the ambient concatenated
subdivision coordinate. -/
def rightBlockObject (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V) (T : PathTwoOpenSubdivision q U V)
    (j : Fin (T.n + 2)) : C :=
  D.obj ((concatSubdivision S T).point (rightBlockVertex S T j))

/-- The actual concatenated mapped piece, transported to the structural
right-block endpoints. -/
def rightBlockArrow (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V) (T : PathTwoOpenSubdivision q U V)
    (j : Fin (T.n + 1)) :
    rightBlockObject D S T j.castSucc ⟶ rightBlockObject D S T j.succ :=
  eqToHom (congrArg (fun k ↦ D.obj ((concatSubdivision S T).point k))
      (rightBlockVertex_castSucc S T j)) ≫
    D.mappedPiece (concatSubdivision S T) (rightSegment S T j) ≫
    eqToHom (congrArg (fun k ↦ D.obj ((concatSubdivision S T).point k))
      (rightBlockVertex_succ S T j)).symm

/-- The object-coordinate isomorphism from the structural right block to the
original subdivision `T`. -/
def rightBlockObjectIso (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V) (T : PathTwoOpenSubdivision q U V)
    (j : Fin (T.n + 2)) : rightBlockObject D S T j ≅ D.obj (T.point j) :=
  eqToIso (congrArg D.obj (rightBlockVertex_point S T j))

/-- Each transported right-block arrow is the corresponding `T` arrow,
conjugated by the point-coordinate isomorphisms. -/
theorem rightBlockArrow_eq_conjugate
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V) (T : PathTwoOpenSubdivision q U V)
    (j : Fin (T.n + 1)) :
    rightBlockArrow D S T j =
      (rightBlockObjectIso D S T j.castSucc).hom ≫ D.mappedPiece T j ≫
        (rightBlockObjectIso D S T j.succ).inv := by
  rw [rightBlockArrow, mappedPiece_concat_right]
  simp [rightBlockObjectIso, rightBlockObject, rightBlockVertex_succ]

/-- The whole literal right-block fold is `T`'s fold with only its midpoint
and terminal point transports remaining. -/
theorem rightBlockComposeFin_eq
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V) (T : PathTwoOpenSubdivision q U V) :
    TwoOpenDescentDatum.composeFin (rightBlockObject D S T)
        (rightBlockArrow D S T) =
      (rightBlockObjectIso D S T 0).hom ≫
        TwoOpenDescentDatum.composeFin (D.obj ∘ T.point) (D.mappedPiece T) ≫
        (rightBlockObjectIso D S T (Fin.last (T.n + 1))).inv := by
  apply composeFin_conjugation
  exact rightBlockArrow_eq_conjugate D S T

#print axioms rightBlockArrow_eq_conjugate
#print axioms rightBlockComposeFin_eq

end ConstructionTargets.ConcatSubdivisionRightFold
