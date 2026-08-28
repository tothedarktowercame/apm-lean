import ConstructionTargets.ConcatSubdivisionShrinkingPrefix
import ConstructionTargets.ComposeFinConjugation

/-!
# Restricted folds of shrinking concatenated prefixes
-/

open CategoryTheory
noncomputable section

namespace ConstructionTargets.ConcatSubdivisionShrinkingFold

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.PathSubdivisionConcatenation
open ConstructionTargets.ConcatSubdivisionShrinkingPrefix
open ConstructionTargets.ComposeFinConjugation

variable {X : Type*} [TopologicalSpace X]
variable {x y z : X} {p : Path x y} {q : Path y z} {U V : Set X}
variable {C : Type*} [Category C]

theorem shrinkingEndpoint_castSucc
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (i : Fin (concatSegmentCount S T - r)) :
    shrinkingVertexEmbedding S T r i.castSucc =
      (shrinkingSegmentEmbedding S T r i).castSucc := by
  apply Fin.ext
  rfl

theorem shrinkingEndpoint_succ
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (i : Fin (concatSegmentCount S T - r)) :
    shrinkingVertexEmbedding S T r i.succ =
      (shrinkingSegmentEmbedding S T r i).succ := by
  apply Fin.ext
  rfl

/-- Objects of the prefix remaining after `r` terminal arrows are removed. -/
def shrinkingPrefixObject
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V) (T : PathTwoOpenSubdivision q U V)
    (r : ℕ) (i : Fin (concatSegmentCount S T - r + 1)) : C :=
  D.obj ((concatSubdivision S T).point (shrinkingVertexEmbedding S T r i))

/-- Actual concatenated arrows transported to the endpoints of a shrinking
prefix. -/
def shrinkingPrefixArrow
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V) (T : PathTwoOpenSubdivision q U V)
    (r : ℕ) (i : Fin (concatSegmentCount S T - r)) :
    shrinkingPrefixObject D S T r i.castSucc ⟶
      shrinkingPrefixObject D S T r i.succ :=
  eqToHom (congrArg (fun k ↦ D.obj ((concatSubdivision S T).point k))
      (shrinkingEndpoint_castSucc S T r i)) ≫
    D.mappedPiece (concatSubdivision S T) (shrinkingSegmentEmbedding S T r i) ≫
    eqToHom (congrArg (fun k ↦ D.obj ((concatSubdivision S T).point k))
      (shrinkingEndpoint_succ S T r i)).symm

def shrinkingPrefixFold
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V) (T : PathTwoOpenSubdivision q U V)
    (r : ℕ) :
    shrinkingPrefixObject D S T r 0 ⟶
      shrinkingPrefixObject D S T r
        (Fin.last (concatSegmentCount S T - r)) :=
  TwoOpenDescentDatum.composeFin (shrinkingPrefixObject D S T r)
    (shrinkingPrefixArrow D S T r)

#print axioms shrinkingEndpoint_castSucc
#print axioms shrinkingEndpoint_succ

end ConstructionTargets.ConcatSubdivisionShrinkingFold
