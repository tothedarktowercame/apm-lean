import ConstructionTargets.ComposeFinArbitrarySplit
import ConstructionTargets.PathSubdivisionConcatenation

/-!
# Structural right suffix of a concatenated subdivision
-/

open CategoryTheory
noncomputable section

namespace ConstructionTargets.ConcatSubdivisionRightSuffix

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.PathSubdivisionConcatenation

variable {X : Type*} [TopologicalSpace X]
variable {x y z : X} {p : Path x y} {q : Path y z} {U V : Set X}

/-- Vertices of the right block inside the concatenated subdivision.  Zero is
the shared midpoint; a successor is the target of the corresponding right
segment. -/
def rightBlockVertex (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    Fin (T.n + 2) → Fin ((concatSubdivision S T).n + 2) :=
  Fin.cases (rightSegment S T 0).castSucc
    (fun j ↦ (rightSegment S T j).succ)

@[simp] theorem rightBlockVertex_zero
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    rightBlockVertex S T 0 = (rightSegment S T 0).castSucc := rfl

@[simp] theorem rightBlockVertex_succ
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (j : Fin (T.n + 1)) :
    rightBlockVertex S T j.succ = (rightSegment S T j).succ := rfl

/-- The structural right-block vertex immediately before segment `j` is its
actual source index. -/
theorem rightBlockVertex_castSucc
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (j : Fin (T.n + 1)) :
    rightBlockVertex S T j.castSucc = (rightSegment S T j).castSucc := by
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · rfl
  · apply Fin.ext
    rfl

theorem rightBlockVertex_point
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (j : Fin (T.n + 2)) :
    (concatSubdivision S T).point (rightBlockVertex S T j) = T.point j := by
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · exact rightSegment_point_castSucc S T 0
  · exact rightSegment_point_succ S T k

/-- Both endpoints of every right segment are recovered by the right-block
vertex map, without rewriting a dependent arrow family. -/
theorem rightBlockSegment_endpoints
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (j : Fin (T.n + 1)) :
    rightBlockVertex S T j.castSucc = (rightSegment S T j).castSucc ∧
      rightBlockVertex S T j.succ = (rightSegment S T j).succ :=
  ⟨rightBlockVertex_castSucc S T j, rightBlockVertex_succ S T j⟩

#print axioms rightBlockVertex_castSucc
#print axioms rightBlockVertex_point
#print axioms rightBlockSegment_endpoints

end ConstructionTargets.ConcatSubdivisionRightSuffix
