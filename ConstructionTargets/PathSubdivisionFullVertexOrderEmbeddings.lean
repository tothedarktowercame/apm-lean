import ConstructionTargets.PathSubdivisionStructuralVertexEmbeddings

/-!
# Full occurrence-sensitive subdivision order embeddings
-/

open Set
open scoped unitInterval
noncomputable section

namespace ConstructionTargets.PathSubdivisionFullVertexOrderEmbeddings

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.PathSubdivisionMultiplicityCommonVertices
open ConstructionTargets.PathSubdivisionOccurrenceEmbeddings
open ConstructionTargets.PathSubdivisionStructuralVertexEmbeddings

variable {X : Type*} [TopologicalSpace X]
variable {x y : X} {p : Path x y} {U V : Set X}
variable (S T : PathTwoOpenSubdivision p U V)

theorem leftVertexMap_succ_pos (k : Fin (S.n + 1)) :
    0 < leftVertexMap S T k.succ := by
  change 0 < (leftVertexMap S T k.succ).val
  refine Fin.lastCases ?_ (fun i ↦ ?_) k
  · rw [Fin.succ_last, leftVertexMap_last]
    exact Fin.last_pos
  · rw [show i.castSucc.succ = i.succ.castSucc by apply Fin.ext; rfl,
      leftVertexMap_internal]
    exact Nat.zero_lt_succ _

theorem rightVertexMap_succ_pos (k : Fin (T.n + 1)) :
    0 < rightVertexMap S T k.succ := by
  change 0 < (rightVertexMap S T k.succ).val
  refine Fin.lastCases ?_ (fun i ↦ ?_) k
  · rw [Fin.succ_last, rightVertexMap_last]
    exact Fin.last_pos
  · rw [show i.castSucc.succ = i.succ.castSucc by apply Fin.ext; rfl,
      rightVertexMap_internal]
    exact Nat.zero_lt_succ _

theorem leftVertexMap_internal_lt_last (i : Fin S.n) :
    leftVertexMap S T i.succ.castSucc < Fin.last (S.n + T.n + 1) := by
  rw [leftVertexMap_internal]
  apply Fin.mk_lt_mk.mpr
  have hi := (leftInternalEmbedding S T i).isLt
  omega

theorem rightVertexMap_internal_lt_last (i : Fin T.n) :
    rightVertexMap S T i.succ.castSucc < Fin.last (S.n + T.n + 1) := by
  rw [rightVertexMap_internal]
  apply Fin.mk_lt_mk.mpr
  have hi := (rightInternalEmbedding S T i).isLt
  omega

theorem mergedVertex_leftVertexMap (i : Fin (S.n + 2)) :
    mergedVertex S T (leftVertexMap S T i) = S.vertex i := by
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · exact mergedVertex_leftVertexMap_zero S T
  · refine Fin.lastCases ?_ (fun j ↦ ?_) k
    · simpa [← Fin.succ_last] using mergedVertex_leftVertexMap_last S T
    · exact mergedVertex_leftVertexMap_internal S T j

theorem mergedVertex_rightVertexMap (i : Fin (T.n + 2)) :
    mergedVertex S T (rightVertexMap S T i) = T.vertex i := by
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · exact mergedVertex_rightVertexMap_zero S T
  · refine Fin.lastCases ?_ (fun j ↦ ?_) k
    · simpa [← Fin.succ_last] using mergedVertex_rightVertexMap_last S T
    · exact mergedVertex_rightVertexMap_internal S T j

#print axioms leftVertexMap_succ_pos
#print axioms rightVertexMap_succ_pos
#print axioms leftVertexMap_internal_lt_last
#print axioms rightVertexMap_internal_lt_last
#print axioms mergedVertex_leftVertexMap
#print axioms mergedVertex_rightVertexMap

end ConstructionTargets.PathSubdivisionFullVertexOrderEmbeddings
