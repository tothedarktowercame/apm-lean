import ConstructionTargets.PathSubdivisionOccurrenceEmbeddings

open Set
open scoped unitInterval
noncomputable section

namespace ConstructionTargets.PathSubdivisionStructuralVertexEmbeddings

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.PathSubdivisionMultiplicityCommonVertices
open ConstructionTargets.PathSubdivisionOccurrenceEmbeddings

variable {X : Type*} [TopologicalSpace X]
variable {x y : X} {p : Path x y} {U V : Set X}
variable (S T : PathTwoOpenSubdivision p U V)

/-- Extend the left occurrence embedding by explicit structural endpoints. -/
def leftVertexMap : Fin (S.n + 2) → Fin (S.n + T.n + 2) :=
  Fin.cases 0 (fun k ↦ Fin.lastCases (Fin.last (S.n + T.n + 1))
    (fun i ↦ ⟨(leftInternalEmbedding S T i).val + 1, by
      have := (leftInternalEmbedding S T i).isLt
      omega⟩) k)

@[simp] theorem leftVertexMap_zero : leftVertexMap S T 0 = 0 := rfl

@[simp] theorem leftVertexMap_internal (i : Fin S.n) :
    leftVertexMap S T i.succ.castSucc =
      ⟨(leftInternalEmbedding S T i).val + 1, by
        have := (leftInternalEmbedding S T i).isLt
        omega⟩ := by simp [leftVertexMap]

@[simp] theorem leftVertexMap_last :
    leftVertexMap S T (Fin.last (S.n + 1)) = Fin.last (S.n + T.n + 1) := by
  simp [leftVertexMap, ← Fin.succ_last]

/-- Right-source analogue of `leftVertexMap`. -/
def rightVertexMap : Fin (T.n + 2) → Fin (S.n + T.n + 2) :=
  Fin.cases 0 (fun k ↦ Fin.lastCases (Fin.last (S.n + T.n + 1))
    (fun i ↦ ⟨(rightInternalEmbedding S T i).val + 1, by
      have := (rightInternalEmbedding S T i).isLt
      omega⟩) k)

@[simp] theorem rightVertexMap_zero : rightVertexMap S T 0 = 0 := rfl

@[simp] theorem rightVertexMap_internal (i : Fin T.n) :
    rightVertexMap S T i.succ.castSucc =
      ⟨(rightInternalEmbedding S T i).val + 1, by
        have := (rightInternalEmbedding S T i).isLt
        omega⟩ := by simp [rightVertexMap]

@[simp] theorem rightVertexMap_last :
    rightVertexMap S T (Fin.last (T.n + 1)) = Fin.last (S.n + T.n + 1) := by
  simp [rightVertexMap, ← Fin.succ_last]

theorem mergedVertex_leftVertexMap_internal (i : Fin S.n) :
    mergedVertex S T (leftVertexMap S T i.succ.castSucc) =
      S.vertex i.succ.castSucc := by
  simpa [leftVertexMap, mergedVertex, mergedVertices] using
    mergedInternalVertices_get_left S T i

theorem mergedVertex_rightVertexMap_internal (i : Fin T.n) :
    mergedVertex S T (rightVertexMap S T i.succ.castSucc) =
      T.vertex i.succ.castSucc := by
  simpa [rightVertexMap, mergedVertex, mergedVertices] using
    mergedInternalVertices_get_right S T i

@[simp] theorem mergedVertex_leftVertexMap_zero :
    mergedVertex S T (leftVertexMap S T 0) = S.vertex 0 := by
  rw [leftVertexMap_zero, mergedVertex_zero, S.vertex_zero]

@[simp] theorem mergedVertex_leftVertexMap_last :
    mergedVertex S T (leftVertexMap S T (Fin.last (S.n + 1))) =
      S.vertex (Fin.last (S.n + 1)) := by
  rw [leftVertexMap_last, mergedVertex_last, S.vertex_last]

@[simp] theorem mergedVertex_rightVertexMap_zero :
    mergedVertex S T (rightVertexMap S T 0) = T.vertex 0 := by
  rw [rightVertexMap_zero, mergedVertex_zero, T.vertex_zero]

@[simp] theorem mergedVertex_rightVertexMap_last :
    mergedVertex S T (rightVertexMap S T (Fin.last (T.n + 1))) =
      T.vertex (Fin.last (T.n + 1)) := by
  rw [rightVertexMap_last, mergedVertex_last, T.vertex_last]

#print axioms leftVertexMap
#print axioms rightVertexMap
#print axioms mergedVertex_leftVertexMap_internal
#print axioms mergedVertex_rightVertexMap_internal

end ConstructionTargets.PathSubdivisionStructuralVertexEmbeddings
