import ConstructionTargets.EndpointPreservingFinEmbeddingDecomposition
import ConstructionTargets.PathSubdivisionInsertionReachability

open Set
open scoped unitInterval
noncomputable section

namespace ConstructionTargets.PathSubdivisionRemovalReconstruction

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenInsertion
open ConstructionTargets.EndpointPreservingFinEmbeddingRemoval
open ConstructionTargets.EndpointPreservingFinEmbeddingDecomposition
open ConstructionTargets.PathSubdivisionInsertionReachability
open PathTwoOpenSubdivision

variable {X : Type*} [TopologicalSpace X]
variable {x y : X} {p : Path x y} {U V : Set X}

/-- The subdivision segment immediately before a non-endpoint target vertex. -/
def reconstructionSegment {r : ℕ} (j : Fin (r + 3))
    (hj0 : j ≠ 0) (hjlast : j ≠ Fin.last (r + 2)) : Fin (r + 1) :=
  (removalPivot j hj0).castPred (by
    intro h
    apply hjlast
    have hs := congrArg Fin.succ h
    rw [show (removalPivot j hj0).succ = j by
      exact Fin.succ_pred j hj0] at hs
    simpa [← Fin.succ_last] using hs)

@[simp] theorem reconstructionSegment_castSucc {r : ℕ} (j : Fin (r + 3))
    (hj0 : j ≠ 0) (hjlast : j ≠ Fin.last (r + 2)) :
    (reconstructionSegment j hj0 hjlast).castSucc = removalPivot j hj0 := by
  exact Fin.castSucc_castPred _ _

@[simp] theorem reconstructionSegment_succ {r : ℕ} (j : Fin (r + 3))
    (hj0 : j ≠ 0) (hjlast : j ≠ Fin.last (r + 2)) :
    (reconstructionSegment j hj0 hjlast).succ = removalPivotNext j hjlast := by
  apply Fin.ext
  change (removalPivot j hj0).val + 1 = j.val
  have hpred := congrArg Fin.val (Fin.succ_pred j hj0)
  simp only [Fin.val_succ] at hpred
  simpa [removalPivot] using hpred

/-- Data saying that a current subdivision is obtained from a target vertex
sequence by deleting the coordinate `j`. -/
structure DeletedVertexPresentation (R : PathTwoOpenSubdivision p U V) where
  targetVertex : Fin (R.n + 3) → unitInterval
  monotone_targetVertex : Monotone targetVertex
  removed : Fin (R.n + 3)
  removed_ne_zero : removed ≠ 0
  removed_ne_last : removed ≠ Fin.last (R.n + 2)
  current_vertex : ∀ i, R.vertex i = targetVertex (removed.succAbove i)

namespace DeletedVertexPresentation

def insertion {R : PathTwoOpenSubdivision p U V}
    (d : DeletedVertexPresentation R) : PathTwoOpenSubdivision.SingleVertexInsertion R where
  segment := reconstructionSegment d.removed d.removed_ne_zero d.removed_ne_last
  parameter := d.targetVertex d.removed
  lower := by
    rw [d.current_vertex, reconstructionSegment_castSucc]
    exact d.monotone_targetVertex
      (le_of_lt (removalPivot_left_lt_removed d.removed d.removed_ne_zero))
  upper := by
    rw [d.current_vertex, reconstructionSegment_succ]
    exact d.monotone_targetVertex
      (le_of_lt (removed_lt_succAbove_removalPivot_succ d.removed d.removed_ne_last))

@[simp] theorem insertion_parameter {R : PathTwoOpenSubdivision p U V}
    (d : DeletedVertexPresentation R) :
    d.insertion.parameter = d.targetVertex d.removed := rfl

theorem refined_vertex_at {R : PathTwoOpenSubdivision p U V}
    (d : DeletedVertexPresentation R) :
    d.insertion.refined.vertex
      (insertedVertexPosition R d.insertion.segment) = d.targetVertex d.removed := by
  exact insertedVertex_at _ _ _

theorem refined_vertex_old {R : PathTwoOpenSubdivision p U V}
    (d : DeletedVertexPresentation R) (i : Fin (R.n + 2)) :
    d.insertion.refined.vertex
      ((insertedVertexPosition R d.insertion.segment).succAbove i) =
        d.targetVertex (d.removed.succAbove i) := by
  change insertedVertex R d.insertion.segment d.insertion.parameter
      ((insertedVertexPosition R d.insertion.segment).succAbove i) = _
  rw [insertedVertex_old, d.current_vertex]

theorem insertedVertexPosition_eq_removed {R : PathTwoOpenSubdivision p U V}
    (d : DeletedVertexPresentation R) :
    insertedVertexPosition R d.insertion.segment = d.removed := by
  apply Fin.ext
  change (removalPivot d.removed d.removed_ne_zero).val + 1 = d.removed.val
  have hpred := congrArg Fin.val (Fin.succ_pred d.removed d.removed_ne_zero)
  simp only [Fin.val_succ] at hpred
  simpa [removalPivot] using hpred

/-- Inserting the deleted coordinate reconstructs the entire target vertex
sequence pointwise. -/
theorem refined_vertex_eq_target {R : PathTwoOpenSubdivision p U V}
    (d : DeletedVertexPresentation R) (i : Fin (R.n + 3)) :
    d.insertion.refined.vertex i = d.targetVertex i := by
  by_cases hi : i = insertedVertexPosition R d.insertion.segment
  · subst i
    rw [d.refined_vertex_at, d.insertedVertexPosition_eq_removed]
  · obtain ⟨q, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [d.refined_vertex_old, d.insertedVertexPosition_eq_removed]

theorem reachable_refined {R : PathTwoOpenSubdivision p U V}
    (d : DeletedVertexPresentation R) :
    InsertionReachable R d.insertion.refined :=
  InsertionReachable.of_single d.insertion

end DeletedVertexPresentation

#print axioms reconstructionSegment_castSucc
#print axioms reconstructionSegment_succ
#print axioms DeletedVertexPresentation.insertion
#print axioms DeletedVertexPresentation.refined_vertex_eq_target
#print axioms DeletedVertexPresentation.reachable_refined

end ConstructionTargets.PathSubdivisionRemovalReconstruction
