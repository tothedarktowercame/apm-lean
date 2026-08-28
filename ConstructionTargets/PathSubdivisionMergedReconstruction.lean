import ConstructionTargets.PathSubdivisionRecursiveReconstruction
import ConstructionTargets.PathSubdivisionStructuralVertexEmbeddings

open Set
open scoped unitInterval
noncomputable section

namespace ConstructionTargets.PathSubdivisionMergedReconstruction

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.PathSubdivisionInsertionReachability
open ConstructionTargets.PathSubdivisionMultiplicityCommonVertices
open ConstructionTargets.PathSubdivisionStructuralVertexEmbeddings
open ConstructionTargets.EndpointPreservingFinEmbeddingDecomposition
open ConstructionTargets.PathSubdivisionRecursiveReconstruction

variable {X : Type*} [TopologicalSpace X]
variable {x y : X} {p : Path x y} {U V : Set X}
variable (S T : PathTwoOpenSubdivision p U V)

def leftMergedDecomposition :
    RemovalDecomposition S.n T.n (leftVertexEmbedding S T) :=
  removalDecomposition (leftVertexEmbedding S T)
    (leftVertexMap_zero S T) (leftVertexMap_last S T)

/-- Reconstruct the multiplicity-preserving merged vertex tuple from the left
source subdivision by genuine single-vertex insertions. -/
def leftMergedReconstruction : ReconstructionResult S T.n (mergedVertex S T) :=
  reconstruct S (mergedVertex S T) (monotone_mergedVertex S T)
    (leftVertexEmbedding S T) (mergedVertex_leftVertexEmbedding S T)
    (leftMergedDecomposition S T)

@[simp] theorem leftMergedReconstruction_size :
    (leftMergedReconstruction S T).subdivision.n = S.n + T.n :=
  (leftMergedReconstruction S T).size_eq

theorem leftMergedReconstruction_vertex
    (i : Fin ((leftMergedReconstruction S T).subdivision.n + 2)) :
    (leftMergedReconstruction S T).subdivision.vertex i =
      mergedVertex S T
        (Fin.cast (congrArg (fun r : ℕ ↦ r + 2)
          (leftMergedReconstruction S T).size_eq) i) :=
  (leftMergedReconstruction S T).vertex_eq i

theorem leftMergedReconstruction_reachable :
    InsertionReachable S (leftMergedReconstruction S T).subdivision :=
  (leftMergedReconstruction S T).reachable

/-- The right reconstruction uses the arithmetically reordered target index
type required by `ReconstructionResult T S.n`. -/
def rightMergedTargetVertex : Fin (T.n + S.n + 2) → unitInterval :=
  fun i ↦ mergedVertex S T (Fin.cast (by omega) i)

theorem monotone_rightMergedTargetVertex : Monotone (rightMergedTargetVertex S T) := by
  intro i j hij
  exact monotone_mergedVertex S T (Fin.mk_le_mk.mpr hij)

def rightMergedEmbedding : Fin (T.n + 2) ↪o Fin (T.n + S.n + 2) :=
  (rightVertexEmbedding S T).trans
    (Fin.castOrderIso (by omega)).toOrderEmbedding

@[simp] theorem rightMergedEmbedding_apply (i : Fin (T.n + 2)) :
    rightMergedEmbedding S T i = Fin.cast (by omega) (rightVertexEmbedding S T i) := rfl

@[simp] theorem rightMergedTargetVertex_recovery (i : Fin (T.n + 2)) :
    rightMergedTargetVertex S T (rightMergedEmbedding S T i) = T.vertex i := by
  change mergedVertex S T
    (Fin.cast (by omega) (Fin.cast (by omega) (rightVertexEmbedding S T i))) = _
  rw [show Fin.cast (by omega)
      (Fin.cast (by omega) (rightVertexEmbedding S T i)) =
        rightVertexEmbedding S T i by apply Fin.ext; rfl]
  exact mergedVertex_rightVertexEmbedding S T i

@[simp] theorem rightMergedEmbedding_zero : rightMergedEmbedding S T 0 = 0 := by
  apply Fin.ext
  rfl

@[simp] theorem rightMergedEmbedding_last :
    rightMergedEmbedding S T (Fin.last (T.n + 1)) = Fin.last (T.n + S.n + 1) := by
  apply Fin.ext
  simp [rightMergedEmbedding]

def rightMergedDecomposition :
    RemovalDecomposition T.n S.n (rightMergedEmbedding S T) :=
  removalDecomposition (rightMergedEmbedding S T)
    (rightMergedEmbedding_zero S T) (rightMergedEmbedding_last S T)

/-- Right-source reconstruction, over the reordered but order-isomorphic
finite coordinate type. -/
def rightMergedReconstruction :
    ReconstructionResult T S.n (rightMergedTargetVertex S T) :=
  reconstruct T (rightMergedTargetVertex S T) (monotone_rightMergedTargetVertex S T)
    (rightMergedEmbedding S T) (rightMergedTargetVertex_recovery S T)
    (rightMergedDecomposition S T)

@[simp] theorem rightMergedReconstruction_size :
    (rightMergedReconstruction S T).subdivision.n = T.n + S.n :=
  (rightMergedReconstruction S T).size_eq

theorem rightMergedReconstruction_size_common :
    (rightMergedReconstruction S T).subdivision.n = S.n + T.n := by
  rw [rightMergedReconstruction_size]
  omega

theorem rightMergedReconstruction_vertex
    (i : Fin ((rightMergedReconstruction S T).subdivision.n + 2)) :
    (rightMergedReconstruction S T).subdivision.vertex i =
      mergedVertex S T
        (Fin.cast (congrArg (fun r : ℕ ↦ r + 2)
          (rightMergedReconstruction_size_common S T)) i) := by
  rw [(rightMergedReconstruction S T).vertex_eq]
  rfl

theorem rightMergedReconstruction_reachable :
    InsertionReachable T (rightMergedReconstruction S T).subdivision :=
  (rightMergedReconstruction S T).reachable

#print axioms leftMergedReconstruction
#print axioms leftMergedReconstruction_vertex
#print axioms leftMergedReconstruction_reachable
#print axioms rightMergedEmbedding
#print axioms rightMergedReconstruction
#print axioms rightMergedReconstruction_size_common
#print axioms rightMergedReconstruction_vertex
#print axioms rightMergedReconstruction_reachable

end ConstructionTargets.PathSubdivisionMergedReconstruction
