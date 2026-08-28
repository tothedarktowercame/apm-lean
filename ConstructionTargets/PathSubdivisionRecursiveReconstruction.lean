import ConstructionTargets.PathSubdivisionRemovalReconstruction

/-!
# Recursive subdivision reconstruction
-/

open Set
open scoped unitInterval
noncomputable section

namespace ConstructionTargets.PathSubdivisionRecursiveReconstruction

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenInsertion
open ConstructionTargets.EndpointPreservingFinEmbeddingRemoval
open ConstructionTargets.EndpointPreservingFinEmbeddingDecomposition
open ConstructionTargets.PathSubdivisionInsertionReachability
open ConstructionTargets.PathSubdivisionRemovalReconstruction

variable {X : Type*} [TopologicalSpace X]
variable {x y : X} {p : Path x y} {U V : Set X}

theorem succAbove_cast {a b : ℕ} (h : a = b)
    (j : Fin (b + 1)) (i : Fin a) :
    j.succAbove (Fin.cast h i) =
      Fin.cast (congrArg (fun r : ℕ ↦ r + 1) h)
        ((Fin.cast (congrArg (fun r : ℕ ↦ r + 1) h).symm j).succAbove i) := by
  subst b
  rfl

/-- A reconstructed subdivision, with its size and target vertex coordinates
kept as explicit fields rather than hidden in structure equality. -/
structure ReconstructionResult
    (S : PathTwoOpenSubdivision p U V) (m : ℕ)
    (targetVertex : Fin (S.n + m + 2) → unitInterval) where
  subdivision : PathTwoOpenSubdivision p U V
  size_eq : subdivision.n = S.n + m
  vertex_eq : ∀ i : Fin (subdivision.n + 2),
    subdivision.vertex i =
      targetVertex (Fin.cast (congrArg (fun r : ℕ ↦ r + 2) size_eq) i)
  reachable : InsertionReachable S subdivision

/-- Recursively reinsert the complementary coordinates retained by a
`RemovalDecomposition`. -/
def reconstruct
    (S : PathTwoOpenSubdivision p U V)
    {m : ℕ}
    (targetVertex : Fin (S.n + m + 2) → unitInterval)
    (monotone_targetVertex : Monotone targetVertex)
    (e : Fin (S.n + 2) ↪o Fin (S.n + m + 2))
    (recovery : ∀ i, targetVertex (e i) = S.vertex i)
    (d : RemovalDecomposition S.n m e) :
    ReconstructionResult S m targetVertex := by
  induction d with
  | base =>
      exact
        { subdivision := S
          size_eq := by omega
          vertex_eq := by
            intro i
            simpa [finIdEmbedding] using (recovery i).symm
          reachable := .refl S }
  | @step k s tail ih =>
      let smallerTarget : Fin (S.n + k + 2) → unitInterval :=
        fun i ↦ targetVertex (s.removed.succAbove i)
      have hmono : Monotone smallerTarget :=
        monotone_targetVertex.comp (Fin.succAboveOrderEmb s.removed).monotone
      have hrecovery : ∀ i, smallerTarget (s.smaller i) = S.vertex i := by
        intro i
        change targetVertex (s.removed.succAbove (s.smaller i)) = S.vertex i
        rw [s.reinsert_smaller]
        exact recovery i
      let recResult := ih smallerTarget hmono hrecovery
      let deleted : DeletedVertexPresentation recResult.subdivision :=
        { targetVertex := fun i ↦ targetVertex
              (Fin.cast (by rw [recResult.size_eq]; omega) i)
          monotone_targetVertex := by
            intro i j hij
            exact monotone_targetVertex (Fin.mk_le_mk.mpr hij)
          removed := Fin.cast (by rw [recResult.size_eq]) s.removed
          removed_ne_zero := by
            intro h
            apply s.removed_ne_zero
            apply Fin.ext
            simpa using congrArg Fin.val h
          removed_ne_last := by
            intro h
            apply s.removed_ne_last
            apply Fin.ext
            have hv := congrArg Fin.val h
            simp only [Fin.val_last] at hv
            change s.removed.val = recResult.subdivision.n + 2 at hv
            change s.removed.val = S.n + k + 2
            exact hv.trans (congrArg (fun r : ℕ ↦ r + 2) recResult.size_eq)
          current_vertex := by
            intro i
            rw [recResult.vertex_eq]
            apply congrArg targetVertex
            exact succAbove_cast
              (congrArg (fun r : ℕ ↦ r + 2) recResult.size_eq) s.removed i }
      exact
        { subdivision := deleted.insertion.refined
          size_eq := by rw [PathTwoOpenSubdivision.SingleVertexInsertion.refined_n,
              recResult.size_eq]; omega
          vertex_eq := by
            intro i
            rw [deleted.refined_vertex_eq_target]
            apply congrArg targetVertex
            rfl
          reachable := recResult.reachable.trans deleted.reachable_refined }

#print axioms succAbove_cast
#print axioms ReconstructionResult
#print axioms reconstruct

end ConstructionTargets.PathSubdivisionRecursiveReconstruction
