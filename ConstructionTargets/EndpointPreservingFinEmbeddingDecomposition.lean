import ConstructionTargets.EndpointPreservingFinEmbeddingRemoval
import ConstructionTargets.FinOrderEmbeddingComplement

/-!
# Recursive removal decomposition of endpoint-preserving finite embeddings
-/

open Set
noncomputable section

namespace ConstructionTargets.EndpointPreservingFinEmbeddingDecomposition

open ConstructionTargets.EndpointPreservingFinEmbeddingRemoval
open ConstructionTargets.FinOrderEmbeddingComplement

theorem removalPivotNext_eq_pivot_succ {n k : ℕ}
    (s : EndpointRemovalStep n k) :
    (removalPivotNext s.removed s.removed_ne_last).castSucc = s.pivot.succ := by
  apply Fin.ext
  simp [EndpointRemovalStep.pivot, removalPivotNext, removalPivot]

theorem reinsert_pivot_left {n k : ℕ} (s : EndpointRemovalStep n k) :
    s.removed.succAbove s.pivot = s.pivot.castSucc :=
  succAbove_removalPivot_left _ _

def finIdEmbedding (r : ℕ) : Fin r ↪o Fin r :=
  OrderEmbedding.ofStrictMono id strictMono_id

/-- Proof-carrying recursive deletion of every complementary index.  Each
successor node retains the removed target coordinate and its literal
`succAbove` reconstruction through `EndpointRemovalStep.reinsert_smaller`. -/
inductive RemovalDecomposition (n : ℕ) :
    (m : ℕ) → (Fin (n + 2) ↪o Fin (n + m + 2)) → Type
  | base : RemovalDecomposition n 0 (finIdEmbedding (n + 2))
  | step {k : ℕ} (s : EndpointRemovalStep n k)
      (tail : RemovalDecomposition n k s.smaller) :
      RemovalDecomposition n (k + 1) s.original

theorem selfEmbedding_eq_refl {n : ℕ} (e : Fin (n + 2) ↪o Fin (n + 2)) :
    e = finIdEmbedding (n + 2) := by
  ext i
  apply le_antisymm
  · exact e.strictMono.apply_le
  · exact e.strictMono.le_apply

/-- Every endpoint-preserving finite embedding admits the recursive removal
decomposition. -/
def removalDecomposition
    {n m : ℕ}
    (e : Fin (n + 2) ↪o Fin (n + m + 2))
    (hzero : e 0 = 0)
    (hlast : e (Fin.last (n + 1)) = Fin.last (n + m + 1)) :
    RemovalDecomposition n m e := by
  induction m with
  | zero =>
      rw [selfEmbedding_eq_refl e]
      exact .base
  | succ k ih =>
      have hc : (complement e).Nonempty := by
        apply Finset.card_pos.mp
        rw [card_complement]
        omega
      let j : Fin (n + k + 3) := Classical.choose hc
      have hj : j ∉ Set.range e :=
        (mem_complement_iff e j).mp (Classical.choose_spec hc)
      let s : EndpointRemovalStep n k :=
        { original := e
          removed := j
          removed_not_mem := hj
          original_zero := hzero
          original_last := hlast }
      exact .step s (ih s.smaller s.smaller_zero s.smaller_last)

#print axioms removalPivotNext_eq_pivot_succ
#print axioms reinsert_pivot_left
#print axioms selfEmbedding_eq_refl
#print axioms removalDecomposition

end ConstructionTargets.EndpointPreservingFinEmbeddingDecomposition
