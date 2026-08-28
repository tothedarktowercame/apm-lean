import ConstructionTargets.PathSubdivisionStructuralVertexEmbeddings
import Mathlib.Order.Fin.SuccAboveOrderIso

open Set
noncomputable section

namespace ConstructionTargets.EndpointPreservingFinEmbeddingRemoval

/-- Remove a point outside the range of an order embedding.  The resulting
embedding uses the unique coordinates whose `succAbove j` images are the old
coordinates. -/
def removeComplementEmbedding {a b : ℕ} (e : Fin a ↪o Fin (b + 2))
    (j : Fin (b + 2)) (hj : j ∉ Set.range e) : Fin a ↪o Fin (b + 1) :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ (Fin.succAboveOrderIso j).symm
      ⟨e i, by
        simp only [Finset.mem_compl, Finset.mem_singleton]
        exact fun h ↦ hj ⟨i, h⟩⟩)
    (fun _ _ h ↦ (Fin.succAboveOrderIso j).symm.strictMono
      (by simpa using e.strictMono h))

@[simp] theorem succAbove_removeComplementEmbedding {a b : ℕ}
    (e : Fin a ↪o Fin (b + 2)) (j : Fin (b + 2))
    (hj : j ∉ Set.range e) (i : Fin a) :
    j.succAbove (removeComplementEmbedding e j hj i) = e i := by
  change ((Fin.succAboveOrderIso j)
    ((Fin.succAboveOrderIso j).symm ⟨e i, _⟩)).1 = e i
  simp

theorem removeComplementEmbedding_zero {n k : ℕ}
    (e : Fin (n + 2) ↪o Fin (n + k + 3))
    (hzero : e 0 = 0)
    (j : Fin (n + k + 3)) (hj : j ∉ Set.range e) :
    removeComplementEmbedding e j hj 0 = 0 := by
  apply (Fin.succAboveOrderEmb j).injective
  change j.succAbove (removeComplementEmbedding e j hj 0) = j.succAbove 0
  rw [succAbove_removeComplementEmbedding, hzero]
  have hj0 : j ≠ 0 := by
    intro h
    apply hj
    exact ⟨0, hzero.trans h.symm⟩
  simpa using (Fin.succAbove_ne_zero_zero hj0).symm

theorem removeComplementEmbedding_last {n k : ℕ}
    (e : Fin (n + 2) ↪o Fin (n + k + 3))
    (hlast : e (Fin.last (n + 1)) = Fin.last (n + k + 2))
    (j : Fin (n + k + 3)) (hj : j ∉ Set.range e) :
    removeComplementEmbedding e j hj (Fin.last (n + 1)) = Fin.last (n + k + 1) := by
  apply (Fin.succAboveOrderEmb j).injective
  change j.succAbove (removeComplementEmbedding e j hj (Fin.last (n + 1))) =
    j.succAbove (Fin.last (n + k + 1))
  rw [succAbove_removeComplementEmbedding, hlast]
  have hjlast : j ≠ Fin.last (n + k + 2) := by
    intro h
    apply hj
    exact ⟨Fin.last (n + 1), hlast.trans h.symm⟩
  simpa using (Fin.succAbove_ne_last_last hjlast).symm

theorem range_succAbove_removeComplementEmbedding {a b : ℕ}
    (e : Fin a ↪o Fin (b + 2)) (j : Fin (b + 2))
    (hj : j ∉ Set.range e) :
    Set.range (fun i ↦ j.succAbove (removeComplementEmbedding e j hj i)) =
      Set.range e := by
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, (succAbove_removeComplementEmbedding e j hj i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, succAbove_removeComplementEmbedding e j hj i⟩

theorem range_succAbove_union_removed {b : ℕ} (j : Fin (b + 1)) :
    Set.range j.succAbove ∪ {j} = Set.univ := by
  rw [Fin.range_succAbove]
  exact Set.compl_union_self {j}

/-- The position immediately before a removed nonzero point.  If the point is
also not last, its reinsertion lies strictly between the two adjacent images
of this pivot. -/
def removalPivot {b : ℕ} (j : Fin (b + 1)) (hj0 : j ≠ 0) : Fin b := j.pred hj0

theorem succAbove_removalPivot_left {b : ℕ} (j : Fin (b + 1))
    (hj0 : j ≠ 0) :
    j.succAbove (removalPivot j hj0) = (removalPivot j hj0).castSucc := by
  exact Fin.succAbove_pred_self j hj0

theorem removalPivot_left_lt_removed {b : ℕ} (j : Fin (b + 1))
    (hj0 : j ≠ 0) :
    j.succAbove (removalPivot j hj0) < j := by
  rw [succAbove_removalPivot_left]
  apply Fin.mk_lt_mk.mpr
  have hpred := congrArg Fin.val (Fin.succ_pred j hj0)
  simp only [Fin.val_succ] at hpred
  simp only [removalPivot, Fin.val_pred]
  omega

def removalPivotNext {b : ℕ} (j : Fin (b + 1))
    (hjlast : j ≠ Fin.last b) : Fin b :=
  ⟨j.val, by
    have := j.isLt
    have hne : j.val ≠ b := by
      intro h
      apply hjlast
      ext
      simpa using h
    omega⟩

theorem removed_lt_succAbove_removalPivot_succ {b : ℕ} (j : Fin (b + 1))
    (hjlast : j ≠ Fin.last b) :
    j < j.succAbove (removalPivotNext j hjlast) := by
  rw [Fin.succAbove_of_le_castSucc]
  · apply Fin.mk_lt_mk.mpr
    simp
  · apply Fin.mk_le_mk.mpr
    simp [removalPivotNext]

/-- One recursive removal step for an endpoint-preserving embedding. -/
structure EndpointRemovalStep (n k : ℕ) where
  original : Fin (n + 2) ↪o Fin (n + k + 3)
  removed : Fin (n + k + 3)
  removed_not_mem : removed ∉ Set.range original
  original_zero : original 0 = 0
  original_last : original (Fin.last (n + 1)) = Fin.last (n + k + 2)

namespace EndpointRemovalStep

variable {n k : ℕ}

def smaller (s : EndpointRemovalStep n k) : Fin (n + 2) ↪o Fin (n + k + 2) :=
  removeComplementEmbedding s.original s.removed s.removed_not_mem

@[simp] theorem reinsert_smaller (s : EndpointRemovalStep n k) (i : Fin (n + 2)) :
    s.removed.succAbove (s.smaller i) = s.original i :=
  succAbove_removeComplementEmbedding _ _ _ _

@[simp] theorem smaller_zero (s : EndpointRemovalStep n k) : s.smaller 0 = 0 :=
  removeComplementEmbedding_zero _ s.original_zero _ s.removed_not_mem

@[simp] theorem smaller_last (s : EndpointRemovalStep n k) :
    s.smaller (Fin.last (n + 1)) = Fin.last (n + k + 1) :=
  removeComplementEmbedding_last _ s.original_last _ s.removed_not_mem

theorem range_reinsert_smaller (s : EndpointRemovalStep n k) :
    Set.range (fun i ↦ s.removed.succAbove (s.smaller i)) = Set.range s.original :=
  range_succAbove_removeComplementEmbedding _ _ _

theorem range_reinsert_smaller_union_removed (s : EndpointRemovalStep n k) :
    Set.range (fun i ↦ s.removed.succAbove (s.smaller i)) ∪ {s.removed} =
      Set.range s.original ∪ {s.removed} := by
  rw [s.range_reinsert_smaller]

theorem removed_ne_zero (s : EndpointRemovalStep n k) : s.removed ≠ 0 := by
  intro h
  apply s.removed_not_mem
  exact ⟨0, s.original_zero.trans h.symm⟩

theorem removed_ne_last (s : EndpointRemovalStep n k) :
    s.removed ≠ Fin.last (n + k + 2) := by
  intro h
  apply s.removed_not_mem
  exact ⟨Fin.last (n + 1), s.original_last.trans h.symm⟩

def pivot (s : EndpointRemovalStep n k) : Fin (n + k + 2) :=
  removalPivot s.removed s.removed_ne_zero

theorem pivot_left_lt_removed (s : EndpointRemovalStep n k) :
    s.removed.succAbove s.pivot < s.removed :=
  removalPivot_left_lt_removed _ _

theorem removed_lt_pivot_succ (s : EndpointRemovalStep n k) :
    s.removed < s.removed.succAbove (removalPivotNext s.removed s.removed_ne_last) :=
  removed_lt_succAbove_removalPivot_succ _ s.removed_ne_last

end EndpointRemovalStep

#print axioms removeComplementEmbedding
#print axioms succAbove_removeComplementEmbedding
#print axioms removeComplementEmbedding_zero
#print axioms removeComplementEmbedding_last
#print axioms range_succAbove_removeComplementEmbedding
#print axioms EndpointRemovalStep.smaller
#print axioms EndpointRemovalStep.smaller_zero
#print axioms EndpointRemovalStep.smaller_last
#print axioms EndpointRemovalStep.range_reinsert_smaller_union_removed
#print axioms EndpointRemovalStep.pivot_left_lt_removed
#print axioms EndpointRemovalStep.removed_lt_pivot_succ

end ConstructionTargets.EndpointPreservingFinEmbeddingRemoval
