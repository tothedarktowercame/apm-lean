import ConstructionTargets.PathSubdivisionOccurrenceEmbeddings

open Set
open scoped unitInterval
noncomputable section

namespace ConstructionTargets.PathSubdivisionStructuralVertexEmbeddings

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.PathSubdivisionMultiplicityCommonVertices
open ConstructionTargets.PathSubdivisionOccurrenceEmbeddings

/-- Add a distinguished first and last point to an order embedding of finite
linear orders. -/
def endpointExtend {n m : ℕ} (e : Fin n ↪o Fin m) : Fin (n + 2) → Fin (m + 2) :=
  Fin.cases 0 (fun k ↦ Fin.lastCases (Fin.last (m + 1))
    (fun i ↦ ⟨(e i).val + 1, by have := (e i).isLt; omega⟩) k)

@[simp] theorem endpointExtend_zero {n m : ℕ} (e : Fin n ↪o Fin m) :
    endpointExtend e 0 = 0 := rfl

@[simp] theorem endpointExtend_internal {n m : ℕ} (e : Fin n ↪o Fin m)
    (i : Fin n) :
    endpointExtend e i.succ.castSucc =
      ⟨(e i).val + 1, by have := (e i).isLt; omega⟩ := by
  simp [endpointExtend]

@[simp] theorem endpointExtend_internal' {n m : ℕ} (e : Fin n ↪o Fin m)
    (i : Fin n) :
    endpointExtend e i.castSucc.succ =
      ⟨(e i).val + 1, by have := (e i).isLt; omega⟩ := by
  rw [Fin.succ_castSucc]
  exact endpointExtend_internal e i

@[simp] theorem endpointExtend_last {n m : ℕ} (e : Fin n ↪o Fin m) :
    endpointExtend e (Fin.last (n + 1)) = Fin.last (m + 1) := by
  simp [endpointExtend, ← Fin.succ_last]

theorem endpointExtend_strictMono {n m : ℕ} (e : Fin n ↪o Fin m) :
    StrictMono (endpointExtend e) := by
  rw [Fin.strictMono_iff_lt_succ]
  induction n with
  | zero =>
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rw [show (0 : Fin 1).castSucc = (0 : Fin 2) by rfl,
        show (0 : Fin 1).succ = Fin.last 1 by ext; rfl,
        endpointExtend_zero, endpointExtend_last]
      exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ m)
  | succ n =>
      intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · rw [show (0 : Fin (n + 2)).castSucc = (0 : Fin (n + 3)) by rfl,
          show (0 : Fin (n + 2)).succ =
            (0 : Fin (n + 1)).castSucc.succ by rfl,
          endpointExtend_zero, endpointExtend_internal']
        exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
      · refine Fin.lastCases ?_ (fun k ↦ ?_) j
        · rw [show (Fin.last n).succ.castSucc =
              (Fin.last n : Fin (n + 1)).castSucc.succ by rfl,
            show (Fin.last n).succ.succ = Fin.last (n + 2) by ext; rfl]
          rw [endpointExtend_internal', endpointExtend_last]
          apply Fin.mk_lt_mk.mpr
          have h := (e (Fin.last n)).isLt
          omega
        · rw [show k.castSucc.succ.castSucc = k.castSucc.castSucc.succ by
              ext; rfl,
            show k.castSucc.succ.succ = k.succ.castSucc.succ by
              ext; rfl]
          simp only [endpointExtend_internal', Fin.mk_lt_mk]
          exact Nat.add_lt_add_right (e.strictMono k.castSucc_lt_succ) 1

def endpointExtendOrderEmbedding {n m : ℕ} (e : Fin n ↪o Fin m) :
    Fin (n + 2) ↪o Fin (m + 2) :=
  OrderEmbedding.ofStrictMono (endpointExtend e) (endpointExtend_strictMono e)

variable {X : Type*} [TopologicalSpace X]
variable {x y : X} {p : Path x y} {U V : Set X}
variable (S T : PathTwoOpenSubdivision p U V)

/-- Extend the left occurrence embedding by explicit structural endpoints. -/
def leftVertexMap : Fin (S.n + 2) → Fin (S.n + T.n + 2) :=
  endpointExtend (leftInternalEmbedding S T)

@[simp] theorem leftVertexMap_zero : leftVertexMap S T 0 = 0 := rfl

@[simp] theorem leftVertexMap_internal (i : Fin S.n) :
    leftVertexMap S T i.succ.castSucc =
      ⟨(leftInternalEmbedding S T i).val + 1, by
        have := (leftInternalEmbedding S T i).isLt
        omega⟩ := by simp [leftVertexMap]

@[simp] theorem leftVertexMap_last :
    leftVertexMap S T (Fin.last (S.n + 1)) = Fin.last (S.n + T.n + 1) := by
  rw [leftVertexMap, endpointExtend_last]

/-- Right-source analogue of `leftVertexMap`. -/
def rightVertexMap : Fin (T.n + 2) → Fin (S.n + T.n + 2) :=
  endpointExtend (rightInternalEmbedding S T)

@[simp] theorem rightVertexMap_zero : rightVertexMap S T 0 = 0 := rfl

@[simp] theorem rightVertexMap_internal (i : Fin T.n) :
    rightVertexMap S T i.succ.castSucc =
      ⟨(rightInternalEmbedding S T i).val + 1, by
        have := (rightInternalEmbedding S T i).isLt
        omega⟩ := by simp [rightVertexMap]

@[simp] theorem rightVertexMap_last :
    rightVertexMap S T (Fin.last (T.n + 1)) = Fin.last (S.n + T.n + 1) := by
  rw [rightVertexMap, endpointExtend_last]

theorem leftVertexMap_strictMono : StrictMono (leftVertexMap S T) :=
  endpointExtend_strictMono (leftInternalEmbedding S T)

theorem rightVertexMap_strictMono : StrictMono (rightVertexMap S T) :=
  endpointExtend_strictMono (rightInternalEmbedding S T)

def leftVertexEmbedding : Fin (S.n + 2) ↪o Fin (S.n + T.n + 2) :=
  endpointExtendOrderEmbedding (leftInternalEmbedding S T)

def rightVertexEmbedding : Fin (T.n + 2) ↪o Fin (S.n + T.n + 2) :=
  endpointExtendOrderEmbedding (rightInternalEmbedding S T)

@[simp] theorem leftVertexEmbedding_apply (i : Fin (S.n + 2)) :
    leftVertexEmbedding S T i = leftVertexMap S T i := rfl

@[simp] theorem rightVertexEmbedding_apply (i : Fin (T.n + 2)) :
    rightVertexEmbedding S T i = rightVertexMap S T i := rfl

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

@[simp] theorem mergedVertex_leftVertexEmbedding (i : Fin (S.n + 2)) :
    mergedVertex S T (leftVertexEmbedding S T i) = S.vertex i := by
  rw [leftVertexEmbedding_apply]
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact mergedVertex_leftVertexMap_zero S T
  · refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · exact mergedVertex_leftVertexMap_last S T
    · exact mergedVertex_leftVertexMap_internal S T k

@[simp] theorem mergedVertex_rightVertexEmbedding (i : Fin (T.n + 2)) :
    mergedVertex S T (rightVertexEmbedding S T i) = T.vertex i := by
  rw [rightVertexEmbedding_apply]
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact mergedVertex_rightVertexMap_zero S T
  · refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · exact mergedVertex_rightVertexMap_last S T
    · exact mergedVertex_rightVertexMap_internal S T k

#print axioms leftVertexMap
#print axioms rightVertexMap
#print axioms endpointExtend_strictMono
#print axioms leftVertexEmbedding
#print axioms rightVertexEmbedding
#print axioms mergedVertex_leftVertexMap_internal
#print axioms mergedVertex_rightVertexMap_internal
#print axioms mergedVertex_leftVertexEmbedding
#print axioms mergedVertex_rightVertexEmbedding

end ConstructionTargets.PathSubdivisionStructuralVertexEmbeddings
