import ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Max

/-!
# Common ordered vertices for two path subdivisions
-/

open Set
open scoped unitInterval

noncomputable section

namespace ConstructionTargets.PathSubdivisionCommonVertices

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision

variable {X : Type*} [TopologicalSpace X]
variable {x y : X} {p : Path x y} {U V : Set X}

variable (S T : PathTwoOpenSubdivision p U V)

/-- The deduplicated union of the two finite vertex sets. -/
def commonVertexSet : Finset unitInterval :=
  Finset.univ.image S.vertex ∪ Finset.univ.image T.vertex

theorem left_vertex_mem (i : Fin (S.n + 2)) :
    S.vertex i ∈ commonVertexSet S T := by
  simp [commonVertexSet]

theorem right_vertex_mem (i : Fin (T.n + 2)) :
    T.vertex i ∈ commonVertexSet S T := by
  simp [commonVertexSet]

theorem zero_mem : (0 : unitInterval) ∈ commonVertexSet S T := by
  rw [← S.vertex_zero]
  exact left_vertex_mem S T 0

theorem one_mem : (1 : unitInterval) ∈ commonVertexSet S T := by
  rw [← S.vertex_last]
  exact left_vertex_mem S T (Fin.last (S.n + 1))

/-- Canonical increasing enumeration of the union, with duplicates removed. -/
def commonVertexOrderIso :
    Fin (commonVertexSet S T).card ≃o commonVertexSet S T :=
  Finset.orderIsoOfFin (commonVertexSet S T) rfl

def commonVertex (i : Fin (commonVertexSet S T).card) : unitInterval :=
  (commonVertexOrderIso S T i).1

theorem monotone_commonVertex : Monotone (commonVertex S T) := by
  intro i j hij
  exact (commonVertexOrderIso S T).monotone hij

/-- Index of a vertex from the left subdivision in the common enumeration. -/
def locateLeft (i : Fin (S.n + 2)) : Fin (commonVertexSet S T).card :=
  (commonVertexOrderIso S T).symm ⟨S.vertex i, left_vertex_mem S T i⟩

/-- Index of a vertex from the right subdivision in the common enumeration. -/
def locateRight (i : Fin (T.n + 2)) : Fin (commonVertexSet S T).card :=
  (commonVertexOrderIso S T).symm ⟨T.vertex i, right_vertex_mem S T i⟩

@[simp] theorem commonVertex_locateLeft (i : Fin (S.n + 2)) :
    commonVertex S T (locateLeft S T i) = S.vertex i := by
  exact congrArg Subtype.val ((commonVertexOrderIso S T).apply_symm_apply
    ⟨S.vertex i, left_vertex_mem S T i⟩)

@[simp] theorem commonVertex_locateRight (i : Fin (T.n + 2)) :
    commonVertex S T (locateRight S T i) = T.vertex i := by
  exact congrArg Subtype.val ((commonVertexOrderIso S T).apply_symm_apply
    ⟨T.vertex i, right_vertex_mem S T i⟩)

theorem commonVertex_card_pos : 0 < (commonVertexSet S T).card :=
  Finset.card_pos.mpr ⟨0, zero_mem S T⟩

theorem commonVertex_zero :
    commonVertex S T ⟨0, commonVertex_card_pos S T⟩ = 0 := by
  let iz : Fin (commonVertexSet S T).card :=
    ⟨0, commonVertex_card_pos S T⟩
  change commonVertex S T iz = 0
  have hi : iz ≤ locateLeft S T 0 := Fin.mk_le_mk.mpr (Nat.zero_le _)
  have h := monotone_commonVertex S T
    hi
  rw [commonVertex_locateLeft, S.vertex_zero] at h
  exact le_antisymm h bot_le

def commonLastIndex : Fin (commonVertexSet S T).card :=
  ⟨(commonVertexSet S T).card - 1,
    Nat.sub_lt (commonVertex_card_pos S T) (by omega)⟩

theorem commonVertex_last : commonVertex S T (commonLastIndex S T) = 1 := by
  have hi : locateLeft S T (Fin.last (S.n + 1)) ≤ commonLastIndex S T :=
    Fin.mk_le_mk.mpr (Nat.le_sub_one_of_lt
      (locateLeft S T (Fin.last (S.n + 1))).isLt)
  have h := monotone_commonVertex S T
    hi
  rw [commonVertex_locateLeft, S.vertex_last] at h
  exact le_antisymm le_top h

def commonSegmentLeftIndex (j : Fin ((commonVertexSet S T).card - 1)) :
    Fin (commonVertexSet S T).card :=
  Fin.cast (Nat.sub_add_cancel (commonVertex_card_pos S T)) j.castSucc

def commonSegmentRightIndex (j : Fin ((commonVertexSet S T).card - 1)) :
    Fin (commonVertexSet S T).card :=
  Fin.cast (Nat.sub_add_cancel (commonVertex_card_pos S T)) j.succ

/-- Adjacent entries of the deduplicated common enumeration have no common
vertex strictly between them. -/
theorem no_commonVertex_between (j : Fin ((commonVertexSet S T).card - 1))
    {z : unitInterval} (hz : z ∈ commonVertexSet S T) :
    ¬ (commonVertex S T (commonSegmentLeftIndex S T j) < z ∧
      z < commonVertex S T (commonSegmentRightIndex S T j)) := by
  intro h
  let k := (commonVertexOrderIso S T).symm ⟨z, hz⟩
  have hkz : commonVertex S T k = z := by
    exact congrArg Subtype.val ((commonVertexOrderIso S T).apply_symm_apply ⟨z, hz⟩)
  have hjk : commonSegmentLeftIndex S T j < k := by
    apply (commonVertexOrderIso S T).lt_iff_lt.mp
    change commonVertex S T (commonSegmentLeftIndex S T j) < commonVertex S T k
    rw [hkz]
    exact h.1
  have hkj : k < commonSegmentRightIndex S T j := by
    apply (commonVertexOrderIso S T).lt_iff_lt.mp
    change commonVertex S T k < commonVertex S T (commonSegmentRightIndex S T j)
    rw [hkz]
    exact h.2
  change j.val < k.val at hjk
  change k.val < j.val + 1 at hkj
  omega

/-- A monotone finite vertex list with endpoints `0,1` has a segment
containing two ordered points whenever no vertex lies strictly between them.
The maximal eligible index selects the last duplicate of the left point. -/
theorem exists_segment_containing_of_no_vertex_between
    {n : ℕ} (v : Fin (n + 2) → unitInterval) (hv : Monotone v)
    (hv0 : v 0 = 0) (hv1 : v (Fin.last (n + 1)) = 1)
    {a b : unitInterval} (hab : a < b)
    (hgap : ∀ k, ¬ (a < v k ∧ v k < b)) :
    ∃ i : Fin (n + 1), v i.castSucc ≤ a ∧ b ≤ v i.succ := by
  let eligible : Finset (Fin (n + 2)) := Finset.univ.filter (fun k ↦ v k ≤ a)
  have hne : eligible.Nonempty := by
    refine ⟨0, ?_⟩
    simp [eligible, hv0]
  let k := eligible.max' hne
  have hk_mem : k ∈ eligible := Finset.max'_mem _ _
  have hk : v k ≤ a := (Finset.mem_filter.mp hk_mem).2
  have hk_ne_last : k ≠ Fin.last (n + 1) := by
    intro heq
    have : (1 : unitInterval) ≤ a := by simpa [k, heq, hv1] using hk
    have ha1 : a < (1 : unitInterval) := lt_of_lt_of_le hab b.2.2
    exact (not_lt_of_ge this) ha1
  have hklt : k.val < n + 1 := by
    have hle : k.val ≤ n + 1 := by omega
    exact lt_of_le_of_ne hle (by
      intro heq
      apply hk_ne_last
      apply Fin.ext
      simpa using heq)
  let i : Fin (n + 1) := ⟨k.val, hklt⟩
  refine ⟨i, ?_, ?_⟩
  · exact hk
  · by_contra hnot
    have hvnext_lt : v i.succ < b := lt_of_not_ge hnot
    have ha_lt_next : a < v i.succ := by
      by_contra hna
      have hnext_mem : i.succ ∈ eligible := by
        simp [eligible, le_of_not_gt hna]
      have hle := Finset.le_max' eligible i.succ hnext_mem
      change i.succ ≤ k at hle
      have hik : i.succ ≤ k := hle
      have hki : k < i.succ := by
        apply Fin.mk_lt_mk.mpr
        change k.val < k.val + 1
        omega
      exact (not_lt_of_ge hik) hki
    exact hgap i.succ ⟨ha_lt_next, hvnext_lt⟩

/-- Every adjacent common interval is contained in one segment of the left
subdivision. -/
theorem exists_left_segment_containing
    (j : Fin ((commonVertexSet S T).card - 1)) :
    ∃ i : Fin (S.n + 1),
      S.vertex i.castSucc ≤ commonVertex S T (commonSegmentLeftIndex S T j) ∧
      commonVertex S T (commonSegmentRightIndex S T j) ≤ S.vertex i.succ := by
  apply exists_segment_containing_of_no_vertex_between S.vertex S.monotone_vertex
    S.vertex_zero S.vertex_last
  · exact (commonVertexOrderIso S T).strictMono (by
      apply Fin.mk_lt_mk.mpr
      simp [commonSegmentLeftIndex, commonSegmentRightIndex])
  · intro k
    exact no_commonVertex_between S T j (left_vertex_mem S T k)

/-- Every adjacent common interval is contained in one segment of the right
subdivision. -/
theorem exists_right_segment_containing
    (j : Fin ((commonVertexSet S T).card - 1)) :
    ∃ i : Fin (T.n + 1),
      T.vertex i.castSucc ≤ commonVertex S T (commonSegmentLeftIndex S T j) ∧
      commonVertex S T (commonSegmentRightIndex S T j) ≤ T.vertex i.succ := by
  apply exists_segment_containing_of_no_vertex_between T.vertex T.monotone_vertex
    T.vertex_zero T.vertex_last
  · exact (commonVertexOrderIso S T).strictMono (by
      apply Fin.mk_lt_mk.mpr
      simp [commonSegmentLeftIndex, commonSegmentRightIndex])
  · intro k
    exact no_commonVertex_between S T j (right_vertex_mem S T k)

#print axioms commonVertexSet
#print axioms commonVertexOrderIso
#print axioms commonVertex_locateLeft
#print axioms commonVertex_locateRight
#print axioms monotone_commonVertex
#print axioms commonVertex_zero
#print axioms commonVertex_last
#print axioms no_commonVertex_between
#print axioms exists_segment_containing_of_no_vertex_between
#print axioms exists_left_segment_containing
#print axioms exists_right_segment_containing

end ConstructionTargets.PathSubdivisionCommonVertices
