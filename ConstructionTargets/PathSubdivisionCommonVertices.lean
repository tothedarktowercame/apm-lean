import ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
import Mathlib.Data.Finset.Sort

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

#print axioms commonVertexSet
#print axioms commonVertexOrderIso
#print axioms commonVertex_locateLeft
#print axioms commonVertex_locateRight
#print axioms monotone_commonVertex
#print axioms commonVertex_zero
#print axioms commonVertex_last

end ConstructionTargets.PathSubdivisionCommonVertices
