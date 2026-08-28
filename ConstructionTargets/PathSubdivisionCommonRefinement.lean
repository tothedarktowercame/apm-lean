import ConstructionTargets.PathSubdivisionCommonVertices

/-!
# A common two-open path subdivision

The sorted union of the vertices of two subdivisions is itself packaged as a
`PathTwoOpenSubdivision`.  Its side labels are chosen from containing segments
of the left subdivision.
-/

open Set
open scoped unitInterval

noncomputable section

set_option maxHeartbeats 1000000

namespace ConstructionTargets.PathSubdivisionCommonRefinement

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.PathSubdivisionCommonVertices

variable {X : Type*} [TopologicalSpace X]
variable {x y : X} {p : Path x y} {U V : Set X}
variable (S T : PathTwoOpenSubdivision p U V)

theorem two_le_commonVertex_card :
    2 ≤ (commonVertexSet S T).card := by
  have hsub : ({0, 1} : Finset unitInterval) ⊆ commonVertexSet S T := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact zero_mem S T
    · exact one_mem S T
  have hcard := Finset.card_le_card hsub
  simpa using hcard

def commonSubdivisionN : ℕ := (commonVertexSet S T).card - 2

theorem commonSubdivisionN_add_two :
    commonSubdivisionN S T + 2 = (commonVertexSet S T).card := by
  exact Nat.sub_add_cancel (two_le_commonVertex_card S T)

theorem commonSubdivisionN_add_one :
    commonSubdivisionN S T + 1 = (commonVertexSet S T).card - 1 := by
  have h := two_le_commonVertex_card S T
  unfold commonSubdivisionN
  omega

def commonSubdivisionVertex (k : Fin (commonSubdivisionN S T + 2)) : unitInterval :=
  commonVertex S T (Fin.cast (commonSubdivisionN_add_two S T) k)

def commonSubdivisionSegmentIndex (j : Fin (commonSubdivisionN S T + 1)) :
    Fin ((commonVertexSet S T).card - 1) :=
  Fin.cast (commonSubdivisionN_add_one S T) j

def containingLeftSegment (j : Fin (commonSubdivisionN S T + 1)) : Fin (S.n + 1) :=
  Classical.choose (exists_left_segment_containing S T
    (commonSubdivisionSegmentIndex S T j))

theorem containingLeftSegment_spec (j : Fin (commonSubdivisionN S T + 1)) :
    S.vertex (containingLeftSegment S T j).castSucc ≤
        commonVertex S T (commonSegmentLeftIndex S T
          (commonSubdivisionSegmentIndex S T j)) ∧
      commonVertex S T (commonSegmentRightIndex S T
          (commonSubdivisionSegmentIndex S T j)) ≤
        S.vertex (containingLeftSegment S T j).succ :=
  Classical.choose_spec (exists_left_segment_containing S T
    (commonSubdivisionSegmentIndex S T j))

theorem commonSubdivisionVertex_castSucc (j : Fin (commonSubdivisionN S T + 1)) :
    commonSubdivisionVertex S T j.castSucc =
      commonVertex S T (commonSegmentLeftIndex S T
        (commonSubdivisionSegmentIndex S T j)) := by
  congr 1

theorem commonSubdivisionVertex_succ (j : Fin (commonSubdivisionN S T + 1)) :
    commonSubdivisionVertex S T j.succ =
      commonVertex S T (commonSegmentRightIndex S T
        (commonSubdivisionSegmentIndex S T j)) := by
  congr 1

/-- The sorted union of the vertices of `S` and `T`, labelled using containing
segments of `S`. -/
def commonSubdivision : PathTwoOpenSubdivision p U V where
  n := commonSubdivisionN S T
  vertex := commonSubdivisionVertex S T
  side j := S.side (containingLeftSegment S T j)
  vertex_zero := by
    rw [commonSubdivisionVertex]
    convert commonVertex_zero S T using 1
  vertex_last := by
    change commonVertex S T
      (Fin.cast (commonSubdivisionN_add_two S T)
        (Fin.last (commonSubdivisionN S T + 1))) = 1
    rw [show Fin.cast (commonSubdivisionN_add_two S T)
        (Fin.last (commonSubdivisionN S T + 1)) = commonLastIndex S T by
      apply Fin.ext
      change commonSubdivisionN S T + 1 = (commonVertexSet S T).card - 1
      exact commonSubdivisionN_add_one S T]
    exact commonVertex_last S T
  monotone_vertex := by
    intro i j hij
    apply monotone_commonVertex S T
    exact Fin.mk_le_mk.mpr hij
  segment_mem := by
    intro j z hz
    rw [commonSubdivisionVertex_castSucc, commonSubdivisionVertex_succ] at hz
    have hs := containingLeftSegment_spec S T j
    exact S.segment_mem (containingLeftSegment S T j)
      ⟨hs.1.trans hz.1, hz.2.trans hs.2⟩

@[simp] theorem commonSubdivision_vertex (k : Fin (commonSubdivisionN S T + 2)) :
    (commonSubdivision S T).vertex k =
      commonVertex S T (Fin.cast (commonSubdivisionN_add_two S T) k) := rfl

def commonSubdivisionLocateLeft (i : Fin (S.n + 2)) :
    Fin (commonSubdivisionN S T + 2) :=
  Fin.cast (commonSubdivisionN_add_two S T).symm (locateLeft S T i)

def commonSubdivisionLocateRight (i : Fin (T.n + 2)) :
    Fin (commonSubdivisionN S T + 2) :=
  Fin.cast (commonSubdivisionN_add_two S T).symm (locateRight S T i)

@[simp] theorem commonSubdivision_vertex_locateLeft (i : Fin (S.n + 2)) :
    (commonSubdivision S T).vertex (commonSubdivisionLocateLeft S T i) = S.vertex i := by
  simp [commonSubdivisionLocateLeft]

@[simp] theorem commonSubdivision_vertex_locateRight (i : Fin (T.n + 2)) :
    (commonSubdivision S T).vertex (commonSubdivisionLocateRight S T i) = T.vertex i := by
  simp [commonSubdivisionLocateRight]

#print axioms two_le_commonVertex_card
#print axioms commonSubdivision
#print axioms commonSubdivision_vertex_locateLeft
#print axioms commonSubdivision_vertex_locateRight

end ConstructionTargets.PathSubdivisionCommonRefinement
