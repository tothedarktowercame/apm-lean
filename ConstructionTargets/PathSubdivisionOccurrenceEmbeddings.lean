import ConstructionTargets.PathSubdivisionMultiplicityCommonVertices
import Mathlib.Data.List.NodupEquivFin

/-!
# Occurrence-sensitive embeddings into merged subdivision vertices
-/

open Set
open scoped unitInterval

noncomputable section

namespace ConstructionTargets.PathSubdivisionOccurrenceEmbeddings

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.PathSubdivisionMultiplicityCommonVertices

variable {X : Type*} [TopologicalSpace X]
variable {x y : X} {p : Path x y} {U V : Set X}
variable (S T : PathTwoOpenSubdivision p U V)

theorem sorted_internalVertices (S : PathTwoOpenSubdivision p U V) :
    (internalVertices S).SortedLE := by
  apply Monotone.sortedLE
  intro i j hij
  simp only [internalVertices, List.get_ofFn]
  apply S.monotone_vertex
  apply Fin.mk_le_mk.mpr
  simpa using Nat.add_le_add_right (show i.val ≤ j.val from hij) 1

theorem internalVertices_left_subperm_merged :
    List.Subperm (internalVertices S) (mergedInternalVertices S T) := by
  rw [← Multiset.coe_le]
  rw [show (↑(mergedInternalVertices S T) : Multiset unitInterval) =
      (↑(internalVertices S) : Multiset unitInterval) +
        (↑(internalVertices T) : Multiset unitInterval) by
    exact Multiset.sort_eq _ _]
  exact Multiset.le_add_right _ _

theorem internalVertices_right_subperm_merged :
    List.Subperm (internalVertices T) (mergedInternalVertices S T) := by
  rw [← Multiset.coe_le]
  rw [show (↑(mergedInternalVertices S T) : Multiset unitInterval) =
      (↑(internalVertices S) : Multiset unitInterval) +
        (↑(internalVertices T) : Multiset unitInterval) by
    exact Multiset.sort_eq _ _]
  exact Multiset.le_add_left _ _

theorem internalVertices_left_sublist_merged :
    List.Sublist (internalVertices S) (mergedInternalVertices S T) :=
  List.sublist_of_subperm_of_sortedLE
    (internalVertices_left_subperm_merged S T)
    (sorted_internalVertices S) (sorted_mergedInternalVertices S T)

theorem internalVertices_right_sublist_merged :
    List.Sublist (internalVertices T) (mergedInternalVertices S T) :=
  List.sublist_of_subperm_of_sortedLE
    (internalVertices_right_subperm_merged S T)
    (sorted_internalVertices T) (sorted_mergedInternalVertices S T)

/-- Occurrence-sensitive, order-preserving locations of the left internal
vertices in the merged list. -/
def leftInternalEmbedding : Fin S.n ↪o Fin (S.n + T.n) :=
  (Fin.castOrderIso (length_internalVertices S)).symm.toOrderEmbedding |>.trans
    (Classical.choose
      (List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
        (internalVertices_left_sublist_merged S T))) |>.trans
    (Fin.castOrderIso (length_mergedInternalVertices S T)).toOrderEmbedding

/-- Occurrence-sensitive, order-preserving locations of the right internal
vertices in the merged list. -/
def rightInternalEmbedding : Fin T.n ↪o Fin (S.n + T.n) :=
  (Fin.castOrderIso (length_internalVertices T)).symm.toOrderEmbedding |>.trans
    (Classical.choose
      (List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
        (internalVertices_right_sublist_merged S T))) |>.trans
    (Fin.castOrderIso (length_mergedInternalVertices S T)).toOrderEmbedding

theorem mergedInternalVertices_get_left (i : Fin S.n) :
    (mergedInternalVertices S T).get
        (Fin.cast (length_mergedInternalVertices S T).symm
          (leftInternalEmbedding S T i)) =
      S.vertex i.succ.castSucc := by
  let hex := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
    (internalVertices_left_sublist_merged S T)
  have hget := (Classical.choose_spec hex)
    (Fin.cast (length_internalVertices S).symm i)
  simpa [leftInternalEmbedding, internalVertices] using hget.symm

theorem mergedInternalVertices_get_right (i : Fin T.n) :
    (mergedInternalVertices S T).get
        (Fin.cast (length_mergedInternalVertices S T).symm
          (rightInternalEmbedding S T i)) =
      T.vertex i.succ.castSucc := by
  let hex := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
    (internalVertices_right_sublist_merged S T)
  have hget := (Classical.choose_spec hex)
    (Fin.cast (length_internalVertices T).symm i)
  simpa [rightInternalEmbedding, internalVertices] using hget.symm

theorem leftInternalEmbedding_strictMono :
    StrictMono (leftInternalEmbedding S T) :=
  (leftInternalEmbedding S T).strictMono

theorem rightInternalEmbedding_strictMono :
    StrictMono (rightInternalEmbedding S T) :=
  (rightInternalEmbedding S T).strictMono

#print axioms leftInternalEmbedding
#print axioms rightInternalEmbedding
#print axioms mergedInternalVertices_get_left
#print axioms mergedInternalVertices_get_right

end ConstructionTargets.PathSubdivisionOccurrenceEmbeddings
