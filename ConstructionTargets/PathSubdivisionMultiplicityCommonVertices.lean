import ConstructionTargets.PathSubdivisionInsertionReachability
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.Sort

/-!
# Multiplicity-preserving common path-subdivision vertices
-/

open Set
open scoped unitInterval

noncomputable section

namespace ConstructionTargets.PathSubdivisionMultiplicityCommonVertices

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision

variable {X : Type*} [TopologicalSpace X]
variable {x y : X} {p : Path x y} {U V : Set X}
variable (S T : PathTwoOpenSubdivision p U V)

/-- Internal vertices of a subdivision, retaining repetitions and internal
copies of `0` or `1`. -/
def internalVertices (S : PathTwoOpenSubdivision p U V) : List unitInterval :=
  List.ofFn (fun i : Fin S.n ↦ S.vertex i.succ.castSucc)

@[simp] theorem length_internalVertices : (internalVertices S).length = S.n := by
  simp [internalVertices]

/-- Sorted multiset sum of the two internal vertex tuples. -/
def mergedInternalVertices : List unitInterval :=
  ((↑(internalVertices S) : Multiset unitInterval) +
    (↑(internalVertices T) : Multiset unitInterval)).sort (· ≤ ·)

@[simp] theorem length_mergedInternalVertices :
    (mergedInternalVertices S T).length = S.n + T.n := by
  simp [mergedInternalVertices]

theorem sorted_mergedInternalVertices :
    (mergedInternalVertices S T).SortedLE := by
  exact (Multiset.pairwise_sort
    ((↑(internalVertices S) : Multiset unitInterval) +
      (↑(internalVertices T) : Multiset unitInterval)) (· ≤ ·)).sortedLE

/-- The common tuple keeps one mandatory endpoint at each end and every
internal occurrence from both sources. -/
def mergedVertices : List unitInterval :=
  0 :: mergedInternalVertices S T ++ [1]

@[simp] theorem length_mergedVertices :
    (mergedVertices S T).length = S.n + T.n + 2 := by
  simp [mergedVertices]

theorem sorted_mergedVertices : (mergedVertices S T).SortedLE := by
  have hcore := sorted_mergedInternalVertices S T
  apply List.Pairwise.sortedLE
  rw [mergedVertices, List.pairwise_append]
  constructor
  · rw [List.pairwise_cons]
    exact ⟨fun z _ ↦ bot_le, hcore.pairwise⟩
  constructor
  · simp
  · intro z hz w hw
    simp only [List.mem_singleton] at hw
    subst w
    exact le_top

/-- Finite coordinate function of the multiplicity-preserving common tuple. -/
def mergedVertex (i : Fin (S.n + T.n + 2)) : unitInterval :=
  (mergedVertices S T).get (Fin.cast (length_mergedVertices S T).symm i)

theorem monotone_mergedVertex : Monotone (mergedVertex S T) := by
  intro i j hij
  apply (sorted_mergedVertices S T).monotone_get
  exact Fin.mk_le_mk.mpr hij

@[simp] theorem mergedVertex_zero : mergedVertex S T 0 = 0 := by
  simp [mergedVertex, mergedVertices]

@[simp] theorem mergedVertex_last :
    mergedVertex S T (Fin.last (S.n + T.n + 1)) = 1 := by
  simp [mergedVertex, mergedVertices]

/-- Multiplicity of an internal parameter is the sum of its source
multiplicities. -/
theorem count_mergedInternalVertices (z : unitInterval) :
    Multiset.count z (↑(mergedInternalVertices S T) : Multiset unitInterval) =
      Multiset.count z (↑(internalVertices S) : Multiset unitInterval) +
        Multiset.count z (↑(internalVertices T) : Multiset unitInterval) := by
  have hsort : (↑(mergedInternalVertices S T) : Multiset unitInterval) =
      (↑(internalVertices S) : Multiset unitInterval) +
        (↑(internalVertices T) : Multiset unitInterval) := by
    exact Multiset.sort_eq _ _
  rw [hsort, Multiset.count_add]

#print axioms sorted_mergedVertices
#print axioms monotone_mergedVertex
#print axioms mergedVertex_zero
#print axioms mergedVertex_last
#print axioms count_mergedInternalVertices

end ConstructionTargets.PathSubdivisionMultiplicityCommonVertices
