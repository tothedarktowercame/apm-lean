import ConstructionTargets.ConcatSubdivisionRightSuffixPeel

/-!
# Shrinking prefixes of a concatenated subdivision
-/

noncomputable section

namespace ConstructionTargets.ConcatSubdivisionShrinkingPrefix

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.PathSubdivisionConcatenation
open ConstructionTargets.ConcatSubdivisionRightSuffix

variable {X : Type*} [TopologicalSpace X]
variable {x y z : X} {p : Path x y} {q : Path y z} {U V : Set X}

def concatSegmentCount (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) : ℕ := S.n + T.n + 2

/-- Inclusion of the remaining segment indices after deleting `r` terminal
right-block arrows.  It is the structural initial inclusion, expressed with
its value equation rather than an arithmetic cast. -/
def shrinkingSegmentEmbedding (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ) :
    Fin (concatSegmentCount S T - r) ↪o Fin (concatSegmentCount S T) where
  toFun i := ⟨i, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le _ _)⟩
  inj' _ _ h := Fin.ext (congrArg
    (fun j : Fin (concatSegmentCount S T) => j.val) h)
  map_rel_iff' := Iff.rfl

/-- The corresponding inclusion of the remaining vertices. -/
def shrinkingVertexEmbedding (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ) :
    Fin (concatSegmentCount S T - r + 1) ↪o
      Fin (concatSegmentCount S T + 1) where
  toFun i := ⟨i, by
      have hi := i.isLt
      have hle := Nat.sub_le (concatSegmentCount S T) r
      omega⟩
  inj' _ _ h := Fin.ext (congrArg
    (fun j : Fin (concatSegmentCount S T + 1) => j.val) h)
  map_rel_iff' := Iff.rfl

@[simp] theorem shrinkingSegmentEmbedding_val
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r) (i) :
    (shrinkingSegmentEmbedding S T r i).val = i.val := rfl

@[simp] theorem shrinkingVertexEmbedding_val
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r) (i) :
    (shrinkingVertexEmbedding S T r i).val = i.val := rfl

@[simp] theorem shrinkingVertexEmbedding_zero
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r) :
    shrinkingVertexEmbedding S T r 0 = 0 := by
  apply Fin.ext
  rfl

theorem shrinkingVertexEmbedding_last
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (_hr : r ≤ concatSegmentCount S T) :
    (shrinkingVertexEmbedding S T r
      (Fin.last (concatSegmentCount S T - r))).val =
        concatSegmentCount S T - r := by
  rfl

/-- If at least one right segment remains, the terminal prefix segment is the
corresponding decreasing right segment. -/
theorem shrinkingSegment_last_eq_rightSegment
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ) (hr : r ≤ T.n) :
    shrinkingSegmentEmbedding S T r
        ⟨concatSegmentCount S T - r - 1, by
          simp only [concatSegmentCount]
          omega⟩ =
      rightSegment S T ⟨T.n - r, by omega⟩ := by
  apply Fin.ext
  change concatSegmentCount S T - r - 1 = S.n + 1 + (T.n - r)
  simp only [concatSegmentCount]
  omega

@[simp] theorem rightBlockVertex_val
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (j : Fin (T.n + 2)) :
    (rightBlockVertex S T j).val = S.n + 1 + j.val := by
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [rightBlockVertex, rightSegment, concatSubdivision]
  · simp [rightBlockVertex, rightSegment, concatSubdivision]
    omega

/-- The terminal boundary vertex of the same prefix is the matching
right-block vertex. -/
theorem shrinkingVertex_last_eq_rightBlockVertex
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ) (hr : r ≤ T.n + 1) :
    shrinkingVertexEmbedding S T r
        (Fin.last (concatSegmentCount S T - r)) =
      rightBlockVertex S T ⟨T.n + 1 - r, by omega⟩ := by
  apply Fin.ext
  rw [rightBlockVertex_val]
  change concatSegmentCount S T - r = S.n + 1 + (T.n + 1 - r)
  simp only [concatSegmentCount]
  omega

/-- Removing one more terminal arrow agrees literally with restricting the
current prefix by `Fin.castSucc`. -/
theorem shrinkingVertex_succ_restriction
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (hr : r < concatSegmentCount S T)
    (i : Fin (concatSegmentCount S T - (r + 1) + 1)) :
    shrinkingVertexEmbedding S T (r + 1) i =
      shrinkingVertexEmbedding S T r
        ⟨i, by
          have hi := i.isLt
          omega⟩ := by
  apply Fin.ext
  rfl

/-- The segment indices have the same one-step initial restriction. -/
theorem shrinkingSegment_succ_restriction
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (hr : r + 1 < concatSegmentCount S T)
    (i : Fin (concatSegmentCount S T - (r + 1))) :
    shrinkingSegmentEmbedding S T (r + 1) i =
      shrinkingSegmentEmbedding S T r
        ⟨i, by
          have hi := i.isLt
          omega⟩ := by
  apply Fin.ext
  rfl

/-- The two restrictions used by `composeFin_dropLast_two` are the two-step
successor of the shrinking-prefix family. -/
theorem shrinkingVertex_two_restrictions
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (hr : r + 2 ≤ concatSegmentCount S T)
    (i : Fin (concatSegmentCount S T - (r + 2) + 1)) :
    shrinkingVertexEmbedding S T (r + 2) i =
      shrinkingVertexEmbedding S T r
        ⟨i, by
          have hi := i.isLt
          omega⟩ := by
  apply Fin.ext
  rfl

#print axioms shrinkingSegment_last_eq_rightSegment
#print axioms shrinkingVertex_last_eq_rightBlockVertex
#print axioms shrinkingVertex_succ_restriction
#print axioms shrinkingSegment_succ_restriction
#print axioms shrinkingVertex_two_restrictions

end ConstructionTargets.ConcatSubdivisionShrinkingPrefix
