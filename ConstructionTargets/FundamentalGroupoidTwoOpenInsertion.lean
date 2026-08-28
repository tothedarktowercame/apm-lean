import ConstructionTargets.FundamentalGroupoidTwoOpenRefinement
import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Inserting one vertex in a subordinate two-open path subdivision

This file constructs the finite-index data for inserting a parameter inside
one segment.  The construction duplicates that segment's cover label; its two
new restricted paths are therefore covered by the banked local split theorem.
-/

open Set CategoryTheory
open scoped unitInterval

noncomputable section

namespace ConstructionTargets.FundamentalGroupoidTwoOpenInsertion

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.FundamentalGroupoidTwoOpenRefinement

variable {X : Type*} [TopologicalSpace X] {U V : Set X}
variable {x y : X} {p : Path x y}

namespace TwoOpenDescentDatum

variable {C : Type*} [Category C]

/-- The composable-arrow chain determined by dependent adjacent arrows. -/
def adjacentChain {n : ℕ} (A : Fin (n + 1) → C)
    (f : (i : Fin n) → A i.castSucc ⟶ A i.succ) :
    ComposableArrows C n :=
  ComposableArrows.mkOfObjOfMapSucc A f

@[simp] theorem adjacentChain_obj {n : ℕ} (A : Fin (n + 1) → C)
    (f : (i : Fin n) → A i.castSucc ⟶ A i.succ) (i) :
    (adjacentChain A f).obj i = A i := rfl

theorem adjacentChain_map_succ {n : ℕ} (A : Fin (n + 1) → C)
    (f : (i : Fin n) → A i.castSucc ⟶ A i.succ) (i : ℕ) (hi : i < n) :
    (adjacentChain A f).map' i (i + 1) = f ⟨i, hi⟩ :=
  ComposableArrows.mkOfObjOfMapSucc_map_succ A f i hi

variable (D : @FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum X _ U V C _)

/-- The composable-arrow presentation of a subdivision's mapped pieces. -/
def subdivisionChain {x y : X} {p : Path x y}
    (S : PathTwoOpenSubdivision p U V) : ComposableArrows C (S.n + 1) :=
  adjacentChain (D.obj ∘ S.point) (D.mappedPiece S)

end TwoOpenDescentDatum

namespace PathTwoOpenSubdivision

def insertedSidePosition (S : PathTwoOpenSubdivision p U V)
    (k : Fin (S.n + 1)) : Fin (S.n + 2) := ⟨k.val + 1, by omega⟩

def insertedVertexPosition (S : PathTwoOpenSubdivision p U V)
    (k : Fin (S.n + 1)) : Fin ((S.n + 2) + 1) :=
  (insertedSidePosition S k).castSucc

/-- The vertex tuple obtained by inserting `t` after the initial endpoint of
segment `k`. -/
def insertedVertex (S : PathTwoOpenSubdivision p U V)
    (k : Fin (S.n + 1)) (t : unitInterval) : Fin ((S.n + 2) + 1) → unitInterval :=
  Fin.insertNth (insertedVertexPosition S k) t S.vertex

/-- The side tuple obtained by duplicating the label of segment `k`. -/
def insertedSide (S : PathTwoOpenSubdivision p U V)
    (k : Fin (S.n + 1)) : Fin (S.n + 2) → Bool :=
  Fin.insertNth (insertedSidePosition S k) (S.side k) S.side

@[simp] theorem insertedVertex_at (S : PathTwoOpenSubdivision p U V)
    (k : Fin (S.n + 1)) (t : unitInterval) :
    insertedVertex S k t (insertedVertexPosition S k) = t := by
  simp [insertedVertex]

@[simp] theorem insertedVertex_old (S : PathTwoOpenSubdivision p U V)
    (k : Fin (S.n + 1)) (t : unitInterval) (i : Fin (S.n + 2)) :
    insertedVertex S k t ((insertedVertexPosition S k).succAbove i) = S.vertex i := by
  simp [insertedVertex]

@[simp] theorem insertedSide_at (S : PathTwoOpenSubdivision p U V)
    (k : Fin (S.n + 1)) :
    insertedSide S k (insertedSidePosition S k) = S.side k := by
  simp [insertedSide]

@[simp] theorem insertedSide_old (S : PathTwoOpenSubdivision p U V)
    (k : Fin (S.n + 1)) (i : Fin (S.n + 1)) :
    insertedSide S k ((insertedSidePosition S k).succAbove i) = S.side i := by
  simp [insertedSide]

/-- Proof-carrying insertion data.  The inequalities are precisely what is
needed for the new tuple to remain ordered. -/
structure SingleVertexInsertion (S : PathTwoOpenSubdivision p U V) where
  segment : Fin (S.n + 1)
  parameter : unitInterval
  lower : S.vertex segment.castSucc ≤ parameter
  upper : parameter ≤ S.vertex segment.succ

namespace SingleVertexInsertion

variable {S : PathTwoOpenSubdivision p U V} (ins : SingleVertexInsertion S)

theorem insertedVertex_adjacent (i : Fin (S.n + 2)) :
    insertedVertex S ins.segment ins.parameter i.castSucc ≤
      insertedVertex S ins.segment ins.parameter i.succ := by
  let pivot := insertedVertexPosition S ins.segment
  let pivot₀ := insertedSidePosition S ins.segment
  by_cases h₀ : i.succ = pivot
  · have hi : i = ins.segment.castSucc := by
      apply Fin.ext
      simpa [pivot, insertedVertexPosition, insertedSidePosition] using
        congrArg Fin.val h₀
    have hlt : ins.segment.castSucc < pivot₀ := by
      apply Fin.mk_lt_mk.mpr
      simp [pivot₀, insertedSidePosition]
    have he : pivot.succAbove ins.segment.castSucc = i.castSucc := by
      simpa [pivot, insertedVertexPosition, hi] using
        Fin.succAbove_castSucc_of_lt pivot₀ ins.segment.castSucc hlt
    rw [← he, insertedVertex_old, h₀, insertedVertex_at]
    exact ins.lower
  by_cases h₁ : i.castSucc = pivot
  · have hi : i = ins.segment.succ := by
      apply Fin.ext
      simpa [pivot, insertedVertexPosition, insertedSidePosition] using
        congrArg Fin.val h₁
    have hp : pivot₀ = ins.segment.succ := by
      apply Fin.ext
      simp [pivot₀, insertedSidePosition]
    have he : pivot.succAbove ins.segment.succ = i.succ := by
      have hp' : pivot = ins.segment.succ.castSucc := by
        simpa [pivot, insertedVertexPosition] using congrArg Fin.castSucc hp
      rw [hp', hi]
      exact Fin.succAbove_castSucc_self _
    rw [h₁, insertedVertex_at, ← he, insertedVertex_old]
    exact ins.upper
  · let i₀ := pivot₀.predAbove i.castSucc
    let i₁ := pivot₀.predAbove i.succ
    have he₀ : pivot.succAbove i₀ = i.castSucc := by
      exact Fin.succAbove_predAbove h₁
    have he₁ : pivot.succAbove i₁ = i.succ := by
      exact Fin.succAbove_predAbove h₀
    rw [← he₀, insertedVertex_old, ← he₁, insertedVertex_old]
    exact S.monotone_vertex
      (Fin.predAbove_right_monotone pivot₀ i.castSucc_le_succ)

theorem monotone_insertedVertex :
    Monotone (insertedVertex S ins.segment ins.parameter) := by
  rw [Fin.monotone_iff_le_succ]
  exact ins.insertedVertex_adjacent

/-- The proof-carrying insertion packaged as an actual subordinate
subdivision. -/
def refined : PathTwoOpenSubdivision p U V where
  n := S.n + 1
  vertex := insertedVertex S ins.segment ins.parameter
  side := insertedSide S ins.segment
  vertex_zero := by
    let pivot := insertedVertexPosition S ins.segment
    have hp : (0 : Fin (S.n + 2 + 1)) = pivot.succAbove 0 := by
      symm
      apply Fin.succAbove_ne_zero_zero
      apply Fin.ne_of_gt
      apply Fin.mk_lt_mk.mpr
      simp [pivot, insertedVertexPosition, insertedSidePosition]
    rw [hp, insertedVertex_old]
    exact S.vertex_zero
  vertex_last := by
    let pivot := insertedVertexPosition S ins.segment
    have hp : Fin.last (S.n + 2) =
        pivot.succAbove (Fin.last (S.n + 1)) := by
      symm
      apply Fin.succAbove_ne_last_last
      apply Fin.ne_of_lt
      apply Fin.mk_lt_mk.mpr
      simp [pivot, insertedVertexPosition, insertedSidePosition]
      omega
    rw [hp, insertedVertex_old]
    exact S.vertex_last
  monotone_vertex := ins.monotone_insertedVertex
  segment_mem := by
    intro j z hz
    let pivot₀ := insertedSidePosition S ins.segment
    let pivot := insertedVertexPosition S ins.segment
    by_cases hr : j = pivot₀
    · subst j
      have hp : pivot = pivot₀.castSucc := rfl
      have hv : pivot.succAbove ins.segment.succ = pivot₀.succ := by
        rw [hp]
        have he : pivot₀ = ins.segment.succ := by
          apply Fin.ext
          simp [pivot₀, insertedSidePosition]
        subst pivot₀
        exact Fin.succAbove_castSucc_self _
      have hz' : z ∈ Icc ins.parameter (S.vertex ins.segment.succ) := by
        rw [← hp, insertedVertex_at] at hz
        rw [← hv, insertedVertex_old] at hz
        exact hz
      rw [show insertedSide S ins.segment pivot₀ = S.side ins.segment by
        exact insertedSide_at S ins.segment]
      exact
        S.segment_mem ins.segment ⟨ins.lower.trans hz'.1, hz'.2⟩
    · by_cases hl : j.succ = pivot
      · have hj : j = ins.segment.castSucc := by
          apply Fin.ext
          simpa [pivot, insertedVertexPosition, insertedSidePosition] using
            congrArg Fin.val hl
        have hv : pivot.succAbove ins.segment.castSucc = j.castSucc := by
          have hlt : ins.segment.castSucc < pivot₀ := by
            apply Fin.mk_lt_mk.mpr
            simp [pivot₀, insertedSidePosition]
          simpa [pivot, insertedVertexPosition, hj] using
            Fin.succAbove_castSucc_of_lt pivot₀ ins.segment.castSucc hlt
        have hz' : z ∈ Icc (S.vertex ins.segment.castSucc) ins.parameter := by
          rw [hl, insertedVertex_at] at hz
          rw [← hv, insertedVertex_old] at hz
          exact hz
        have hs : insertedSide S ins.segment j = S.side ins.segment := by
          subst j
          have hp₀ : pivot₀ = ins.segment.succ := by
            apply Fin.ext
            simp [pivot₀, insertedSidePosition]
          have he : pivot₀.succAbove ins.segment = ins.segment.castSucc := by
            rw [hp₀]
            exact Fin.succAbove_succ_self _
          rw [← he, insertedSide_old]
        rw [hs]
        exact S.segment_mem ins.segment ⟨hz'.1, hz'.2.trans ins.upper⟩
      · by_cases hb : j < pivot₀
        · let old := j.castPred (Fin.ne_of_lt (hb.trans_le (Fin.le_last _)))
          have hs : insertedSide S ins.segment j = S.side old := by
            simpa [insertedSide, old] using
              Fin.insertNth_apply_below (α := fun _ ↦ Bool) hb
                (S.side ins.segment) S.side
          have hb₀ : j.castSucc < pivot := by
            apply Fin.mk_lt_mk.mpr
            simpa [pivot, pivot₀, insertedVertexPosition] using hb
          have hb₁ : j.succ < pivot := by
            have hle : j.succ ≤ pivot := by
              apply Fin.mk_le_mk.mpr
              simpa [pivot, pivot₀, insertedVertexPosition] using hb
            exact lt_of_le_of_ne hle hl
          have hv₀ : insertedVertex S ins.segment ins.parameter j.castSucc =
              S.vertex old.castSucc := by
            simpa [insertedVertex, old] using
              Fin.insertNth_apply_below (α := fun _ ↦ unitInterval) hb₀
                ins.parameter S.vertex
          have hv₁ : insertedVertex S ins.segment ins.parameter j.succ =
              S.vertex old.succ := by
            simpa [insertedVertex, old] using
              Fin.insertNth_apply_below (α := fun _ ↦ unitInterval) hb₁
                ins.parameter S.vertex
          rw [hv₀, hv₁] at hz
          rw [hs]
          exact S.segment_mem old hz
        · have ha : pivot₀ < j := lt_of_le_of_ne (le_of_not_gt hb) (Ne.symm hr)
          let old := j.pred (Fin.ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) ha))
          have hs : insertedSide S ins.segment j = S.side old := by
            simpa [insertedSide, old] using
              Fin.insertNth_apply_above (α := fun _ ↦ Bool) ha
                (S.side ins.segment) S.side
          have ha₀ : pivot < j.castSucc := by
            apply Fin.mk_lt_mk.mpr
            simpa [pivot, pivot₀, insertedVertexPosition] using ha
          have ha₁ : pivot < j.succ := ha₀.trans j.castSucc_lt_succ
          have hv₀ : insertedVertex S ins.segment ins.parameter j.castSucc =
              S.vertex old.castSucc := by
            simpa [insertedVertex, old] using
              Fin.insertNth_apply_above (α := fun _ ↦ unitInterval) ha₀
                ins.parameter S.vertex
          have hv₁ : insertedVertex S ins.segment ins.parameter j.succ =
              S.vertex old.succ := by
            simpa [insertedVertex, old] using
              Fin.insertNth_apply_above (α := fun _ ↦ unitInterval) ha₁
                ins.parameter S.vertex
          rw [hv₀, hv₁] at hz
          rw [hs]
          exact S.segment_mem old hz

@[simp] theorem refined_n : ins.refined.n = S.n + 1 := rfl

@[simp] theorem refined_vertex : ins.refined.vertex =
    insertedVertex S ins.segment ins.parameter := rfl

@[simp] theorem refined_side : ins.refined.side = insertedSide S ins.segment := rfl

end SingleVertexInsertion

end PathTwoOpenSubdivision

namespace TwoOpenDescentDatum

variable {C : Type*} [Category C]
variable (D : @FundamentalGroupoidTwoOpenDescent.TwoOpenDescentDatum X _ U V C _)

/-- The refined mapped-piece chain restricted along the order embedding which
skips the inserted vertex. -/
def refinedRestrictedChain {x y : X} {p : Path x y}
    {S : PathTwoOpenSubdivision p U V}
    (ins : PathTwoOpenSubdivision.SingleVertexInsertion S) :
    ComposableArrows C (S.n + 1) :=
  (Fin.succAboveOrderEmb
      (PathTwoOpenSubdivision.insertedVertexPosition S ins.segment)).monotone.functor ⋙
    subdivisionChain D ins.refined

end TwoOpenDescentDatum

#print axioms PathTwoOpenSubdivision.insertedVertex_old
#print axioms PathTwoOpenSubdivision.insertedSide_old
#print axioms PathTwoOpenSubdivision.SingleVertexInsertion.refined

end ConstructionTargets.FundamentalGroupoidTwoOpenInsertion
