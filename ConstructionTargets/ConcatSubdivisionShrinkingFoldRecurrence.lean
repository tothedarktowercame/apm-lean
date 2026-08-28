import ConstructionTargets.ConcatSubdivisionShrinkingFold
import ConstructionTargets.ComposeFinIndexReindex

/-!
# Zero stage and one-step recurrence for shrinking prefix folds
-/

open CategoryTheory
noncomputable section

namespace ConstructionTargets.ConcatSubdivisionShrinkingFoldRecurrence

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.PathSubdivisionConcatenation
open ConstructionTargets.ConcatSubdivisionShrinkingPrefix
open ConstructionTargets.ConcatSubdivisionShrinkingFold
open ConstructionTargets.ComposeFinIndexReindex

variable {X : Type*} [TopologicalSpace X]
variable {x y z : X} {p : Path x y} {q : Path y z} {U V : Set X}
variable {C : Type*} [Category C]

theorem shrinkingVertexEmbedding_zero_stage
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V)
    (i : Fin (concatSegmentCount S T + 1)) :
    shrinkingVertexEmbedding S T 0 i = i := by
  apply Fin.ext
  rfl

theorem shrinkingSegmentEmbedding_zero_stage
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V)
    (i : Fin (concatSegmentCount S T)) :
    shrinkingSegmentEmbedding S T 0 i = i := by
  apply Fin.ext
  rfl

/-- `composeFin` with one or more arrows is its initial restriction followed
by its terminal arrow.  This wrapper fixes the orientation used below. -/
theorem composeFin_terminal_split {n : ℕ} (A : Fin (n + 2) → C)
    (f : (i : Fin (n + 1)) → A i.castSucc ⟶ A i.succ) :
    TwoOpenDescentDatum.composeFin A f =
      TwoOpenDescentDatum.composeFin (A ∘ Fin.castSucc)
          (fun i => f i.castSucc) ≫
        f (Fin.last n) :=
  TwoOpenDescentDatum.composeFin_succ A f

/-- Initial vertex inclusion for the prefix of a positive-length chain. -/
def terminalPrefixVertex {m : ℕ} (hm : 0 < m) :
    Fin (m - 1 + 1) → Fin (m + 1) := fun i => ⟨i, by omega⟩

/-- Initial segment inclusion for the same prefix. -/
def terminalPrefixSegment {m : ℕ} (hm : 0 < m) :
    Fin (m - 1) → Fin m := fun i => ⟨i, by omega⟩

def terminalSegmentIndex {m : ℕ} (hm : 0 < m) : Fin m := ⟨m - 1, by omega⟩

theorem terminalPrefixVertex_zero {m : ℕ} (hm : 0 < m) :
    terminalPrefixVertex hm 0 = (0 : Fin (m + 1)) := by apply Fin.ext; rfl

theorem terminalSegmentIndex_succ {m : ℕ} (hm : 0 < m) :
    (terminalSegmentIndex hm).succ = Fin.last m := by
  apply Fin.ext
  simp [terminalSegmentIndex]
  omega

theorem terminalPrefixEndpoint_castSucc {m : ℕ} (hm : 0 < m)
    (i : Fin (m - 1)) :
    terminalPrefixVertex hm i.castSucc = (terminalPrefixSegment hm i).castSucc := by
  apply Fin.ext; rfl

theorem terminalPrefixEndpoint_succ {m : ℕ} (hm : 0 < m)
    (i : Fin (m - 1)) :
    terminalPrefixVertex hm i.succ = (terminalPrefixSegment hm i).succ := by
  apply Fin.ext; rfl

/-- The source objects of successive stages are canonically equal. -/
def shrinkingPrefixInitialIso
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ) :
    shrinkingPrefixObject D S T r 0 ≅
      shrinkingPrefixObject D S T (r + 1) 0 :=
  eqToIso (by simp [shrinkingPrefixObject])

/-- The last vertex at stage `r+1` is the source of the terminal stage-`r`
arrow. -/
def shrinkingPrefixBoundaryIso
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (hr : r < concatSegmentCount S T) :
    shrinkingPrefixObject D S T (r + 1)
        (Fin.last (concatSegmentCount S T - (r + 1))) ≅
      shrinkingPrefixObject D S T r
        ⟨concatSegmentCount S T - r - 1, by
          omega⟩ :=
  eqToIso (by
    apply congrArg (fun k => D.obj ((concatSubdivision S T).point k))
    apply Fin.ext
    change concatSegmentCount S T - (r + 1) =
      concatSegmentCount S T - r - 1
    omega)

def shrinkingPrefixTerminalIso
    (D : @TwoOpenDescentDatum X _ U V C _)
    (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (r : ℕ)
    (hr : r < concatSegmentCount S T) :
    shrinkingPrefixObject D S T r
        (⟨concatSegmentCount S T - r - 1, by omega⟩ :
          Fin (concatSegmentCount S T - r)).succ ≅
      shrinkingPrefixObject D S T r
        (Fin.last (concatSegmentCount S T - r)) :=
  eqToIso (by
    apply congrArg (shrinkingPrefixObject D S T r)
    apply Fin.ext
    change concatSegmentCount S T - r - 1 + 1 =
      concatSegmentCount S T - r
    omega)

#print axioms shrinkingVertexEmbedding_zero_stage
#print axioms shrinkingSegmentEmbedding_zero_stage
#print axioms composeFin_terminal_split
#print axioms shrinkingPrefixInitialIso
#print axioms shrinkingPrefixBoundaryIso
#print axioms shrinkingPrefixTerminalIso

end ConstructionTargets.ConcatSubdivisionShrinkingFoldRecurrence
