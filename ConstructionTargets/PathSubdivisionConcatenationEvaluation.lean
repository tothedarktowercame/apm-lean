import ConstructionTargets.PathSubdivisionConcatenation
import ConstructionTargets.PathMapPathTransport

/-!
# Mapped-piece transport for concatenated subdivisions
-/

open Set CategoryTheory
noncomputable section

namespace ConstructionTargets.PathSubdivisionConcatenationEvaluation

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
open ConstructionTargets.FundamentalGroupoidTwoOpenDescent
open ConstructionTargets.PathSubdivisionConcatenation
open ConstructionTargets.PathMapPathTransport

variable {X : Type*} [TopologicalSpace X]
variable {x y z : X} {p : Path x y} {q : Path y z} {U V : Set X}
variable {C : Type*} [Category C]

def leftSegment (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (i : Fin (S.n + 1)) :
    Fin ((concatSubdivision S T).n + 1) :=
  Fin.cast (by simp; omega) (Fin.castAdd (T.n + 1) i)

def rightSegment (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (j : Fin (T.n + 1)) :
    Fin ((concatSubdivision S T).n + 1) :=
  Fin.cast (by simp; omega) (Fin.natAdd (S.n + 1) j)

theorem trans_leftHalf_apply (t : unitInterval) : (p.trans q) (leftHalf t) = p t := by
  rw [Path.trans_apply]
  split_ifs with h
  · congr 1
    apply Subtype.ext
    simp [leftHalf]
    ring
  · exfalso
    apply h
    simp [leftHalf]
    linarith [t.2.2]

theorem trans_rightHalf_apply (t : unitInterval) : (p.trans q) (rightHalf t) = q t := by
  rw [Path.trans_apply]
  split_ifs with h
  · have ht : (1 : ℝ) / 2 ≤ (rightHalf t : ℝ) := by
      simp [rightHalf]
      linarith [t.2.1]
    have heq : (rightHalf t : ℝ) = 1 / 2 := le_antisymm h ht
    have hz : t = 0 := by
      apply Subtype.ext
      change (t : ℝ) = 0
      simp [rightHalf] at heq
      linarith
    subst t
    simp [rightHalf, p.target, q.source]
  · congr 1
    apply Subtype.ext
    simp [rightHalf]
    ring

#print axioms trans_leftHalf_apply
#print axioms trans_rightHalf_apply

end ConstructionTargets.PathSubdivisionConcatenationEvaluation
