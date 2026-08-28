import ConstructionTargets.TwoOpenDescentQuotient

/-!
# Coordinate layer for concatenating two-open path subdivisions
-/

open Set
open scoped unitInterval
noncomputable section

namespace ConstructionTargets.PathSubdivisionConcatenation

open ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision

variable {X : Type*} [TopologicalSpace X]
variable {x y z : X} {p : Path x y} {q : Path y z} {U V : Set X}

def leftHalf (t : unitInterval) : unitInterval :=
  ⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩

def rightHalf (t : unitInterval) : unitInterval :=
  ⟨(1 + (t : ℝ)) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩

theorem leftHalf_monotone : Monotone leftHalf := by
  intro a b hab
  change (a : ℝ) ≤ (b : ℝ) at hab
  change (a : ℝ) / 2 ≤ (b : ℝ) / 2
  linarith

theorem rightHalf_monotone : Monotone rightHalf := by
  intro a b hab
  change (a : ℝ) ≤ (b : ℝ) at hab
  change (1 + (a : ℝ)) / 2 ≤ (1 + (b : ℝ)) / 2
  linarith

@[simp] theorem leftHalf_zero : leftHalf 0 = 0 := by ext; simp [leftHalf]
@[simp] theorem leftHalf_one : leftHalf 1 = ⟨1 / 2, by norm_num, by norm_num⟩ := by
  ext
  simp [leftHalf]
@[simp] theorem rightHalf_zero : rightHalf 0 = ⟨1 / 2, by norm_num, by norm_num⟩ := by
  ext
  simp [rightHalf]
@[simp] theorem rightHalf_one : rightHalf 1 = 1 := by ext; simp [rightHalf]

/-- Vertices for the concatenation: all left vertices, followed by the
noninitial right vertices, so the midpoint occurs exactly once. -/
def concatVertex (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    Fin ((S.n + 2) + (T.n + 1)) → unitInterval :=
  Fin.addCases (fun i ↦ leftHalf (S.vertex i))
    (fun j ↦ rightHalf (T.vertex j.succ))

/-- Segment labels append without deleting a segment. -/
def concatSide (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    Fin ((S.n + 1) + (T.n + 1)) → Bool :=
  Fin.addCases S.side T.side

@[simp] theorem concatVertex_left (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (i : Fin (S.n + 2)) :
    concatVertex S T (Fin.castAdd (T.n + 1) i) = leftHalf (S.vertex i) := by
  simp [concatVertex]

@[simp] theorem concatVertex_right (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (j : Fin (T.n + 1)) :
    concatVertex S T (Fin.natAdd (S.n + 2) j) =
      rightHalf (T.vertex j.succ) := by
  simp [concatVertex]

@[simp] theorem concatSide_left (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (i : Fin (S.n + 1)) :
    concatSide S T (Fin.castAdd (T.n + 1) i) = S.side i := by
  simp [concatSide]

@[simp] theorem concatSide_right (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (j : Fin (T.n + 1)) :
    concatSide S T (Fin.natAdd (S.n + 1) j) = T.side j := by
  simp [concatSide]

theorem concatVertex_zero (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) : concatVertex S T 0 = 0 := by
  change leftHalf (S.vertex 0) = 0
  rw [S.vertex_zero, leftHalf_zero]

theorem concatVertex_last (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    concatVertex S T (Fin.last ((S.n + 2) + (T.n + 1) - 1)) = 1 := by
  rw [show Fin.last ((S.n + 2) + (T.n + 1) - 1) =
      Fin.natAdd (S.n + 2) (Fin.last T.n) by apply Fin.ext; simp]
  rw [concatVertex_right]
  have hs : (Fin.last T.n).succ = Fin.last (T.n + 1) := by apply Fin.ext; rfl
  rw [hs, T.vertex_last, rightHalf_one]

#print axioms concatVertex
#print axioms concatSide
#print axioms concatVertex_zero
#print axioms concatVertex_last

end ConstructionTargets.PathSubdivisionConcatenation
