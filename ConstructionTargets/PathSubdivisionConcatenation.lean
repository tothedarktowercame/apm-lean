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

theorem concatVertex_monotone (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) : Monotone (concatVertex S T) := by
  intro a
  refine Fin.addCases
    (motive := fun a : Fin ((S.n + 2) + (T.n + 1)) ↦ ∀ b, a ≤ b →
      concatVertex S T a ≤ concatVertex S T b) ?_ ?_ a
  · intro i
    intro b hab
    rw [concatVertex_left]
    refine Fin.addCases
      (motive := fun b ↦ Fin.castAdd (T.n + 1) i ≤ b →
        leftHalf (S.vertex i) ≤ concatVertex S T b) ?_ ?_ b hab
    · intro j h
      rw [concatVertex_left]
      apply leftHalf_monotone
      apply S.monotone_vertex
      exact h
    · intro j _
      rw [concatVertex_right]
      calc
        leftHalf (S.vertex i) ≤ leftHalf 1 :=
          leftHalf_monotone (by simpa using (S.vertex i).2.2)
        _ = rightHalf 0 := by rw [leftHalf_one, rightHalf_zero]
        _ ≤ rightHalf (T.vertex j.succ) :=
          rightHalf_monotone (by simpa using (T.vertex j.succ).2.1)
  · intro i
    intro b hab
    rw [concatVertex_right]
    refine Fin.addCases
      (motive := fun b ↦ Fin.natAdd (S.n + 2) i ≤ b →
        rightHalf (T.vertex i.succ) ≤ concatVertex S T b) ?_ ?_ b hab
    · intro j h
      exfalso
      exact (not_le_of_gt (show j.val < S.n + 2 + i.val by omega)) h
    · intro j h
      rw [concatVertex_right]
      apply rightHalf_monotone
      apply T.monotone_vertex
      change i.val + 1 ≤ j.val + 1
      change S.n + 2 + i.val ≤ S.n + 2 + j.val at h
      omega

theorem trans_subpath_left_apply (a b t : unitInterval) :
    (p.trans q).subpath (leftHalf a) (leftHalf b) t = p.subpath a b t := by
  change (p.trans q) (Set.Icc.convexCombo (leftHalf a) (leftHalf b) t) =
    p (Set.Icc.convexCombo a b t)
  rw [Path.trans_apply]
  split_ifs with h
  · apply congr_arg p
    apply Subtype.ext
    simp [leftHalf, Set.Icc.convexCombo]
    ring
  · exfalso
    have ht : ((Set.Icc.convexCombo (leftHalf a) (leftHalf b) t :
        unitInterval) : ℝ) ≤ 1 / 2 := by
      simp [leftHalf, Set.Icc.convexCombo]
      nlinarith [a.2.2, b.2.2, t.2.1, t.2.2]
    exact h ht

theorem trans_subpath_right_apply (a b t : unitInterval) :
    (p.trans q).subpath (rightHalf a) (rightHalf b) t = q.subpath a b t := by
  change (p.trans q) (Set.Icc.convexCombo (rightHalf a) (rightHalf b) t) =
    q (Set.Icc.convexCombo a b t)
  rw [Path.trans_apply]
  split_ifs with h
  · have ht : (1 : ℝ) / 2 ≤
        ((Set.Icc.convexCombo (rightHalf a) (rightHalf b) t :
          unitInterval) : ℝ) := by
      simp [rightHalf, Set.Icc.convexCombo]
      nlinarith [a.2.1, b.2.1, t.2.1, t.2.2]
    have heq : ((Set.Icc.convexCombo (rightHalf a) (rightHalf b) t :
        unitInterval) : ℝ) = 1 / 2 := le_antisymm h ht
    have hab : Set.Icc.convexCombo a b t = (0 : unitInterval) := by
      apply Subtype.ext
      simp [rightHalf, Set.Icc.convexCombo] at heq ⊢
      nlinarith
    rw [show (⟨2 * (Set.Icc.convexCombo (rightHalf a) (rightHalf b) t : ℝ), _⟩ :
        unitInterval) = 1 by
          apply Subtype.ext
          change 2 * (Set.Icc.convexCombo (rightHalf a) (rightHalf b) t : ℝ) = 1
          rw [heq]
          norm_num]
    rw [p.target, hab, q.source]
  · apply congr_arg q
    apply Subtype.ext
    simp [rightHalf, Set.Icc.convexCombo]
    ring

theorem concatVertex_segment_left_castSucc (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (i : Fin (S.n + 1)) :
    concatVertex S T (Fin.cast (by omega) (Fin.castAdd (T.n + 1) i).castSucc) =
      leftHalf (S.vertex i.castSucc) := by
  rw [show Fin.cast (by omega) (Fin.castAdd (T.n + 1) i).castSucc =
    Fin.castAdd (T.n + 1) i.castSucc by apply Fin.ext; rfl]
  exact concatVertex_left S T i.castSucc

theorem concatVertex_segment_left_succ (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (i : Fin (S.n + 1)) :
    concatVertex S T (Fin.cast (by omega) (Fin.castAdd (T.n + 1) i).succ) =
      leftHalf (S.vertex i.succ) := by
  rw [show Fin.cast (by omega) (Fin.castAdd (T.n + 1) i).succ =
    Fin.castAdd (T.n + 1) i.succ by apply Fin.ext; rfl]
  exact concatVertex_left S T i.succ

theorem concatVertex_segment_right_castSucc (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (i : Fin (T.n + 1)) :
    concatVertex S T (Fin.cast (by omega) (Fin.natAdd (S.n + 1) i).castSucc) =
      rightHalf (T.vertex i.castSucc) := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [show Fin.cast (by omega) (Fin.natAdd (S.n + 1) (0 : Fin (T.n + 1))).castSucc =
      Fin.castAdd (T.n + 1) (Fin.last (S.n + 1)) by apply Fin.ext; simp]
    rw [concatVertex_left, S.vertex_last, leftHalf_one,
      show (Fin.castSucc (0 : Fin (T.n + 1))) = 0 by apply Fin.ext; rfl,
      T.vertex_zero, rightHalf_zero]
  · convert concatVertex_right S T j.castSucc using 1
    · apply congrArg (concatVertex S T)
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ, Fin.val_castSucc]
      omega

theorem concatVertex_segment_right_succ (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (i : Fin (T.n + 1)) :
    concatVertex S T (Fin.cast (by omega) (Fin.natAdd (S.n + 1) i).succ) =
      rightHalf (T.vertex i.succ) := by
  convert concatVertex_right S T i using 1
  apply congrArg (concatVertex S T)
  apply Fin.ext
  simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
  omega

theorem concatSegment_mem (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) :
    ∀ k : Fin ((S.n + 1) + (T.n + 1)),
    Set.Icc (concatVertex S T (Fin.cast (by omega) k.castSucc))
      (concatVertex S T (Fin.cast (by omega) k.succ)) ⊆
      (p.trans q) ⁻¹' twoChart U V (concatSide S T k) := by
  intro k
  refine Fin.addCases
    (motive := fun k : Fin ((S.n + 1) + (T.n + 1)) ↦
      Set.Icc (concatVertex S T (Fin.cast (by omega) k.castSucc))
        (concatVertex S T (Fin.cast (by omega) k.succ)) ⊆
          (p.trans q) ⁻¹' twoChart U V (concatSide S T k)) ?_ ?_ k
  · intro i t ht
    simp only [concatSide_left] at ⊢
    rw [concatVertex_segment_left_castSucc, concatVertex_segment_left_succ] at ht
    rcases ht with ⟨ht1, ht2⟩
    change (p.trans q) t ∈ twoChart U V (S.side i)
    rw [Path.trans_apply]
    split_ifs with h
    · apply S.segment_mem i
      constructor
      · change (S.vertex i.castSucc : ℝ) ≤ 2 * (t : ℝ)
        change ((S.vertex i.castSucc : ℝ) / 2) ≤ (t : ℝ) at ht1
        linarith
      · change 2 * (t : ℝ) ≤ (S.vertex i.succ : ℝ)
        change (t : ℝ) ≤ ((S.vertex i.succ : ℝ) / 2) at ht2
        linarith
    · exfalso
      apply h
      change (t : ℝ) ≤ 1 / 2
      calc
        (t : ℝ) ≤ (S.vertex i.succ : ℝ) / 2 := ht2
        _ ≤ 1 / 2 := by linarith [(S.vertex i.succ).2.2]
  · intro i t ht
    simp only [concatSide_right] at ⊢
    rw [concatVertex_segment_right_castSucc, concatVertex_segment_right_succ] at ht
    rcases ht with ⟨ht1, ht2⟩
    change (p.trans q) t ∈ twoChart U V (T.side i)
    rw [Path.trans_apply]
    split_ifs with h
    · have hlower : (1 : ℝ) / 2 ≤ (t : ℝ) := by
        calc
          (1 : ℝ) / 2 ≤ (1 + (T.vertex i.castSucc : ℝ)) / 2 := by
            linarith [(T.vertex i.castSucc).2.1]
          _ ≤ (t : ℝ) := ht1
      have : (t : ℝ) = 1 / 2 := le_antisymm h hlower
      have hm := T.segment_mem i (show (0 : unitInterval) ∈
          Set.Icc (T.vertex i.castSucc) (T.vertex i.succ) by
        constructor
        · change (T.vertex i.castSucc : ℝ) ≤ 0
          change (1 + (T.vertex i.castSucc : ℝ)) / 2 ≤ (t : ℝ) at ht1
          linarith
        · exact (T.vertex i.succ).2.1)
      simpa [this, p.target, q.source] using hm
    · apply T.segment_mem i
      constructor
      · change (T.vertex i.castSucc : ℝ) ≤ 2 * (t : ℝ) - 1
        change (1 + (T.vertex i.castSucc : ℝ)) / 2 ≤ (t : ℝ) at ht1
        linarith
      · change 2 * (t : ℝ) - 1 ≤ (T.vertex i.succ : ℝ)
        change (t : ℝ) ≤ (1 + (T.vertex i.succ : ℝ)) / 2 at ht2
        linarith

/-- Concatenating two subordinate subdivisions gives a genuine subordinate
subdivision of the concatenated path. -/
def concatSubdivision (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) : PathTwoOpenSubdivision (p.trans q) U V where
  n := S.n + T.n + 1
  vertex := fun i ↦ concatVertex S T (Fin.cast (by omega) i)
  side := fun i ↦ concatSide S T (Fin.cast (by omega) i)
  vertex_zero := by simpa using concatVertex_zero S T
  vertex_last := by simpa using concatVertex_last S T
  monotone_vertex := by
    intro i j hij
    apply concatVertex_monotone S T
    exact hij
  segment_mem := by
    intro k
    simpa using concatSegment_mem S T (Fin.cast (by omega) k)

@[simp] theorem concatSubdivision_n (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) : (concatSubdivision S T).n = S.n + T.n + 1 := rfl

@[simp] theorem concatSubdivision_vertex (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (i : Fin ((concatSubdivision S T).n + 2)) :
    (concatSubdivision S T).vertex i = concatVertex S T
      (Fin.cast (by simp [concatSubdivision]; omega) i) := rfl

@[simp] theorem concatSubdivision_side (S : PathTwoOpenSubdivision p U V)
    (T : PathTwoOpenSubdivision q U V) (i : Fin ((concatSubdivision S T).n + 1)) :
    (concatSubdivision S T).side i = concatSide S T
      (Fin.cast (by simp [concatSubdivision]; omega) i) := rfl

#print axioms concatVertex
#print axioms concatSide
#print axioms concatVertex_zero
#print axioms concatVertex_last
#print axioms concatVertex_monotone
#print axioms trans_subpath_left_apply
#print axioms trans_subpath_right_apply
#print axioms concatSegment_mem
#print axioms concatSubdivision

end ConstructionTargets.PathSubdivisionConcatenation
