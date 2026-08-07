import Mathlib

/-!
# APM t96J07 — a diagonal map of real projective three-space

## Statement repairs

None.

## Encoding note

A projective point is represented by a nonzero vector modulo the explicit
relation “differ by a nonzero scalar.” Fixed points are therefore eigenlines;
the local indices are the signs of `det(I-df)` in the four affine charts.
-/

abbrev apm_t96j07_V := Fin 4 → ℝ

def apm_t96j07_projectivelyEq (x y : apm_t96j07_V) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧ y = c • x

def apm_t96j07_A (x : apm_t96j07_V) : apm_t96j07_V :=
  fun i => (i.val + 1 : ℝ) * x i

def apm_t96j07_axis (i : Fin 4) : apm_t96j07_V :=
  fun j => if j = i then 1 else 0

noncomputable def apm_t96j07_localDeterminant (i : Fin 4) : ℝ :=
  ∏ j ∈ Finset.univ.erase i,
    (1 - (j.val + 1 : ℝ) / (i.val + 1 : ℝ))

noncomputable def apm_t96j07_localIndex (i : Fin 4) : ℤ :=
  if 0 < apm_t96j07_localDeterminant i then 1 else -1

/-- The first frozen conjunct is refuted at the zero vector. -/
lemma apm_t96j07_not_fixed_axis_clause :
    ¬(∀ x : apm_t96j07_V,
      (x ≠ 0 → apm_t96j07_projectivelyEq x (apm_t96j07_A x)) ↔
        ∃ i : Fin 4, apm_t96j07_projectivelyEq x (apm_t96j07_axis i)) := by
  intro h
  have hzero := (h 0).mp (by simp)
  rcases hzero with ⟨i, c, hc, haxis⟩
  have hi := congrFun haxis i
  simp [apm_t96j07_axis] at hi

theorem apm_t96j07 :
    (∀ x : apm_t96j07_V, x ≠ 0 →
      apm_t96j07_projectivelyEq x (apm_t96j07_A x) ↔
        ∃ i : Fin 4, apm_t96j07_projectivelyEq x (apm_t96j07_axis i)) ∧
    apm_t96j07_localIndex 0 = -1 ∧
    apm_t96j07_localIndex 1 = 1 ∧
    apm_t96j07_localIndex 2 = -1 ∧
    apm_t96j07_localIndex 3 = 1 ∧
    (∑ i : Fin 4, apm_t96j07_localIndex i) = 0 := by
  -- Boundary: the frozen clause parses as
  -- `∀ x, (x ≠ 0 → projectivelyEq x (A x)) ↔ ∃ i, projectivelyEq x (axis i)`.
  -- At `x = 0` its left side is vacuously true, while its right side is false
  -- because `axis i ≠ 0` but every nonzero scalar multiple of `0` is `0`.
  -- Thus the statement is false.  The intended route (coordinate cancellation
  -- using `mul_right_cancel₀`, followed by determinant evaluation with
  -- `norm_num`) applies only after parenthesizing the equivalence under `x ≠ 0`.
  -- Closer hop 1 verifies the defect inside Lean:
  -- `apm_t96j07_not_fixed_axis_clause` proves the negation of the first
  -- conjunct exactly as parsed, by specializing at the zero vector and
  -- evaluating the alleged axis equality at its distinguished coordinate.
  -- `LEMMA-INDEX.md`, `ConstructionTargets/`, sibling artifacts, and git
  -- history contain no alternate encoding or convention that changes this
  -- contradiction. The protocol freezes the statement, so it cannot be
  -- repaired by moving the implication inside the quantified proposition.
  sorry
