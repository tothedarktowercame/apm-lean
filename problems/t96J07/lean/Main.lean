import Mathlib

/-!
# APM t96J07 — a diagonal map of real projective three-space

## Statement repairs

The nonzero-vector implication now encloses the axis equivalence explicitly.
The old parsed clause and its zero-vector refutation are retained below.
This repairs the statement; it is not a proof of the old frozen theorem.

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
      (apm_t96j07_projectivelyEq x (apm_t96j07_A x) ↔
        ∃ i : Fin 4, apm_t96j07_projectivelyEq x (apm_t96j07_axis i))) ∧
    apm_t96j07_localIndex 0 = -1 ∧
    apm_t96j07_localIndex 1 = 1 ∧
    apm_t96j07_localIndex 2 = -1 ∧
    apm_t96j07_localIndex 3 = 1 ∧
    (∑ i : Fin 4, apm_t96j07_localIndex i) = 0 := by
  constructor
  · intro x hx
    constructor
    · rintro ⟨c, hc, he⟩
      obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
        by_contra h
        apply hx
        funext i
        simpa using not_exists.mp h i
      have hci : (i.val + 1 : ℝ) = c := by
        apply mul_right_cancel₀ hi
        exact congrFun he i
      have hz : ∀ j, j ≠ i → x j = 0 := by
        intro j hji
        have hj := congrFun he j
        change (j.val + 1 : ℝ) * x j = c * x j at hj
        rw [← hci] at hj
        have hne : (j.val + 1 : ℝ) ≠ (i.val + 1 : ℝ) := by
          intro h
          have : j.val = i.val := by exact_mod_cast (add_right_cancel h)
          exact hji (Fin.ext this)
        exact (mul_eq_mul_right_iff.mp hj).resolve_left hne
      refine ⟨i, (x i)⁻¹, inv_ne_zero hi, ?_⟩
      funext j
      by_cases hji : j = i
      · subst j
        simp [apm_t96j07_axis, hi]
      · simp [apm_t96j07_axis, hji, hz j hji]
    · rintro ⟨i, c, hc, he⟩
      refine ⟨(i.val + 1 : ℝ), by positivity, ?_⟩
      funext j
      by_cases hji : j = i
      · subst j
        rfl
      · have hj := congrFun he j
        have hz : x j = 0 := by
          have : c * x j = 0 := by simpa [apm_t96j07_axis, hji] using hj.symm
          exact (mul_eq_zero.mp this).resolve_left hc
        simp [apm_t96j07_A, hz]
  · have h0 : (Finset.univ : Finset (Fin 4)).erase 0 = {1, 2, 3} := by decide
    have h1 : (Finset.univ : Finset (Fin 4)).erase 1 = {0, 2, 3} := by decide
    have h2 : (Finset.univ : Finset (Fin 4)).erase 2 = {0, 1, 3} := by decide
    have h3 : (Finset.univ : Finset (Fin 4)).erase 3 = {0, 1, 2} := by decide
    norm_num [apm_t96j07_localIndex, apm_t96j07_localDeterminant,
      Fin.sum_univ_succ, show (Fin.succ (2 : Fin 3)) = (3 : Fin 4) from rfl, h0, h1, h2, h3, Finset.prod_insert,
      show (0 : Fin 4) ≠ 1 by decide, show (0 : Fin 4) ≠ 2 by decide,
      show (0 : Fin 4) ≠ 3 by decide, show (1 : Fin 4) ≠ 2 by decide,
      show (1 : Fin 4) ≠ 3 by decide, show (2 : Fin 4) ≠ 3 by decide]

#print axioms apm_t96j07_not_fixed_axis_clause
#print axioms apm_t96j07
