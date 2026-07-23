import Mathlib
import ApmCanaries.Frames.A96J01.Apm_v2_a96J01_1774999742972.Scratch

noncomputable section

namespace ApmCanaries.Frames.A96J01.Apm_v2_a96J01_1774999742972.Main

open scoped BigOperators Topology

notation "I" => Set.Icc (0 : ℝ) 1

/-- The left endpoint of the n-th support interval. -/
def left (n : ℕ) : ℝ := 1 - (1 / ((2 : ℝ) ^ (n + 1)))
/-- The right endpoint of the n-th support interval. -/
def right (n : ℕ) : ℝ := 1 - (1 / ((2 : ℝ) ^ (n + 2)))
/-- Midpoint of the support interval. -/
def center (n : ℕ) : ℝ := (left n + right n) / 2
/-- Half-width of the support interval. -/
def radius (n : ℕ) : ℝ := (right n - left n) / 2

lemma left_nonneg (n : ℕ) : 0 ≤ left n := by
  have : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ (n + 1) := by positivity
  simpa [left] using sub_nonneg.mpr this

lemma right_le_one (n : ℕ) : right n ≤ 1 := by
  have : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ (n + 2) := by positivity
  simpa [right] using (sub_le_iff_le_add).mpr this

lemma interval_subset : ∀ n, left n ≤ right n := by
  intro n; simp [left, right, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, pow_add,
    pow_succ, two_mul, add_comm]

lemma radius_pos (n : ℕ) : 0 < radius n := by
  have h : left n < right n := by
    have := interval_subset n
    exact lt_of_le_of_lt this (lt_of_le_of_lt this ?_)
  have : 0 < right n - left n := sub_pos.mpr h
  simpa [radius, half_lt_self_iff] using (half_pos this)

/-- Raw triangular profile centered at `center n`. -/
def raw (n : ℕ) (x : ℝ) : ℝ := 1 - |x - center n| / radius n
/-- Nonnegative tent bump. -/
def bump (n : ℕ) (x : ℝ) : ℝ := max (raw n x) 0

lemma bump_nonneg (n : ℕ) (x : ℝ) : 0 ≤ bump n x := by
  unfold bump; exact le_max_right _ _

lemma bump_le_one (n : ℕ) (x : ℝ) : bump n x ≤ 1 := by
  unfold bump raw
  have h := max_le_iff.mpr
    ⟨sub_le_iff_le_add'.mp (by have := abs_nonneg (x - center n); positivity), le_of_eq rfl⟩
  simpa using h

lemma bump_zero_of_far {n : ℕ} {x : ℝ} (hx : |x - center n| ≥ radius n) : bump n x = 0 := by
  unfold bump raw
  have : 1 - |x - center n| / radius n ≤ 0 := by
    have := sub_nonpos.mpr ?_
    simpa using this
  · have := max_eq_right (show (1 - |x - center n| / radius n) ≤ 0 by exact this)
    simpa [this]
  have hpos : 0 < radius n := radius_pos n
  have := (div_le_one_of_le hpos).mpr hx
  simpa using this

/-- The n-th bump as a continuous function on `[0,1]`. -/
def f (n : ℕ) : C(I, ℝ) :=
{ toFun := fun x => (1 / (n + 1 : ℝ)) * bump n x,
  continuous_toFun := by
    have hcont : Continuous fun x : ℝ => bump n x :=
      (continuous_const.sub ((Continuous.abs Continuous.subtype_val).div_const _)).max
        continuous_const
    simpa using hcont.comp continuous_subtype_val,
  map_mul := by intro x y; simp,
  map_add := by intro x y; simp }

end ApmCanaries.Frames.A96J01.Apm_v2_a96J01_1774999742972.Main
