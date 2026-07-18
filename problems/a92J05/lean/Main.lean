import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# APM a92J05: Counting roots outside the unit disk via Rouché

**Problem.** How many roots (with multiplicity) of z¹⁰ + 5z³ + 2z + 1 = 0
lie in {|z| > 1}? **Answer: 7.** By Rouché on |z| = 1.

## Statement repair note

Mathlib does not have Rouché's theorem. We prove the supporting lemmas
and leave the Rouché application as a genuine sorry boundary.
-/

set_option linter.unusedVariables false in
noncomputable section

open Complex Polynomial

namespace ApmCanaries.A92J05

noncomputable def p : ℂ[X] := X ^ 10 + C (5 : ℂ) * X ^ 3 + C (2 : ℂ) * X + C (1 : ℂ)
noncomputable def g : ℂ[X] := C (5 : ℂ) * X ^ 3
noncomputable def h : ℂ[X] := X ^ 10 + C (2 : ℂ) * X + C (1 : ℂ)

lemma aeval_g (z : ℂ) : aeval z g = 5 * z ^ 3 := by simp [g]
lemma aeval_h (z : ℂ) : aeval z h = z ^ 10 + 2 * z + 1 := by simp [h]
lemma aeval_p (z : ℂ) : aeval z p = z ^ 10 + 5 * z ^ 3 + 2 * z + 1 := by simp [p]

/-- Auxiliary: if ‖z‖ = 1 then ‖z^n‖ = 1. -/
lemma norm_pow_of_norm_one (z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) : ‖z ^ n‖ = 1 := by
  rw [norm_pow, hz]; simp

/-- Auxiliary: if ‖z‖ = 1 then ‖(c : ℂ) * z^n‖ = ‖c‖. -/
lemma norm_smul_pow_of_norm_one (z : ℂ) (hz : ‖z‖ = 1) (c : ℂ) (n : ℕ) :
    ‖c * z ^ n‖ = ‖c‖ := by
  rw [norm_mul, norm_pow, hz, one_pow, mul_one]

/-- On |z| = 1: |h(z)| ≤ 4 < 5 = |g(z)|. -/
lemma rouche_condition (z : ℂ) (hz : ‖z‖ = 1) : ‖aeval z h‖ < ‖aeval z g‖ := by
  rw [aeval_h, aeval_g]
  have h4 : ‖z ^ 10 + 2 * z + 1‖ ≤ 4 := by
    have h01 : ‖(z ^ 10 + 2 * z) + (1 : ℂ)‖ ≤ ‖z ^ 10 + 2 * z‖ + ‖(1 : ℂ)‖ :=
      norm_add_le _ _
    have h02 : ‖z ^ 10 + (2 : ℂ) * z‖ ≤ ‖z ^ 10‖ + ‖(2 : ℂ) * z‖ :=
      norm_add_le _ _
    have h03 : ‖z ^ 10‖ = (1 : ℝ) := norm_pow_of_norm_one z hz 10
    have h04 : ‖(2 : ℂ) * z‖ = 2 := by
      have : z = z ^ 1 := (pow_one z).symm
      rw [this, norm_smul_pow_of_norm_one z hz (2:ℂ) 1]; norm_num
    have h06 : ‖(1 : ℂ)‖ = 1 := by norm_num
    -- z^10 + 2*z = z^10 + (2:ℂ)*z definitionally
    linarith [h01, h02, h03, h04, h06]
  have h5 : ‖(5 : ℂ) * z ^ 3‖ = 5 := by
    rw [norm_smul_pow_of_norm_one z hz (5:ℂ) 3]; norm_num
  linarith

/-- p has no roots on |z| = 1.

    If |z| = 1 and p(z) = 0: z¹⁰+1 = -(5z³+2z), so |z¹⁰+1| = |5z³+2z| ≥ 3,
    but |z¹⁰+1| ≤ 2. Contradiction. -/
lemma p_no_roots_on_circle (z : ℂ) (hz : ‖z‖ = 1) : aeval z p ≠ 0 := by
  intro hzero
  rw [aeval_p] at hzero
  -- z^10 + 1 = -(5z^3 + 2z) from p(z) = 0
  have heq : z ^ 10 + (1 : ℂ) = -((5 : ℂ) * z ^ 3 + (2 : ℂ) * z) := by
    have hconv : z ^ 10 + (1 : ℂ) + ((5 : ℂ) * z ^ 3 + (2 : ℂ) * z) =
        z ^ 10 + 5 * z ^ 3 + 2 * z + 1 := by push_cast; ring
    have hsum : z ^ 10 + (1 : ℂ) + ((5 : ℂ) * z ^ 3 + (2 : ℂ) * z) = 0 := by
      rw [hconv]; exact hzero
    -- a + b = 0 implies a = -b
    calc z ^ 10 + (1 : ℂ)
        = z ^ 10 + (1 : ℂ) + ((5 : ℂ) * z ^ 3 + (2 : ℂ) * z) -
            ((5 : ℂ) * z ^ 3 + (2 : ℂ) * z) := by ring
      _ = 0 - ((5 : ℂ) * z ^ 3 + (2 : ℂ) * z) := by rw [hsum]
      _ = -((5 : ℂ) * z ^ 3 + (2 : ℂ) * z) := by ring
  -- |z^10 + 1| ≤ 2
  have hle : ‖z ^ 10 + (1 : ℂ)‖ ≤ 2 := by
    have h01 : ‖z ^ 10 + (1 : ℂ)‖ ≤ ‖z ^ 10‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    have h02 : ‖z ^ 10‖ = (1 : ℝ) := norm_pow_of_norm_one z hz 10
    have h03 : ‖(1 : ℂ)‖ = 1 := by norm_num
    linarith
  -- |5z^3 + 2z| ≥ 3 via |5z^3| ≤ |5z^3 + 2z| + |2z|
  have hge : 3 ≤ ‖(5 : ℂ) * z ^ 3 + (2 : ℂ) * z‖ := by
    have h5z3 : ‖(5 : ℂ) * z ^ 3‖ = 5 := by
      rw [norm_smul_pow_of_norm_one z hz (5:ℂ) 3]; norm_num
    have h2z : ‖(2 : ℂ) * z‖ = 2 := by
      have : z = z ^ 1 := (pow_one z).symm
      rw [this, norm_smul_pow_of_norm_one z hz (2:ℂ) 1]; norm_num
    -- |5z^3| = |5z^3 + 2z - 2z| ≤ |5z^3 + 2z| + |2z|
    have key : ‖(5 : ℂ) * z ^ 3‖ ≤ ‖(5 : ℂ) * z ^ 3 + (2 : ℂ) * z‖ + ‖(2 : ℂ) * z‖ := by
      have htri : ‖((5 : ℂ) * z ^ 3 + (2 : ℂ) * z) + -((2 : ℂ) * z)‖ ≤
          ‖(5 : ℂ) * z ^ 3 + (2 : ℂ) * z‖ + ‖-((2 : ℂ) * z)‖ := norm_add_le _ _
      rw [norm_neg, add_neg_cancel_right] at htri
      linarith
    linarith
  -- |z^10 + 1| = |5z^3 + 2z| ≥ 3 but ≤ 2
  -- From heq: -(z^10 + 1) = 5z^3 + 2z
  have hneg : (5 : ℂ) * z ^ 3 + (2 : ℂ) * z = -(z ^ 10 + (1 : ℂ)) := by
    have h1 : z ^ 10 + (1 : ℂ) + ((5 : ℂ) * z ^ 3 + (2 : ℂ) * z) = 0 := by
      have : z ^ 10 + (1 : ℂ) + ((5 : ℂ) * z ^ 3 + (2 : ℂ) * z) =
          z ^ 10 + 5 * z ^ 3 + 2 * z + 1 := by push_cast; ring
      rw [this]; exact hzero
    have h2 : (5 : ℂ) * z ^ 3 + (2 : ℂ) * z = -(z ^ 10 + (1 : ℂ)) := by
      calc (5 : ℂ) * z ^ 3 + (2 : ℂ) * z
          = -(z ^ 10 + (1 : ℂ)) + ((5 : ℂ) * z ^ 3 + (2 : ℂ) * z + (z ^ 10 + (1 : ℂ))) := by ring
        _ = -(z ^ 10 + (1 : ℂ)) + 0 := by rw [← h1]; ring
        _ = -(z ^ 10 + (1 : ℂ)) := by ring
    exact h2
  rw [hneg, norm_neg] at hge
  linarith

/-- Main theorem: p has exactly 7 roots in {|z| > 1}.

    **SORRY BOUNDARY:** Uses Rouché's theorem (not in Mathlib). The proven
    lemmas (Rouché condition, no roots on circle) reduce the gap to the
    single Rouché application: p has 3 roots inside {|z| < 1} (same as
    5z³ by Rouché), and 10 − 3 = 7 outside. -/
theorem roots_outside_unit_disk :
    (p.roots.filter (fun z => 1 < ‖z‖)).card = 7 := by
  sorry

end ApmCanaries.A92J05
