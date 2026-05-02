import Mathlib

open Complex Polynomial Set Metric

noncomputable section

/-- The polynomial f(z) = z⁵ + 15z + 1. -/
def apm_a97A08_f : Polynomial ℂ :=
  Polynomial.X ^ 5 + 15 * Polynomial.X + 1

/-- Helper: |15z + 1| < |z⁵| on the circle |z| = 2. -/
theorem apm_a97A08_rouche_outer
    (z : ℂ) (hz : ‖z‖ = 2) :
    ‖15 * z + 1‖ < ‖z ^ 5‖ := by
  have h1 : ‖15 * z + 1‖ ≤ 31 := by
    calc
      ‖15 * z + 1‖ ≤ ‖15 * z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = 15 * ‖z‖ + 1 := by simp
      _ = 31 := by rw [hz]; norm_num
  have h2 : ‖z ^ 5‖ = 32 := by
    rw [norm_pow, hz]
    norm_num
  exact lt_of_le_of_lt h1 (by simpa [h2] using (show (31 : ℝ) < 32 by norm_num))

/-- Helper: |z⁵ + 1| < |15z| on the circle |z| = 3/2. -/
theorem apm_a97A08_rouche_inner
    (z : ℂ) (hz : ‖z‖ = 3/2) :
    ‖z ^ 5 + 1‖ < ‖15 * z‖ := by
  have h1 : ‖z ^ 5 + 1‖ ≤ (3 / 2 : ℝ) ^ 5 + 1 := by
    calc
      ‖z ^ 5 + 1‖ ≤ ‖z ^ 5‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖z‖ ^ 5 + 1 := by simp [norm_pow]
      _ = (3 / 2 : ℝ) ^ 5 + 1 := by rw [hz]
  have h2 : ‖15 * z‖ = 15 * (3 / 2 : ℝ) := by
    rw [norm_mul, hz]
    norm_num
  have hlt : ((3 / 2 : ℝ) ^ 5 + 1) < 15 * (3 / 2 : ℝ) := by
    norm_num
  rw [h2]
  exact lt_of_le_of_lt h1 hlt

/-- f has no zeros on |z| = 2 (so the count on the open disk is well-defined). -/
theorem apm_a97A08_no_zeros_outer
    (z : ℂ) (hz : ‖z‖ = 2) :
    apm_a97A08_f.aeval z ≠ 0 := by
  intro hzero
  have hzero' : z ^ 5 + 15 * z + 1 = 0 := by
    simpa [apm_a97A08_f, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm] using hzero
  have hnorm : ‖15 * z + 1‖ = ‖z ^ 5‖ := by
    have hz5 : z ^ 5 = -(15 * z + 1) := by
      apply eq_neg_of_add_eq_zero_left
      simpa [add_assoc, add_comm, add_left_comm] using hzero'
    rw [hz5, norm_neg]
  nlinarith [apm_a97A08_rouche_outer z hz, hnorm]

/-- f has no zeros on |z| = 3/2. -/
theorem apm_a97A08_no_zeros_inner
    (z : ℂ) (hz : ‖z‖ = 3/2) :
    apm_a97A08_f.aeval z ≠ 0 := by
  intro hzero
  have hzero' : z ^ 5 + 15 * z + 1 = 0 := by
    simpa [apm_a97A08_f, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm] using hzero
  have hnorm : ‖z ^ 5 + 1‖ = ‖15 * z‖ := by
    have hz5 : z ^ 5 + 1 = -(15 * z) := by
      apply eq_neg_of_add_eq_zero_left
      simpa [add_assoc, add_comm, add_left_comm] using hzero'
    rw [hz5, norm_neg]
  nlinarith [apm_a97A08_rouche_inner z hz, hnorm]

/-- f has 5 zeros (with multiplicity) in the open disk |z| < 2. -/
theorem apm_a97A08_count_outer :
    (apm_a97A08_f.roots.filter (fun z => ‖z‖ < 2)).card = 5 := by sorry

/-- f has 1 zero in the open disk |z| < 3/2. -/
theorem apm_a97A08_count_inner :
    (apm_a97A08_f.roots.filter (fun z => ‖z‖ < 3/2)).card = 1 := by sorry

/-- Main theorem: the count in disk |z| < 2 is 5, and the count in
    annulus 3/2 < |z| < 2 is 4. -/
theorem apm_a97A08_main :
    (apm_a97A08_f.roots.filter (fun z => ‖z‖ < 2)).card = 5 ∧
    (apm_a97A08_f.roots.filter (fun z => 3/2 < ‖z‖ ∧ ‖z‖ < 2)).card = 4 := by sorry
