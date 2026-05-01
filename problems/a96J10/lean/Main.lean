import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.Bernoulli

open Complex Set

noncomputable section

/-- The function f(z) = z/(e^{2πz} - 1) + z/2 extended by f(0) = 1/(2π) + 0
    is analytic on the open unit disk. -/
def apm_a96J10_f (z : ℂ) : ℂ :=
  if z = 0 then 1 / (2 * Real.pi) else z / (Complex.exp (2 * Real.pi * z) - 1) + z / 2

lemma exp_two_pi_mul_sub_ne_zero_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    Complex.exp (2 * (Real.pi : ℂ) * z) - 1 ≠ 0 := by
  intro h
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * z) = 1 := sub_eq_zero.mp h
  rcases Complex.exp_eq_one_iff.mp hexp with ⟨n, hn⟩
  have hRe : z.re = 0 := by
    have hre := congrArg Complex.re hn
    simp [Complex.mul_re, Complex.mul_im] at hre
    nlinarith [Real.pi_pos]
  have hIm : z.im = n := by
    have him := congrArg Complex.im hn
    simp [Complex.mul_re, Complex.mul_im, hRe] at him
    nlinarith [Real.pi_pos]
  have hzI : z = n * Complex.I := by
    apply Complex.ext <;> simp [hRe, hIm]
  by_cases hn0 : n = 0
  · exact hz0 (by simp [hzI, hn0])
  · have hnorm_ge : (1 : ℝ) ≤ ‖z‖ := by
      rw [hzI, norm_mul, norm_I, Complex.norm_intCast]
      simpa using (show (1 : ℝ) ≤ |(n : ℝ)| from by exact_mod_cast Int.one_le_abs hn0)
    linarith

def apm_a96J10_q : ℂ → ℂ := dslope Complex.exp 0

lemma apm_a96J10_q_analytic : AnalyticOn ℂ apm_a96J10_q univ := by
  refine DifferentiableOn.analyticOn ?_ isOpen_univ
  refine (Complex.differentiableOn_dslope (s := (Set.univ : Set ℂ)) (c := 0) ?_).2 ?_
  · simp
  · intro z hz
    exact (differentiableAt_exp : DifferentiableAt ℂ Complex.exp z).differentiableWithinAt

lemma apm_a96J10_q_of_ne (z : ℂ) (hz0 : z ≠ 0) :
    apm_a96J10_q z = (Complex.exp z - 1) / z := by
  rw [apm_a96J10_q, dslope_of_ne _ hz0]
  simp [slope, div_eq_mul_inv, mul_comm]

lemma apm_a96J10_q_nonzero_on_ball {z : ℂ} (hz : ‖z‖ < 1) :
    apm_a96J10_q ((2 * Real.pi : ℂ) * z) ≠ 0 := by
  by_cases hz0 : z = 0
  · simp [apm_a96J10_q, hz0, dslope_same]
  · have harg0 : (2 * (Real.pi : ℂ) * z) ≠ 0 := by
      simpa [hz0, Real.pi_ne_zero]
    rw [apm_a96J10_q_of_ne _ harg0]
    apply div_ne_zero
    · exact exp_two_pi_mul_sub_ne_zero_of_norm_lt_one hz hz0
    · exact harg0

theorem apm_a96J10_f_analytic :
    AnalyticOn ℂ apm_a96J10_f (Metric.ball (0:ℂ) 1) := by
  have hEq :
      apm_a96J10_f =
        (fun w : ℂ => (2 * Real.pi : ℂ)⁻¹ * (apm_a96J10_q ((2 * Real.pi : ℂ) * w))⁻¹ + w / 2) := by
    funext w
    by_cases hw0 : w = 0
    · simp [apm_a96J10_f, hw0, apm_a96J10_q, dslope_same]
    · have harg0 : (2 * (Real.pi : ℂ) * w) ≠ 0 := by
        simpa [hw0, Real.pi_ne_zero]
      rw [apm_a96J10_f, if_neg hw0, apm_a96J10_q_of_ne _ harg0]
      field_simp [harg0]
  rw [hEq]
  intro z hz
  have hnorm : ‖z‖ < 1 := by simpa using hz
  have hqAt : AnalyticAt ℂ apm_a96J10_q ((2 * Real.pi : ℂ) * z) := by
    simpa [analyticWithinAt_univ] using apm_a96J10_q_analytic ((2 * Real.pi : ℂ) * z) (by simp)
  have hlin : AnalyticAt ℂ (fun w : ℂ => (2 * Real.pi : ℂ) * w) z := by
    simpa using
      (analyticAt_const.mul analyticAt_id : AnalyticAt ℂ (fun w : ℂ => (2 * Real.pi : ℂ) * w) z)
  have hcomp : AnalyticAt ℂ (fun w : ℂ => apm_a96J10_q ((2 * Real.pi : ℂ) * w)) z :=
    hqAt.comp hlin
  have hcomp_nz : apm_a96J10_q ((2 * Real.pi : ℂ) * z) ≠ 0 := apm_a96J10_q_nonzero_on_ball hnorm
  have hmain :
      AnalyticAt ℂ (fun w : ℂ => (2 * Real.pi : ℂ)⁻¹ * (apm_a96J10_q ((2 * Real.pi : ℂ) * w))⁻¹ + w / 2) z := by
    refine (analyticAt_const.mul ?_).add ?_
    · exact hcomp.inv hcomp_nz
    · simpa [div_eq_mul_inv, mul_comm] using
        ((analyticAt_id).mul analyticAt_const : AnalyticAt ℂ (fun w : ℂ => w * ((2 : ℂ)⁻¹)) z)
  exact hmain.analyticWithinAt

/-- The Bernoulli-type identity: f is even on Δ. -/
theorem apm_a96J10_f_even
    (z : ℂ) (hz : ‖z‖ < 1) :
    apm_a96J10_f (-z) = apm_a96J10_f z := by
  by_cases hz0 : z = 0
  · simp [apm_a96J10_f, hz0]
  · have h1 : Complex.exp (2 * (Real.pi : ℂ) * z) - 1 ≠ 0 :=
      exp_two_pi_mul_sub_ne_zero_of_norm_lt_one hz hz0
    let E : ℂ := Complex.exp (2 * (Real.pi : ℂ) * z)
    have hE0 : E ≠ 0 := by
      simpa [E] using Complex.exp_ne_zero (2 * (Real.pi : ℂ) * z)
    have hE1 : E - 1 ≠ 0 := by
      simpa [E, sub_eq_add_neg] using h1
    have hnegarg : 2 * (Real.pi : ℂ) * (-z) = -(2 * (Real.pi : ℂ) * z) := by
      ring
    have hrewrite :
        (-z) / (Complex.exp (2 * (Real.pi : ℂ) * (-z)) - 1) = z * E / (E - 1) := by
      rw [hnegarg, Complex.exp_neg, div_eq_mul_inv]
      change -z * (E⁻¹ - 1)⁻¹ = z * E / (E - 1)
      have h1' : 1 - E ≠ 0 := sub_ne_zero.mpr <| by simpa using (sub_ne_zero.mp hE1).symm
      field_simp [hE0, h1', hE1]
      ring
    have hsplit : E / (E - 1) = 1 + 1 / (E - 1) := by
      field_simp [hE1]
      ring
    calc
      apm_a96J10_f (-z)
          = (-z) / (Complex.exp (2 * (Real.pi : ℂ) * (-z)) - 1) + (-z) / 2 := by
              simp [apm_a96J10_f, hz0, neg_eq_zero]
      _ = z * E / (E - 1) - z / 2 := by
              rw [hrewrite]
              ring
      _ = z * (E / (E - 1)) - z / 2 := by ring
      _ = z * (1 + 1 / (E - 1)) - z / 2 := by rw [hsplit]
      _ = z / (E - 1) + z / 2 := by ring
      _ = apm_a96J10_f z := by
              simp [apm_a96J10_f, hz0, E]

/-- An analytic even function on a disk factors through z². -/
theorem apm_a96J10_even_factors
    (h : ℂ → ℂ) (hh : AnalyticOn ℂ h (Metric.ball (0:ℂ) 1))
    (heven : ∀ z, ‖z‖ < 1 → h (-z) = h z) :
    ∃ g : ℂ → ℂ, AnalyticOn ℂ g (Metric.ball (0:ℂ) 1) ∧
      ∀ z, ‖z‖ < 1 → g (z ^ 2) = h z := by sorry

/-- Main theorem: f(z) = z/(e^{2πz}-1) + z/2 factors as g(z²) for some
    analytic g on the open unit disk. -/
theorem apm_a96J10_main :
    ∃ g : ℂ → ℂ, AnalyticOn ℂ g (Metric.ball (0:ℂ) 1) ∧
      ∀ z : ℂ, ‖z‖ < 1 → z ≠ 0 →
        g (z ^ 2) = z / (Complex.exp (2 * Real.pi * z) - 1) + z / 2 := by
  rcases apm_a96J10_even_factors apm_a96J10_f apm_a96J10_f_analytic
      (fun z hz => apm_a96J10_f_even z hz) with ⟨g, hg, hfactor⟩
  refine ⟨g, hg, ?_⟩
  intro z hz hz0
  calc
    g (z ^ 2) = apm_a96J10_f z := hfactor z hz
    _ = z / (Complex.exp (2 * Real.pi * z) - 1) + z / 2 := by
      simp [apm_a96J10_f, hz0]
