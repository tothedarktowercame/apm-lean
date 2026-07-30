import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set Real

noncomputable section

/-! # APM a02J05: ∫_{-∞}^{∞} sin(x)/x dx = π

  The Dirichlet integral, computed via contour integration.

  Proof outline:
  1. Consider f(z) = e^{iz}/z on indented contour (avoiding pole at 0)
  2. Cauchy: total contour integral = 0 (no poles enclosed)
  3. Large semicircle → 0 (Jordan's lemma)
  4. Small semicircle → -πi (half-residue)
  5. Real axis gives PV ∫ e^{ix}/x dx = πi
  6. Take Im: ∫ sin(x)/x dx = π

  Lean status: statement + answer, proof via contour integration
  is beyond Mathlib's current complex analysis API (no Jordan's lemma,
  no indented contour machinery, no half-residue formula).
-/

-- CLOSED: sinc and its continuity are already in Mathlib!
-- Real.sinc : ℝ → ℝ with sinc_apply : sinc x = if x = 0 then 1 else sin x / x
-- continuous_sinc : Continuous sinc
-- No custom definition needed — just use Real.sinc directly.

-- Re-export for clarity
#check Real.sinc
#check Real.continuous_sinc

/-- The integration-by-parts identity underlying Dirichlet's test for `sinc`.
This is kept separate from the evaluation of the limit: it is also the
uniform tail estimate needed to remove an Abel or Gaussian regularization. -/
lemma integral_sinc_eq_cos_div_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, Real.sinc x =
      Real.cos a / a - Real.cos b / b - ∫ x in a..b, Real.cos x / x ^ 2 := by
  have hx0 : ∀ x ∈ Set.uIcc a b, x ≠ 0 := by
    intro x hx
    have hx' : a ≤ x := by
      rw [Set.uIcc_of_le hab] at hx
      exact hx.1
    exact ne_of_gt (ha.trans_le hx')
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => Real.cos y / y)
        (-Real.sin x / x - Real.cos x / x ^ 2) x := by
    intro x hx
    convert (Real.hasDerivAt_cos x).div (hasDerivAt_id x) (hx0 x hx) using 1
    simp only [id_eq]
    field_simp [hx0 x hx]
  have hint : IntervalIntegrable
      (fun x : ℝ => -Real.sin x / x - Real.cos x / x ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    fun_prop (disch := aesop)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hsin : IntervalIntegrable (fun x : ℝ => Real.sin x / x) volume a b := by
    apply ContinuousOn.intervalIntegrable
    fun_prop (disch := aesop)
  have hcos : IntervalIntegrable (fun x : ℝ => Real.cos x / x ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    fun_prop (disch := aesop)
  have hfun : (fun x : ℝ => -Real.sin x / x - Real.cos x / x ^ 2) =
      fun x => -(Real.sin x / x) - Real.cos x / x ^ 2 := by
    funext x
    ring
  rw [hfun] at hftc
  change (∫ x in a..b,
    (-(fun y : ℝ => Real.sin y / y)) x - (fun y : ℝ => Real.cos y / y ^ 2) x) =
      Real.cos b / b - Real.cos a / a at hftc
  rw [intervalIntegral.integral_sub hsin.neg hcos] at hftc
  simp only [Pi.neg_apply] at hftc
  rw [intervalIntegral.integral_neg] at hftc
  have hsinc : ∀ᵐ x : ℝ, x ∈ Set.uIoc a b →
      Real.sinc x = Real.sin x / x := by
    filter_upwards with x
    intro hx
    rw [Real.sinc_of_ne_zero]
    exact hx0 x (Set.uIoc_subset_uIcc hx)
  rw [intervalIntegral.integral_congr_ae hsinc]
  linarith

-- The Dirichlet integral: the answer is π
-- This is the exam answer. The contour proof is outlined above.
-- Mathlib does NOT have contour integration for improper integrals,
-- Jordan's lemma, or the half-residue formula.
-- The statement below records the answer for the cheatsheet.
-- NOTE: sinc ∉ L¹(ℝ), so the Bochner integral ∫ sinc ∂volume = 0
-- (Mathlib returns 0 for non-integrable functions).
-- The correct statement uses the improper Riemann integral:
-- lim_{R→∞} ∫_{-R}^{R} sinc(x) dx = π.
-- Mathlib has intervalIntegral for this.

theorem dirichlet_integral_improper :
    Filter.Tendsto (fun R : ℝ => ∫ x in Set.Icc (-R) R, Real.sinc x ∂volume)
      Filter.atTop (nhds π) := by
  sorry -- Contour integration proof:
        -- 1. ∮_Γ e^{iz}/z dz = 0 (Cauchy, no poles inside)
        -- 2. ∫_{C_R} → 0 (Jordan's lemma)
        -- 3. ∫_{C_ε} → -πi (half-residue)
        -- 4. PV ∫ e^{ix}/x dx = πi
        -- 5. Im(πi) = π = ∫ sin(x)/x dx
        --
        -- Mathlib gap: no contour integration for improper integrals.
        -- The result COULD be proved via Parseval/Plancherel
        -- (Fourier transform of rect function) but Mathlib's
        -- Fourier theory doesn't have this specific computation.

-- Alternative proof sketch via Fourier theory (no contour integration):
-- rect(ξ) = χ_{[-1/2,1/2]}(ξ) has Fourier transform sinc(x) = sin(πx)/(πx).
-- By Parseval: ∫ |sinc|² = ∫ |rect|² = 1.
-- But this gives ∫ sinc², not ∫ sinc. The direct Fourier approach:
-- ∫ sinc(x) dx = rect(0) · (normalization) = π (evaluation of FT at 0).
-- This is the Fourier inversion theorem applied at ξ = 0.
