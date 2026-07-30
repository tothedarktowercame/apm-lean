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

/-- The elementary comparison integral used in the Dirichlet tail estimate. -/
lemma integral_one_div_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, 1 / x ^ 2 = 1 / a - 1 / b := by
  have hx0 : ∀ x ∈ Set.uIcc a b, x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact ne_of_gt (ha.trans_le hx.1)
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => -y⁻¹) (1 / x ^ 2) x := by
    intro x hx
    simpa [one_div] using (hasDerivAt_inv (hx0 x hx)).neg
  have hint : IntervalIntegrable (fun x : ℝ => 1 / x ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    fun_prop (disch := aesop)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa only [one_div] using hftc.trans (by ring)

/-- Dirichlet's uniform tail estimate for the sinc integral. -/
lemma abs_integral_sinc_le_two_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    |∫ x in a..b, Real.sinc x| ≤ 2 / a := by
  have hxpos : ∀ x ∈ Set.Icc a b, 0 < x :=
    fun x hx => ha.trans_le hx.1
  have hcos_int :
      IntervalIntegrable (fun x : ℝ => Real.cos x / x ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact Real.continuous_cos.continuousOn.div
      (continuousOn_id.pow 2) fun x hx =>
        pow_ne_zero _ (ne_of_gt (hxpos x (by
          rw [Set.uIcc_of_le hab] at hx
          exact hx)))
  have habs_int :
      IntervalIntegrable (fun x : ℝ => |Real.cos x / x ^ 2|) volume a b :=
    hcos_int.abs
  have hinv_int :
      IntervalIntegrable (fun x : ℝ => 1 / x ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div (continuousOn_id.pow 2) fun x hx =>
      pow_ne_zero _ (ne_of_gt (hxpos x (by
        rw [Set.uIcc_of_le hab] at hx
        exact hx)))
  have hrem :
      |∫ x in a..b, Real.cos x / x ^ 2| ≤ 1 / a - 1 / b := by
    calc
      |∫ x in a..b, Real.cos x / x ^ 2| ≤
          ∫ x in a..b, |Real.cos x / x ^ 2| :=
        intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ x in a..b, 1 / x ^ 2 := by
        apply intervalIntegral.integral_mono_on hab habs_int hinv_int
        intro x hx
        rw [abs_div, abs_of_pos (sq_pos_of_pos (hxpos x hx))]
        exact div_le_div_of_nonneg_right (abs_cos_le_one x)
          (sq_nonneg x)
      _ = 1 / a - 1 / b := integral_one_div_sq ha hab
  rw [integral_sinc_eq_cos_div_sub ha hab]
  calc
    |Real.cos a / a - Real.cos b / b -
        ∫ x in a..b, Real.cos x / x ^ 2|
        ≤ |Real.cos a / a| + |Real.cos b / b| +
            |∫ x in a..b, Real.cos x / x ^ 2| := by
          rw [sub_eq_add_neg, sub_eq_add_neg]
          calc
            |Real.cos a / a + -(Real.cos b / b) +
                -(∫ x in a..b, Real.cos x / x ^ 2)|
                ≤ |Real.cos a / a + -(Real.cos b / b)| +
                    |-(∫ x in a..b, Real.cos x / x ^ 2)| :=
              abs_add_le _ _
            _ = |Real.cos a / a + -(Real.cos b / b)| +
                    |∫ x in a..b, Real.cos x / x ^ 2| := by rw [abs_neg]
            _ ≤ (|Real.cos a / a| + |Real.cos b / b|) +
                    |∫ x in a..b, Real.cos x / x ^ 2| := by
              gcongr
              simpa only [abs_neg] using
                abs_add_le (Real.cos a / a) (-(Real.cos b / b))
            _ = |Real.cos a / a| + |Real.cos b / b| +
                    |∫ x in a..b, Real.cos x / x ^ 2| := by ring
    _ ≤ 1 / a + 1 / b + (1 / a - 1 / b) := by
      gcongr
      · rw [abs_div, abs_of_pos ha]
        exact div_le_div_of_nonneg_right (abs_cos_le_one a) ha.le
      · have hb : 0 < b := ha.trans_le hab
        rw [abs_div, abs_of_pos hb]
        exact div_le_div_of_nonneg_right (abs_cos_le_one b) hb.le
    _ = 2 / a := by ring

/-- The positive-half-line Dirichlet integrals converge; this is the complete
tail-control half of the Dirichlet integral argument, before identifying the
limit as `π / 2`. -/
lemma exists_tendsto_integral_sinc :
    ∃ L : ℝ, Filter.Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, Real.sinc x)
      Filter.atTop (nhds L) := by
  let F : ℝ → ℝ := fun R => ∫ x in (0 : ℝ)..R, Real.sinc x
  apply cauchy_map_iff_exists_tendsto.mp
  rw [Metric.cauchy_iff]
  refine ⟨by infer_instance, ?_⟩
  intro ε hε
  let A := max 1 (4 / ε)
  refine ⟨F '' Set.Ici A, ?_, ?_⟩
  · rw [Filter.mem_map]
    exact Filter.mem_of_superset (Filter.Ici_mem_atTop A) fun R hR =>
      ⟨R, hR, rfl⟩
  · have htail {x y : ℝ} (hx : A ≤ x) (hxy : x ≤ y) :
        dist (F x) (F y) < ε := by
      have hA1 : 1 ≤ A := le_max_left _ _
      have hxpos : 0 < x := zero_lt_one.trans_le (hA1.trans hx)
      have h0x : IntervalIntegrable Real.sinc volume 0 x :=
        Real.continuous_sinc.intervalIntegrable 0 x
      have hxyint : IntervalIntegrable Real.sinc volume x y :=
        Real.continuous_sinc.intervalIntegrable x y
      have hadd :=
        intervalIntegral.integral_add_adjacent_intervals h0x hxyint
      have hdiff : F y - F x = ∫ z in x..y, Real.sinc z := by
        dsimp [F]
        linarith
      have hxA : 4 / ε ≤ x := (le_max_right 1 (4 / ε)).trans hx
      have h4 : 0 < 4 / ε := div_pos (by norm_num) hε
      calc
        dist (F x) (F y) = |F y - F x| := by
          rw [Real.dist_eq, abs_sub_comm]
        _ = |∫ z in x..y, Real.sinc z| := congrArg abs hdiff
        _ ≤ 2 / x := abs_integral_sinc_le_two_div hxpos hxy
        _ ≤ 2 / (4 / ε) :=
          div_le_div_of_nonneg_left (by norm_num) h4 hxA
        _ = ε / 2 := by field_simp; ring
        _ < ε := half_lt_self hε
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rcases le_total x y with hxy | hyx
    · exact htail hx hxy
    · simpa [dist_comm] using htail hy hyx

/-- Symmetric finite Dirichlet integrals likewise converge, to twice the
positive-half-line limit. -/
lemma exists_tendsto_symmetric_integral_sinc :
    ∃ L : ℝ, Filter.Tendsto
      (fun R : ℝ => ∫ x in Set.Icc (-R) R, Real.sinc x ∂volume)
      Filter.atTop (nhds L) := by
  obtain ⟨L, hL⟩ := exists_tendsto_integral_sinc
  refine ⟨2 * L, ?_⟩
  have heq : ∀ᶠ R : ℝ in Filter.atTop,
      (∫ x in Set.Icc (-R) R, Real.sinc x ∂volume) =
        2 * ∫ x in (0 : ℝ)..R, Real.sinc x := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with R hR
    have hneg :
        (∫ x in -R..(0 : ℝ), Real.sinc x) =
          ∫ x in (0 : ℝ)..R, Real.sinc x := by
      symm
      simpa only [Real.sinc_neg, neg_zero] using
        (intervalIntegral.integral_comp_neg
          (f := Real.sinc) (a := (0 : ℝ)) (b := R))
    have hleft : IntervalIntegrable Real.sinc volume (-R) 0 :=
      Real.continuous_sinc.intervalIntegrable (-R) 0
    have hright : IntervalIntegrable Real.sinc volume 0 R :=
      Real.continuous_sinc.intervalIntegrable 0 R
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← (intervalIntegral.integral_of_le
      (f := Real.sinc) (μ := volume) (a := -R) (b := R)
      (neg_le_self hR))]
    rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright,
      hneg]
    ring
  exact Filter.Tendsto.congr' (heq.mono fun _ h => h.symm)
    (tendsto_const_nhds.mul hL)

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
  sorry
  -- Exact remaining obstruction: `exists_tendsto_symmetric_integral_sinc`
  -- proves convergence, so it remains only to identify its limit as `π`.
  -- The checked component route is Abel regularization:
  --   ∫₀∞ exp (-a*x) * sinc x dx = arctan (1/a),
  -- followed by a uniform tail estimate as `a ↓ 0`.
  -- Mathlib supplies the exponential half-line integral and the arctangent
  -- integral, but not the damped Fubini evaluation or the Abel-removal lemma.

-- Alternative proof sketch via Fourier theory (no contour integration):
-- rect(ξ) = χ_{[-1/2,1/2]}(ξ) has Fourier transform sinc(x) = sin(πx)/(πx).
-- By Parseval: ∫ |sinc|² = ∫ |rect|² = 1.
-- But this gives ∫ sinc², not ∫ sinc. The direct Fourier approach:
-- ∫ sinc(x) dx = rect(0) · (normalization) = π (evaluation of FT at 0).
-- This is the Fourier inversion theorem applied at ξ = 0.
