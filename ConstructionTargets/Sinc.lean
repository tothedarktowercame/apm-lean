import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set Real

noncomputable section

/-! # The Dirichlet sinc integral

  The Dirichlet integral, computed by Abel regularization.

  The formal proof first establishes convergence by Dirichlet's test.  It then
  evaluates the exponentially damped integral as
  `∫₀∞ exp (-a*x) * sinc x = arctan (1/a)` using Fubini and the elementary
  Laplace transform of cosine.  An integration-by-parts tail bound removes the
  damping uniformly as `a ↓ 0`, identifying the positive-half-line limit as
  `π / 2`; evenness gives the symmetric limit `π`.
-/

-- CLOSED: sinc and its continuity are already in Mathlib!
-- Real.sinc : ℝ → ℝ with sinc_apply : sinc x = if x = 0 then 1 else sin x / x
-- continuous_sinc : Continuous sinc
-- No custom definition needed — just use Real.sinc directly.

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

/-- The elementary parameter integral representation of `sinc`. -/
lemma integral_cos_mul_eq_sinc (x : ℝ) :
    ∫ t in (0 : ℝ)..1, Real.cos (t * x) = Real.sinc x := by
  by_cases hx : x = 0
  · simp [hx]
  rw [Real.sinc_of_ne_zero hx]
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun u : ℝ => Real.sin (u * x) / x) (Real.cos (t * x)) t := by
    intro t _
    convert ((Real.hasDerivAt_sin (t * x)).comp t
      ((hasDerivAt_id t).mul_const x)).div_const x using 1
    field_simp
  have hint : IntervalIntegrable (fun t : ℝ => Real.cos (t * x)) volume 0 1 :=
    (Real.continuous_cos.comp (continuous_id.mul continuous_const)).intervalIntegrable 0 1
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- The Laplace transform of a cosine on the positive half-line. -/
lemma integral_exp_neg_mul_cos_Ioi {a : ℝ} (ha : 0 < a) (t : ℝ) :
    ∫ x in Set.Ioi (0 : ℝ), Real.exp (-a * x) * Real.cos (t * x) =
      a / (a ^ 2 + t ^ 2) := by
  let c : ℂ := (-a : ℂ) + t * Complex.I
  have hc : c.re < 0 := by
    dsimp [c]
    simpa using ha
  have hi := integral_exp_mul_complex_Ioi hc (0 : ℝ)
  have hrexp (x : ℝ) :
      (Complex.exp (c * x)).re = Real.exp (-a * x) * Real.cos (t * x) := by
    rw [Complex.exp_re]
    simp [c]
  have hint := integrableOn_exp_mul_complex_Ioi hc (0 : ℝ)
  calc
    ∫ x in Set.Ioi (0 : ℝ), Real.exp (-a * x) * Real.cos (t * x) =
        ∫ x in Set.Ioi (0 : ℝ), (Complex.exp (c * x)).re := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      exact (hrexp x).symm
    _ = (∫ x in Set.Ioi (0 : ℝ), Complex.exp (c * x)).re :=
      integral_re hint
    _ = (-Complex.exp (c * (0 : ℝ)) / c).re := congrArg Complex.re hi
    _ = a / (a ^ 2 + t ^ 2) := by
      dsimp [c]
      simp only [mul_zero, Complex.exp_zero, neg_div]
      rw [Complex.neg_re]
      rw [Complex.div_re]
      simp [Complex.normSq_apply]
      have hden : a ^ 2 + t ^ 2 ≠ 0 :=
        ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t))
      field_simp [hden]

/-- The integrability input for the damped sinc Fubini calculation. -/
lemma integrable_damped_cos_prod {a : ℝ} (ha : 0 < a) :
    Integrable
      (Function.uncurry fun t x : ℝ => Real.exp (-a * x) * Real.cos (t * x))
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod
        (volume.restrict (Set.Ioi (0 : ℝ)))) := by
  have hone : Integrable (fun _ : ℝ => (1 : ℝ))
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    exact integrableOn_const (by simp)
  have hexp : Integrable (fun x : ℝ => Real.exp (-a * x))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa [neg_mul] using integrableOn_exp_mul_Ioi (a := -a) (by linarith) (0 : ℝ)
  refine Integrable.mono (hone.mul_prod hexp) (by fun_prop) ?_
  exact ae_of_all _ fun p => by
    rcases p with ⟨t, x⟩
    change |Real.exp (-a * x) * Real.cos (t * x)| ≤ |1 * Real.exp (-a * x)|
    rw [abs_mul]
    simp only [one_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (abs_cos_le_one _)

/-- Abel's exponentially damped evaluation of the positive Dirichlet integral. -/
lemma integral_exp_neg_mul_sinc_Ioi {a : ℝ} (ha : 0 < a) :
    ∫ x in Set.Ioi (0 : ℝ), Real.exp (-a * x) * Real.sinc x =
      Real.arctan (1 / a) := by
  have hswap := intervalIntegral_integral_swap
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (integrable_damped_cos_prod ha)
  calc
    ∫ x in Set.Ioi (0 : ℝ), Real.exp (-a * x) * Real.sinc x =
        ∫ x in Set.Ioi (0 : ℝ),
          Real.exp (-a * x) * (∫ t in (0 : ℝ)..1, Real.cos (t * x)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [integral_cos_mul_eq_sinc]
    _ = ∫ t in (0 : ℝ)..1,
          ∫ x in Set.Ioi (0 : ℝ), Real.exp (-a * x) * Real.cos (t * x) := by
      simpa [Measure.restrict_apply_univ] using hswap.symm
    _ = ∫ t in (0 : ℝ)..1, a / (a ^ 2 + t ^ 2) := by
      apply intervalIntegral.integral_congr
      intro t _
      exact integral_exp_neg_mul_cos_Ioi ha t
    _ = Real.arctan (1 / a) := by
      rw [integral_div_sq_add_sq]
      simp

/-- Abel summation preserves a uniform Dirichlet tail estimate. -/
lemma abs_integral_exp_neg_mul_sinc_le_four_div
    {a A B : ℝ} (ha : 0 < a) (hA : 0 < A) (hAB : A ≤ B) :
    |∫ x in A..B, Real.exp (-a * x) * Real.sinc x| ≤ 4 / A := by
  let F : ℝ → ℝ := fun x => ∫ t in A..x, Real.sinc t
  have hF {x : ℝ} (hx : A ≤ x) : |F x| ≤ 2 / A := by
    exact abs_integral_sinc_le_two_div hA hx
  have hFderiv (x : ℝ) : HasDerivAt F (Real.sinc x) x := by
    exact intervalIntegral.integral_hasDerivAt_right
      (Real.continuous_sinc.intervalIntegrable A x)
      (Real.continuous_sinc.stronglyMeasurableAtFilter volume (nhds x))
      Real.continuous_sinc.continuousAt
  have hFcont : Continuous F :=
    continuous_iff_continuousAt.mpr fun x => (hFderiv x).continuousAt
  have hexpderiv (x : ℝ) :
      HasDerivAt (fun y : ℝ => Real.exp (-a * y))
        (-a * Real.exp (-a * x)) x := by
    convert (Real.hasDerivAt_exp (-a * x)).comp x
      ((hasDerivAt_const x (-a)).mul (hasDerivAt_id x)) using 1 <;> ring
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := A) (b := B)
    (u := fun x : ℝ => Real.exp (-a * x))
    (v := F)
    (u' := fun x => -a * Real.exp (-a * x))
    (v' := Real.sinc)
    (fun x _ => hexpderiv x)
    (fun x _ => hFderiv x)
    ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).const_mul (-a) |>.intervalIntegrable A B)
    (Real.continuous_sinc.intervalIntegrable A B)
  have hFA : F A = 0 := by simp [F]
  have hrepr :
      (∫ x in A..B, Real.exp (-a * x) * Real.sinc x) =
        Real.exp (-a * B) * F B -
          ∫ x in A..B, (-a * Real.exp (-a * x)) * F x := by
    simpa [hFA] using hparts
  rw [hrepr]
  calc
    |Real.exp (-a * B) * F B -
        ∫ x in A..B, (-a * Real.exp (-a * x)) * F x|
        ≤ |Real.exp (-a * B) * F B| +
            |∫ x in A..B, (-a * Real.exp (-a * x)) * F x| := abs_sub _ _
    _ ≤ 2 / A + ∫ x in A..B, a * Real.exp (-a * x) * (2 / A) := by
      gcongr
      · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_of_le_one_left (abs_nonneg _) (Real.exp_le_one_iff.mpr (by
          have hB : 0 ≤ B := hA.le.trans hAB
          nlinarith))
          |>.trans (hF hAB)
      · calc
          |∫ x in A..B, (-a * Real.exp (-a * x)) * F x|
              ≤ ∫ x in A..B, |(-a * Real.exp (-a * x)) * F x| :=
                intervalIntegral.abs_integral_le_integral_abs hAB
          _ ≤ ∫ x in A..B, a * Real.exp (-a * x) * (2 / A) := by
            apply intervalIntegral.integral_mono_on hAB
              (by
                apply ContinuousOn.intervalIntegrable
                fun_prop)
              (by
                apply ContinuousOn.intervalIntegrable
                fun_prop)
            intro x hx
            change |(-a * Real.exp (-a * x)) * F x| ≤
              a * Real.exp (-a * x) * (2 / A)
            rw [abs_mul, abs_mul, abs_neg, abs_of_pos ha,
              abs_of_pos (Real.exp_pos _)]
            exact mul_le_mul_of_nonneg_left (hF hx.1)
              (mul_nonneg ha.le (Real.exp_pos _).le)
    _ ≤ 2 / A + 2 / A := by
      gcongr
      have hanti : AntitoneOn (fun x : ℝ => Real.exp (-a * x)) (Set.Icc A B) := by
        intro x hx y hy hxy
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hxy (neg_nonpos.mpr ha.le))
      have hcalc :
          ∫ x in A..B, a * Real.exp (-a * x) =
            Real.exp (-a * A) - Real.exp (-a * B) := by
        have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
          (a := A) (b := B)
          (f := fun x : ℝ => -Real.exp (-a * x))
          (f' := fun x : ℝ => a * Real.exp (-a * x))
          (fun x _ => by convert (hexpderiv x).neg using 1 <;> ring)
          (by
            apply ContinuousOn.intervalIntegrable
            fun_prop)
        convert h using 1 <;> ring
      rw [show (fun x : ℝ => a * Real.exp (-a * x) * (2 / A)) =
          fun x => (2 / A) * (a * Real.exp (-a * x)) by
            funext x
            ring,
        intervalIntegral.integral_const_mul, hcalc]
      have hnonneg : 0 ≤ Real.exp (-a * A) - Real.exp (-a * B) :=
        sub_nonneg.mpr (hanti (Set.left_mem_Icc.mpr hAB)
          (Set.right_mem_Icc.mpr hAB) hAB)
      have hdiff_le : Real.exp (-a * A) - Real.exp (-a * B) ≤ 1 :=
        (sub_le_self _ (Real.exp_pos _).le).trans
          (Real.exp_le_one_iff.mpr (by nlinarith))
      simpa using mul_le_mul_of_nonneg_left hdiff_le
        (show 0 ≤ 2 / A by positivity)
    _ = 4 / A := by ring

lemma integrableOn_exp_neg_mul_sinc_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => Real.exp (-a * x) * Real.sinc x)
      (Set.Ioi (0 : ℝ)) := by
  have hexp : IntegrableOn (fun x : ℝ => Real.exp (-a * x)) (Set.Ioi (0 : ℝ)) := by
    simpa [neg_mul] using integrableOn_exp_mul_Ioi (a := -a) (by linarith) (0 : ℝ)
  refine Integrable.mono' hexp (by fun_prop) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_sinc_le_one x)

/-- The corresponding improper tail estimate, obtained by passing the finite
Abel-summation bound to the limit. -/
lemma abs_integral_exp_neg_mul_sinc_Ioi_le_four_div
    {a A : ℝ} (ha : 0 < a) (hA : 0 < A) :
    |∫ x in Set.Ioi A, Real.exp (-a * x) * Real.sinc x| ≤ 4 / A := by
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-a * x) * Real.sinc x)
      (Set.Ioi A) :=
    (integrableOn_exp_neg_mul_sinc_Ioi ha).mono_set
      (Set.Ioi_subset_Ioi hA.le)
  have hlim := intervalIntegral_tendsto_integral_Ioi A hint Filter.tendsto_id
  apply le_of_tendsto hlim.abs
  filter_upwards [Filter.eventually_ge_atTop A] with B hAB
  exact abs_integral_exp_neg_mul_sinc_le_four_div ha hA hAB

/-- On a fixed finite interval the damping can be removed by dominated
convergence. -/
lemma tendsto_intervalIntegral_exp_neg_mul_sinc
    {A : ℝ} (hA : 0 < A) :
    Filter.Tendsto
      (fun a : ℝ => ∫ x in (0 : ℝ)..A,
        Real.exp (-a * x) * Real.sinc x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ x in (0 : ℝ)..A, Real.sinc x)) := by
  simp_rw [intervalIntegral.integral_of_le hA.le]
  have hdct := tendsto_integral_filter_of_dominated_convergence
    (l := nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (μ := volume.restrict (Set.Ioc (0 : ℝ) A))
    (F := fun a x : ℝ => Real.exp (-a * x) * Real.sinc x)
    (f := Real.sinc)
    (fun _ : ℝ => (1 : ℝ))
  apply hdct
  · filter_upwards with a
    fun_prop
  · filter_upwards [self_mem_nhdsWithin] with a ha'
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-a * x) * |Real.sinc x| ≤ Real.exp (-a * x) :=
        mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_sinc_le_one x)
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by
        have ha0 : 0 < a := ha'
        have hx0 : 0 ≤ x := hx.1.le
        nlinarith)
  · exact integrableOn_const (by simp)
  · filter_upwards with x
    have hcont : ContinuousAt
        (fun a : ℝ => Real.exp (-a * x) * Real.sinc x) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left inf_le_left

/-- Abel removal: the exponentially damped integrals tend to the already
existing Dirichlet limit. -/
lemma tendsto_integral_exp_neg_mul_sinc_nhdsWithin
    {L : ℝ}
    (hL : Filter.Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, Real.sinc x)
      Filter.atTop (nhds L)) :
    Filter.Tendsto
      (fun a : ℝ => ∫ x in Set.Ioi (0 : ℝ),
        Real.exp (-a * x) * Real.sinc x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L) := by
  have hLatTop := Metric.tendsto_atTop.mp hL
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := hLatTop (ε / 3) (by positivity)
  let A : ℝ := max N (12 / ε) + 1
  have hNA : N ≤ A := le_trans (le_max_left _ _) (le_add_of_nonneg_right zero_le_one)
  have hA12 : 12 / ε < A :=
    lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
  have hA : 0 < A := (div_pos (by norm_num) hε).trans hA12
  have hLA : dist (∫ x in (0 : ℝ)..A, Real.sinc x) L < ε / 3 :=
    hN A hNA
  have hfinite := Metric.tendsto_nhdsWithin_nhds.mp
    (tendsto_intervalIntegral_exp_neg_mul_sinc hA)
  obtain ⟨δ, hδ, hclose⟩ := hfinite (ε / 3) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro a ha' hadist
  have ha : 0 < a := ha'
  have hhead :
      dist (∫ x in (0 : ℝ)..A, Real.exp (-a * x) * Real.sinc x)
        (∫ x in (0 : ℝ)..A, Real.sinc x) < ε / 3 :=
    hclose ha' hadist
  have htail :=
    abs_integral_exp_neg_mul_sinc_Ioi_le_four_div ha hA
  have htail_lt : 4 / A < ε / 3 := by
    rw [div_lt_iff₀ hA]
    have h12 : 12 < A * ε := (div_lt_iff₀ hε).mp hA12
    calc
      4 < (ε * A) / 3 := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2 (by
        nlinarith)
      _ = ε / 3 * A := by ring
  have h0int := integrableOn_exp_neg_mul_sinc_Ioi ha
  have hAint : IntegrableOn
      (fun x : ℝ => Real.exp (-a * x) * Real.sinc x) (Set.Ioi A) :=
    h0int.mono_set (Set.Ioi_subset_Ioi hA.le)
  have hsplit := intervalIntegral.integral_interval_add_Ioi h0int hAint
  rw [← hsplit]
  rw [Real.dist_eq] at hhead hLA
  rw [Real.dist_eq]
  calc
    |(∫ x in (0 : ℝ)..A, Real.exp (-a * x) * Real.sinc x) +
        (∫ x in Set.Ioi A, Real.exp (-a * x) * Real.sinc x) - L|
        ≤ |(∫ x in (0 : ℝ)..A, Real.exp (-a * x) * Real.sinc x) -
            (∫ x in (0 : ℝ)..A, Real.sinc x)| +
          |(∫ x in (0 : ℝ)..A, Real.sinc x) - L| +
          |∫ x in Set.Ioi A, Real.exp (-a * x) * Real.sinc x| := by
      calc
        _ = |((∫ x in (0 : ℝ)..A, Real.exp (-a * x) * Real.sinc x) -
              (∫ x in (0 : ℝ)..A, Real.sinc x)) +
            ((∫ x in (0 : ℝ)..A, Real.sinc x) - L) +
            (∫ x in Set.Ioi A, Real.exp (-a * x) * Real.sinc x)| := by
              congr 1
              ring
        _ ≤ |((∫ x in (0 : ℝ)..A, Real.exp (-a * x) * Real.sinc x) -
              (∫ x in (0 : ℝ)..A, Real.sinc x)) +
            ((∫ x in (0 : ℝ)..A, Real.sinc x) - L)| +
            |∫ x in Set.Ioi A, Real.exp (-a * x) * Real.sinc x| :=
              abs_add_le _ _
        _ ≤ _ := add_le_add (abs_add_le _ _) le_rfl
    _ < ε / 3 + ε / 3 + ε / 3 :=
      add_lt_add (add_lt_add hhead hLA) (htail.trans_lt htail_lt)
    _ = ε := by ring

lemma tendsto_arctan_one_div_nhdsWithin :
    Filter.Tendsto (fun a : ℝ => Real.arctan (1 / a))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (π / 2)) := by
  have hbase : Filter.Tendsto (fun a : ℝ => π / 2 - Real.arctan a)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (π / 2)) := by
    convert tendsto_const_nhds.sub
      (Real.continuous_arctan.continuousAt.tendsto.mono_left inf_le_left) using 1
    simp
  apply Filter.Tendsto.congr' _ hbase
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [one_div, Real.arctan_inv_of_pos ha]

/-- Identification of the convergent positive-half-line Dirichlet integral. -/
lemma tendsto_integral_sinc_pi_div_two :
    Filter.Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, Real.sinc x)
      Filter.atTop (nhds (π / 2)) := by
  obtain ⟨L, hL⟩ := exists_tendsto_integral_sinc
  have hdamped_L := tendsto_integral_exp_neg_mul_sinc_nhdsWithin hL
  have hdamped_pi : Filter.Tendsto
      (fun a : ℝ => ∫ x in Set.Ioi (0 : ℝ),
        Real.exp (-a * x) * Real.sinc x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (π / 2)) := by
    apply Filter.Tendsto.congr' _ tendsto_arctan_one_div_nhdsWithin
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact (integral_exp_neg_mul_sinc_Ioi ha).symm
  have hLval : L = π / 2 :=
    tendsto_nhds_unique hdamped_L hdamped_pi
  simpa [hLval] using hL

-- The Dirichlet integral.
-- NOTE: sinc ∉ L¹(ℝ), so the Bochner integral ∫ sinc ∂volume = 0
-- (Mathlib returns 0 for non-integrable functions).
-- The correct statement uses the improper Riemann integral:
-- lim_{R→∞} ∫_{-R}^{R} sinc(x) dx = π.
-- Mathlib has intervalIntegral for this.

theorem dirichlet_integral_improper :
    Filter.Tendsto (fun R : ℝ => ∫ x in Set.Icc (-R) R, Real.sinc x ∂volume)
      Filter.atTop (nhds π) := by
  have hpos := tendsto_integral_sinc_pi_div_two
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
  have htwo : Filter.Tendsto
      (fun R : ℝ => 2 * ∫ x in (0 : ℝ)..R, Real.sinc x)
      Filter.atTop (nhds π) := by
    convert tendsto_const_nhds.mul hpos using 1 <;> ring
  exact Filter.Tendsto.congr' (heq.mono fun _ h => h.symm) htwo

-- Alternative proof sketch via Fourier theory (no contour integration):
-- rect(ξ) = χ_{[-1/2,1/2]}(ξ) has Fourier transform sinc(x) = sin(πx)/(πx).
-- By Parseval: ∫ |sinc|² = ∫ |rect|² = 1.
-- But this gives ∫ sinc², not ∫ sinc. The direct Fourier approach:
-- ∫ sinc(x) dx = rect(0) · (normalization) = π (evaluation of FT at 0).
-- This is the Fourier inversion theorem applied at ξ = 0.
