import Mathlib

/-!
# APM m02J06

## Statement repairs

The printed condition `|x| = 0 ⇒ f(x) = 0` only constrains one point and makes
the compactness conclusion false by translations. Following the intended
Kolmogorov–Riesz argument, it is repaired to the uniform support condition
`|x| ≥ 1 ⇒ f(x) = 0`. The translation estimate is quantified over `h > 0`.
The usual nonnegativity condition for a mollifier is made explicit; it is
needed for the stated constant-one approximation estimate.

## Encoding questions

Compactness is asserted after mapping the actual measurable representatives
into Mathlib's `L¹` space, so it is compactness in the `L¹` norm and not a
pointwise-function topology.
-/

open MeasureTheory Set

/-- The class `K` from the problem, with its intended common support. -/
def apm_m02J06_K : Set (ℝ → ℝ) :=
  {f | Integrable f volume ∧
    ∫ x, |f x| ∂volume ≤ 1 ∧
    (∀ h : ℝ, 0 < h → ∫ x, |f (x + h) - f x| ∂volume ≤ Real.sqrt h) ∧
    (∀ x : ℝ, 1 ≤ |x| → f x = 0)}

/-- The standard rescaling of a mollifier. -/
noncomputable def apm_m02J06_mollifier (φ : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  fun x ↦ ε⁻¹ * φ (x / ε)

/-- Convolution of two scalar functions on `ℝ`. -/
noncomputable def apm_m02J06_convolution (f g : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ ∫ t, f (x - t) * g t ∂volume

/-- The canonical class of an integrable function in `L¹(ℝ)`. -/
noncomputable def apm_m02J06_toL1 (f : ℝ → ℝ) (hf : Integrable f volume) :
    Lp ℝ 1 (volume : Measure ℝ) :=
  (memLp_one_iff_integrable.2 hf).toLp f

/-- `K` regarded as a subset of the normed space `L¹(ℝ)`. -/
def apm_m02J06_KL1 : Set (Lp ℝ 1 (volume : Measure ℝ)) :=
  {u | ∃ (f : ℝ → ℝ) (hf : Integrable f volume),
    f ∈ apm_m02J06_K ∧ u = apm_m02J06_toL1 f hf}

/-- The chosen `L¹` class is independent of the integrable representative. -/
lemma apm_m02J06_toL1_congr_ae
    {f g : ℝ → ℝ} (hf : Integrable f volume) (hg : Integrable g volume)
    (hfg : f =ᵐ[volume] g) :
    apm_m02J06_toL1 f hf = apm_m02J06_toL1 g hg := by
  exact MemLp.toLp_congr (memLp_one_iff_integrable.2 hf)
    (memLp_one_iff_integrable.2 hg) hfg

/-- Positive rescaling preserves nonnegativity of the mollifier. -/
lemma apm_m02J06_mollifier_nonneg
    {φ : ℝ → ℝ} (hφ : ∀ x, 0 ≤ φ x) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    0 ≤ apm_m02J06_mollifier φ ε x := by
  exact mul_nonneg (inv_nonneg.mpr hε.le) (hφ (x / ε))

/-- A mollifier supported in the unit interval rescales to support radius
`ε`. -/
lemma apm_m02J06_mollifier_eq_zero
    {φ : ℝ → ℝ} (hφ : ∀ x, 1 ≤ |x| → φ x = 0)
    {ε x : ℝ} (hε : 0 < ε) (hx : ε ≤ |x|) :
    apm_m02J06_mollifier φ ε x = 0 := by
  rw [apm_m02J06_mollifier, hφ (x / ε)]
  · simp
  · rw [abs_div, abs_of_pos hε]
    exact (le_div_iff₀ hε).2 (by simpa using hx)

/-- The positive rescaling preserves total mass one. -/
lemma apm_m02J06_mollifier_integral_one
    {φ : ℝ → ℝ} (hφ : ∫ x, φ x ∂volume = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∫ x, apm_m02J06_mollifier φ ε x ∂volume = 1 := by
  have hscale := Measure.integral_comp_mul_left φ ε⁻¹
  simp only [inv_inv, abs_of_pos hε] at hscale
  have hscale' : (∫ x, φ (ε⁻¹ * x) ∂volume) = ε := by
    simpa [hφ, smul_eq_mul] using hscale
  change (∫ x, ε⁻¹ * φ (x / ε) ∂volume) = 1
  simp_rw [div_eq_inv_mul]
  rw [integral_const_mul, hscale']
  field_simp

/-- A nonnegative function whose Bochner integral is one is integrable; hence
so is every positive mollifier rescaling.  This packages the integrability
premise needed by Tonelli in the first bridge. -/
lemma apm_m02J06_mollifier_integrable
    {φ : ℝ → ℝ} (_hφnonneg : ∀ x, 0 ≤ φ x)
    (hφint : ∫ x, φ x ∂volume = 1) {ε : ℝ} (hε : 0 < ε) :
    Integrable (apm_m02J06_mollifier φ ε) volume := by
  have hφ : Integrable φ volume := by
    by_contra hn
    have hz : ∫ x, φ x ∂volume = 0 := integral_undef hn
    linarith [hφint, hz]
  have hcomp : Integrable (fun x : ℝ ↦ φ (ε⁻¹ * x)) volume :=
    hφ.comp_mul_left' (inv_ne_zero hε.ne')
  have hscaled : Integrable (fun x : ℝ ↦ ε⁻¹ * φ (ε⁻¹ * x)) volume :=
    hcomp.const_mul ε⁻¹
  convert hscaled using 1
  funext x
  simp only [apm_m02J06_mollifier]
  congr 2
  field_simp

/-- The rescaled nonnegative mollifier has `L¹` norm exactly one. -/
lemma apm_m02J06_mollifier_integral_abs_one
    {φ : ℝ → ℝ} (hφnonneg : ∀ x, 0 ≤ φ x)
    (hφint : ∫ x, φ x ∂volume = 1) {ε : ℝ} (hε : 0 < ε) :
    ∫ x, |apm_m02J06_mollifier φ ε x| ∂volume = 1 := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun x ↦
    abs_of_nonneg (apm_m02J06_mollifier_nonneg hφnonneg hε x))]
  exact apm_m02J06_mollifier_integral_one hφint hε

/-- The defining one-sided translation estimate for `apm_m02J06_K` extends
to arbitrary shifts.  The negative case uses Mathlib's
`integral_add_right_eq_self`; compare the translated-integral helper
`integral_translate_norm` in the solved artifact `a95J08`. -/
lemma apm_m02J06_translation_estimate
    {f : ℝ → ℝ} (hf : f ∈ apm_m02J06_K) (h : ℝ) :
    ∫ x, |f (x + h) - f x| ∂volume ≤ Real.sqrt |h| := by
  rcases hf with ⟨_, _, htrans, _⟩
  rcases lt_trichotomy h 0 with hh | rfl | hh
  · have hk : 0 < -h := neg_pos.mpr hh
    have heq :
        (∫ x, |f (x + h) - f x| ∂volume) =
          ∫ x, |f (x + (-h)) - f x| ∂volume := by
      rw [← integral_add_right_eq_self
        (fun x : ℝ ↦ |f (x + h) - f x|) (-h)]
      congr 1
      funext x
      rw [add_assoc, neg_add_cancel, add_zero, abs_sub_comm]
    rw [heq, abs_of_neg hh]
    exact htrans (-h) hk
  · simp
  · rw [abs_of_pos hh]
    exact htrans h hh

/-- Convolution with the rescaled mollifier has a common compact support:
the support radius is the sum of the radii of `f` and the mollifier. -/
lemma apm_m02J06_convolution_eq_zero
    {φ f : ℝ → ℝ} (hφ : ∀ x, 1 ≤ |x| → φ x = 0)
    {ε : ℝ} (hε : 0 < ε) (hf : f ∈ apm_m02J06_K)
    {x : ℝ} (hx : 1 + ε ≤ |x|) :
    apm_m02J06_convolution f (apm_m02J06_mollifier φ ε) x = 0 := by
  unfold apm_m02J06_convolution
  have hz : (fun t : ℝ ↦
      f (x - t) * apm_m02J06_mollifier φ ε t) = 0 := by
    funext t
    by_cases ht : ε ≤ |t|
    · simp [apm_m02J06_mollifier_eq_zero hφ hε ht]
    · have ht' : |t| < ε := lt_of_not_ge ht
      have htri : |x| ≤ |x - t| + |t| := by
        calc
          |x| = |(x - t) + t| := by ring_nf
          _ ≤ |x - t| + |t| := abs_add_le _ _
      have hxt : 1 ≤ |x - t| := by linarith
      simp [hf.2.2.2 (x - t) hxt]
  simp [hz]

/-- Tonelli estimate underlying mollifier approximation, stated before the
a.e. convolution identity: averaging translation differences against a
nonnegative probability kernel supported in radius `ε` costs at most `√ε`. -/
lemma apm_m02J06_tonelli_translation_average
    {f g : ℝ → ℝ} (hf : f ∈ apm_m02J06_K)
    (hg : Integrable g volume) (hgnonneg : ∀ t, 0 ≤ g t)
    (hgint : ∫ t, g t ∂volume = 1) {ε : ℝ} (_hε : 0 < ε)
    (hgsupport : ∀ t, ε ≤ |t| → g t = 0) :
    ∫ x, ∫ t, |f x - f (x - t)| * g t ∂volume ∂volume ≤ Real.sqrt ε := by
  let A : ℝ × ℝ → ℝ := fun z ↦ f z.1 * g z.2
  have hA : Integrable A (volume.prod volume) := hf.1.mul_prod hg
  have hB : Integrable (fun z : ℝ × ℝ ↦ f (z.1 - z.2) * g z.2)
      (volume.prod volume) := by
    simpa [A, Function.comp_def] using
      (measurePreserving_sub_prod volume volume).integrable_comp_of_integrable hA
  have hq : Integrable
      (fun z : ℝ × ℝ ↦ |f z.1 - f (z.1 - z.2)| * g z.2)
      (volume.prod volume) := by
    have hd := hA.sub hB
    have hdabs := hd.abs
    simpa [A, ← sub_mul, abs_mul, abs_of_nonneg (hgnonneg _)] using hdabs
  rw [← integral_prod _ hq, integral_prod_symm _ hq]
  calc
    (∫ t, ∫ x, |f x - f (x - t)| * g t ∂volume ∂volume) =
        ∫ t, g t * (∫ x, |f x - f (x - t)| ∂volume) ∂volume := by
      apply integral_congr_ae
      filter_upwards with t
      rw [integral_mul_const]
      ring
    _ ≤ ∫ t, g t * Real.sqrt ε ∂volume := by
      apply integral_mono_ae
      · convert hq.integral_prod_right using 1
        funext t
        dsimp only
        rw [integral_mul_const]
        ring
      · exact hg.mul_const _
      · filter_upwards with t
        by_cases ht : ε ≤ |t|
        · simp [hgsupport t ht]
        · have hte : |t| ≤ ε := le_of_lt (lt_of_not_ge ht)
          have hsqrt : Real.sqrt |t| ≤ Real.sqrt ε := Real.sqrt_le_sqrt hte
          have htrans :
              (∫ x, |f x - f (x - t)| ∂volume) ≤ Real.sqrt |t| := by
            rw [integral_congr_ae (Filter.Eventually.of_forall fun x ↦
              abs_sub_comm (f x) (f (x - t)))]
            simpa [sub_eq_add_neg] using apm_m02J06_translation_estimate hf (-t)
          exact mul_le_mul_of_nonneg_left (htrans.trans hsqrt) (hgnonneg t)
    _ = Real.sqrt ε := by rw [integral_mul_const, hgint, one_mul]

/-- The a.e. convolution identity and triangle inequality reduce the `L¹`
approximation error to the Tonelli translation average. -/
lemma apm_m02J06_convolution_error_le_translation_average
    {f g : ℝ → ℝ} (hf : Integrable f volume) (hg : Integrable g volume)
    (hgint : ∫ t, g t ∂volume = 1) :
    ∫ x, |f x - apm_m02J06_convolution f g x| ∂volume ≤
      ∫ x, ∫ t, |f x - f (x - t)| * |g t| ∂volume ∂volume := by
  let A : ℝ × ℝ → ℝ := fun z ↦ f z.1 * g z.2
  have hA : Integrable A (volume.prod volume) := hf.mul_prod hg
  have hB : Integrable (fun z : ℝ × ℝ ↦ f (z.1 - z.2) * g z.2)
      (volume.prod volume) := by
    simpa [A, Function.comp_def] using
      (measurePreserving_sub_prod volume volume).integrable_comp_of_integrable hA
  have hD : Integrable
      (fun z : ℝ × ℝ ↦ (f z.1 - f (z.1 - z.2)) * g z.2)
      (volume.prod volume) := by
    simpa [A, sub_mul] using hA.sub hB
  have hid : ∀ᵐ x ∂volume,
      |f x - apm_m02J06_convolution f g x| =
        |∫ t, (f x - f (x - t)) * g t ∂volume| := by
    filter_upwards [hA.prod_right_ae, hB.prod_right_ae] with x hAx hBx
    unfold apm_m02J06_convolution
    have hAx' : Integrable (fun t ↦ f x * g t) volume := by simpa [A] using hAx
    have hi : (∫ t, (f x - f (x - t)) * g t ∂volume) =
        f x - ∫ t, f (x - t) * g t ∂volume := by
      simp_rw [sub_mul]
      rw [integral_sub hAx' hBx, integral_const_mul, hgint, mul_one]
    exact congrArg abs hi.symm
  rw [integral_congr_ae hid]
  calc
    (∫ a, |∫ t, (f a - f (a - t)) * g t ∂volume| ∂volume) ≤
        ∫ x, ∫ t, |(f x - f (x - t)) * g t| ∂volume ∂volume := by
      apply integral_mono_ae hD.integral_prod_left.abs hD.abs.integral_prod_left
      filter_upwards with x
      exact abs_integral_le_integral_abs
    _ = ∫ x, ∫ t, |f x - f (x - t)| * |g t| ∂volume ∂volume := by
      congr 1
      funext x
      congr 1
      funext t
      rw [abs_mul]

/-- Why this unblocks `apm_m02j06`: this is the first missing Tonelli
estimate, expressing approximation by the normalized nonnegative mollifier in
terms of the translation modulus already compiled for `apm_m02J06_K`. -/
theorem apm_m02J06_bridge_1
    {φ : ℝ → ℝ} (hφnonneg : ∀ x, 0 ≤ φ x)
    (hφint : ∫ x, φ x ∂volume = 1)
    (hφsupport : ∀ x, 1 ≤ |x| → φ x = 0) :
    ∀ ε : ℝ, 0 < ε → ∀ f ∈ apm_m02J06_K,
      ∫ x, |f x - apm_m02J06_convolution f
        (apm_m02J06_mollifier φ ε) x| ∂volume ≤ Real.sqrt ε := by
  intro ε hε f hf
  let g := apm_m02J06_mollifier φ ε
  have hg : Integrable g volume := apm_m02J06_mollifier_integrable hφnonneg hφint hε
  have hgnonneg : ∀ t, 0 ≤ g t := apm_m02J06_mollifier_nonneg hφnonneg hε
  calc
    (∫ x, |f x - apm_m02J06_convolution f g x| ∂volume) ≤
        ∫ x, ∫ t, |f x - f (x - t)| * |g t| ∂volume ∂volume :=
      apm_m02J06_convolution_error_le_translation_average hf.1 hg
        (apm_m02J06_mollifier_integral_one hφint hε)
    _ = ∫ x, ∫ t, |f x - f (x - t)| * g t ∂volume ∂volume := by
      congr 1
      funext x
      congr 1
      funext t
      rw [abs_of_nonneg (hgnonneg t)]
    _ ≤ Real.sqrt ε := apm_m02J06_tonelli_translation_average hf hg hgnonneg
      (apm_m02J06_mollifier_integral_one hφint hε) hε
      (fun t ht ↦ apm_m02J06_mollifier_eq_zero hφsupport hε ht)

/-- The analytic core of the second bridge: convolution against an a.e.
measurable kernel bounded by `C` inherits the translation modulus of `f`.
This isolates the exact measurability premise needed for the Bochner integral
linearity step. -/
lemma apm_m02J06_bounded_kernel_translation
    {f g : ℝ → ℝ} (hf : f ∈ apm_m02J06_K)
    (hg : AEStronglyMeasurable g volume) {C : ℝ} (hC : 0 ≤ C)
    (hgbound : ∀ t, |g t| ≤ C) (x y : ℝ) :
    |apm_m02J06_convolution f g x - apm_m02J06_convolution f g y| ≤
      C * Real.sqrt |x - y| := by
  have hfx : Integrable (fun t : ℝ ↦ f (x - t)) volume := hf.1.comp_sub_left x
  have hfy : Integrable (fun t : ℝ ↦ f (y - t)) volume := hf.1.comp_sub_left y
  have hxg : Integrable (fun t : ℝ ↦ f (x - t) * g t) volume := by
    simpa [mul_comm] using hfx.bdd_mul hg (Filter.Eventually.of_forall hgbound)
  have hyg : Integrable (fun t : ℝ ↦ f (y - t) * g t) volume := by
    simpa [mul_comm] using hfy.bdd_mul hg (Filter.Eventually.of_forall hgbound)
  have hdiff : Integrable (fun t : ℝ ↦ f (x - t) - f (y - t)) volume :=
    hfx.sub hfy
  have hprod : Integrable
      (fun t : ℝ ↦ (f (x - t) - f (y - t)) * g t) volume := by
    simpa [mul_comm] using hdiff.bdd_mul hg (Filter.Eventually.of_forall hgbound)
  have hmajor : Integrable
      (fun t : ℝ ↦ C * |f (x - t) - f (y - t)|) volume :=
    hdiff.abs.const_mul C
  unfold apm_m02J06_convolution
  rw [← integral_sub hxg hyg]
  calc
    |∫ t, f (x - t) * g t - f (y - t) * g t ∂volume| =
        |∫ t, (f (x - t) - f (y - t)) * g t ∂volume| := by
          congr 2
          funext t
          ring
    _ ≤ ∫ t, |(f (x - t) - f (y - t)) * g t| ∂volume :=
      abs_integral_le_integral_abs
    _ ≤ ∫ t, C * |f (x - t) - f (y - t)| ∂volume := by
      exact integral_mono_ae hprod.abs hmajor
        (Filter.Eventually.of_forall fun t ↦ by
          simp only
          rw [abs_mul]
          simpa [mul_comm] using
            mul_le_mul_of_nonneg_left (hgbound t)
              (abs_nonneg (f (x - t) - f (y - t))))
    _ = C * ∫ t, |f (x - t) - f (y - t)| ∂volume := integral_const_mul _ _
    _ = C * ∫ s, |f (s + (x - y)) - f s| ∂volume := by
      congr 1
      rw [← integral_sub_left_eq_self
        (fun s : ℝ ↦ |f (s + (x - y)) - f s|) volume y]
      congr 1
      funext t
      ring_nf
    _ ≤ C * Real.sqrt |x - y| :=
      mul_le_mul_of_nonneg_left (apm_m02J06_translation_estimate hf (x - y)) hC

/-- Convolution against a measurable kernel bounded by `C` is pointwise
bounded by `C` times the `L¹` norm. -/
lemma apm_m02J06_convolution_abs_le
    {f g : ℝ → ℝ} (hf : Integrable f volume)
    (hg : AEStronglyMeasurable g volume) {C : ℝ} (_hC : 0 ≤ C)
    (hgbound : ∀ t, |g t| ≤ C) (x : ℝ) :
    |apm_m02J06_convolution f g x| ≤ C * ∫ t, |f t| ∂volume := by
  have hfx : Integrable (fun t : ℝ ↦ f (x - t)) volume := hf.comp_sub_left x
  have hprod : Integrable (fun t : ℝ ↦ f (x - t) * g t) volume := by
    simpa [mul_comm] using hfx.bdd_mul hg (Filter.Eventually.of_forall hgbound)
  have hmajor : Integrable (fun t : ℝ ↦ C * |f (x - t)|) volume :=
    hfx.abs.const_mul C
  unfold apm_m02J06_convolution
  calc
    |∫ t, f (x - t) * g t ∂volume| ≤
        ∫ t, |f (x - t) * g t| ∂volume := abs_integral_le_integral_abs
    _ ≤ ∫ t, C * |f (x - t)| ∂volume := by
      exact integral_mono_ae hprod.abs hmajor
        (Filter.Eventually.of_forall fun t ↦ by
          simp only
          rw [abs_mul]
          simpa [mul_comm] using mul_le_mul_of_nonneg_left (hgbound t)
            (abs_nonneg (f (x - t))))
    _ = C * ∫ t, |f (x - t)| ∂volume := integral_const_mul _ _
    _ = C * ∫ t, |f t| ∂volume := by
      rw [integral_sub_left_eq_self (fun t : ℝ ↦ |f t|) volume x]

/-- A global Hölder-half estimate implies continuity. -/
lemma apm_m02J06_continuous_of_sqrt_modulus
    {F : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ x y, |F x - F y| ≤ C * Real.sqrt |x - y|) : Continuous F := by
  rw [Metric.continuous_iff]
  intro b η hη
  by_cases hC0 : C = 0
  · refine ⟨1, zero_lt_one, fun a _ ↦ ?_⟩
    have hz : |F a - F b| = 0 := le_antisymm ((hF a b).trans (by simp [hC0])) (abs_nonneg _)
    simpa [Real.dist_eq] using lt_of_eq_of_lt hz hη
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    refine ⟨(η / C) ^ 2, sq_pos_of_pos (div_pos hη hCpos), fun a hab ↦ ?_⟩
    rw [Real.dist_eq] at hab ⊢
    have hsqrt : Real.sqrt |a - b| < η / C := by
      rw [Real.sqrt_lt' (div_pos hη hCpos)]
      simpa [sq] using hab
    exact lt_of_le_of_lt (hF a b) (by
      calc
        C * Real.sqrt |a - b| < C * (η / C) := mul_lt_mul_of_pos_left hsqrt hCpos
        _ = η := by field_simp)

/-- The second bridge at the interface available in the final theorem: smoothness
supplies the measurability omitted from the standalone quantitative statement. -/
lemma apm_m02J06_bridge_2_of_contDiff
    {φ : ℝ → ℝ} {M : ℝ} (hφsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφbound : ∀ x, |φ x| ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∀ f ∈ apm_m02J06_K, ∀ x y : ℝ,
      |apm_m02J06_convolution f (apm_m02J06_mollifier φ ε) x -
        apm_m02J06_convolution f (apm_m02J06_mollifier φ ε) y| ≤
          (M / ε) * Real.sqrt |x - y| := by
  intro ε hε f hf x y
  have hM : 0 ≤ M := by
    exact (abs_nonneg (φ 0)).trans (hφbound 0)
  apply apm_m02J06_bounded_kernel_translation (g := apm_m02J06_mollifier φ ε)
      hf (C := M / ε) _ (div_nonneg hM hε.le) _ x y
  · have hc : Continuous (apm_m02J06_mollifier φ ε) := by
      unfold apm_m02J06_mollifier
      fun_prop
    exact hc.aestronglyMeasurable
  · intro t
    change |ε⁻¹ * φ (t / ε)| ≤ M / ε
    rw [abs_mul, abs_inv, abs_of_pos hε]
    calc
      ε⁻¹ * |φ (t / ε)| ≤ ε⁻¹ * M :=
        mul_le_mul_of_nonneg_left (hφbound (t / ε)) (inv_nonneg.mpr hε.le)
      _ = M / ε := by rw [div_eq_mul_inv, mul_comm]

/-- Why this unblocks `apm_m02j06`: this is the second missing Tonelli
estimate. It turns the translation control on `f` and the uniform bound on
the mollifier into the equicontinuity modulus used by Arzelà--Ascoli. -/
theorem apm_m02J06_bridge_2
    {φ : ℝ → ℝ} {M : ℝ} (hφsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφbound : ∀ x, |φ x| ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∀ f ∈ apm_m02J06_K, ∀ x y : ℝ,
      |apm_m02J06_convolution f (apm_m02J06_mollifier φ ε) x -
        apm_m02J06_convolution f (apm_m02J06_mollifier φ ε) y| ≤
          (M / ε) * Real.sqrt |x - y| := by
  exact apm_m02J06_bridge_2_of_contDiff hφsmooth hφbound

/-- A concrete normalized kernel used for the compactness proof.  Smoothness
is unnecessary there: the first bridge only needs positivity, mass and
support, while continuity of the convolution follows from translation of
`f`. -/
noncomputable def apm_m02J06_boxKernel : ℝ → ℝ :=
  (Ioo (-1 : ℝ) 1).indicator (fun _ ↦ (2 : ℝ)⁻¹)

lemma apm_m02J06_boxKernel_nonneg (x : ℝ) : 0 ≤ apm_m02J06_boxKernel x := by
  by_cases hx : x ∈ Ioo (-1 : ℝ) 1 <;> simp [apm_m02J06_boxKernel, hx]

lemma apm_m02J06_boxKernel_bound (x : ℝ) :
    |apm_m02J06_boxKernel x| ≤ (2 : ℝ)⁻¹ := by
  by_cases hx : x ∈ Ioo (-1 : ℝ) 1 <;> simp [apm_m02J06_boxKernel, hx]

lemma apm_m02J06_boxKernel_support (x : ℝ) (hx : 1 ≤ |x|) :
    apm_m02J06_boxKernel x = 0 := by
  by_cases hxi : x ∈ Ioo (-1 : ℝ) 1
  · exact (not_lt_of_ge hx (abs_lt.mpr hxi)).elim
  · simp [apm_m02J06_boxKernel, hxi]

lemma apm_m02J06_boxKernel_integrable :
    Integrable apm_m02J06_boxKernel volume := by
  exact (integrableOn_const (s := Ioo (-1 : ℝ) 1)
    (by simp [Real.volume_Ioo])).integrable_indicator measurableSet_Ioo

lemma apm_m02J06_boxKernel_integral :
    ∫ x, apm_m02J06_boxKernel x ∂volume = 1 := by
  rw [apm_m02J06_boxKernel, integral_indicator measurableSet_Ioo]
  norm_num

lemma apm_m02J06_box_approximation
    {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ} (hf : f ∈ apm_m02J06_K) :
    ∫ x, |f x - apm_m02J06_convolution f
      (apm_m02J06_mollifier apm_m02J06_boxKernel ε) x| ∂volume ≤ Real.sqrt ε := by
  exact apm_m02J06_bridge_1 apm_m02J06_boxKernel_nonneg
    apm_m02J06_boxKernel_integral apm_m02J06_boxKernel_support ε hε f hf

lemma apm_m02J06_box_convolution_modulus
    {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ} (hf : f ∈ apm_m02J06_K)
    (x y : ℝ) :
    |apm_m02J06_convolution f
        (apm_m02J06_mollifier apm_m02J06_boxKernel ε) x -
      apm_m02J06_convolution f
        (apm_m02J06_mollifier apm_m02J06_boxKernel ε) y| ≤
      ((2 : ℝ)⁻¹ / ε) * Real.sqrt |x - y| := by
  let g := apm_m02J06_mollifier apm_m02J06_boxKernel ε
  have hg : Integrable g volume := apm_m02J06_mollifier_integrable
    apm_m02J06_boxKernel_nonneg apm_m02J06_boxKernel_integral hε
  apply apm_m02J06_bounded_kernel_translation hf hg.aestronglyMeasurable
    (C := (2 : ℝ)⁻¹ / ε) (div_nonneg (by positivity) hε.le) _ x y
  intro t
  change |ε⁻¹ * apm_m02J06_boxKernel (t / ε)| ≤ (2 : ℝ)⁻¹ / ε
  rw [abs_mul, abs_inv, abs_of_pos hε]
  calc
    ε⁻¹ * |apm_m02J06_boxKernel (t / ε)| ≤ ε⁻¹ * (2 : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (apm_m02J06_boxKernel_bound _) (inv_nonneg.mpr hε.le)
    _ = (2 : ℝ)⁻¹ / ε := by rw [div_eq_mul_inv, mul_comm]

lemma apm_m02J06_box_convolution_continuous
    {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ} (hf : f ∈ apm_m02J06_K) :
    Continuous (apm_m02J06_convolution f
      (apm_m02J06_mollifier apm_m02J06_boxKernel ε)) := by
  apply apm_m02J06_continuous_of_sqrt_modulus
    (C := (2 : ℝ)⁻¹ / ε) (div_nonneg (by positivity) hε.le)
  exact apm_m02J06_box_convolution_modulus hε hf

lemma apm_m02J06_box_convolution_bound
    {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ} (hf : f ∈ apm_m02J06_K)
    (x : ℝ) :
    |apm_m02J06_convolution f
      (apm_m02J06_mollifier apm_m02J06_boxKernel ε) x| ≤ (2 : ℝ)⁻¹ / ε := by
  let g := apm_m02J06_mollifier apm_m02J06_boxKernel ε
  have hg : Integrable g volume := apm_m02J06_mollifier_integrable
    apm_m02J06_boxKernel_nonneg apm_m02J06_boxKernel_integral hε
  have hC : 0 ≤ (2 : ℝ)⁻¹ / ε := div_nonneg (by positivity) hε.le
  refine (apm_m02J06_convolution_abs_le hf.1 hg.aestronglyMeasurable hC ?_ x).trans ?_
  · intro t
    change |ε⁻¹ * apm_m02J06_boxKernel (t / ε)| ≤ (2 : ℝ)⁻¹ / ε
    rw [abs_mul, abs_inv, abs_of_pos hε]
    calc
      ε⁻¹ * |apm_m02J06_boxKernel (t / ε)| ≤ ε⁻¹ * (2 : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left (apm_m02J06_boxKernel_bound _) (inv_nonneg.mpr hε.le)
      _ = (2 : ℝ)⁻¹ / ε := by rw [div_eq_mul_inv, mul_comm]
  · simpa using mul_le_mul_of_nonneg_left hf.2.1 hC

lemma apm_m02J06_box_convolution_support
    {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ} (hf : f ∈ apm_m02J06_K)
    {x : ℝ} (hx : 1 + ε ≤ |x|) :
    apm_m02J06_convolution f
      (apm_m02J06_mollifier apm_m02J06_boxKernel ε) x = 0 :=
  apm_m02J06_convolution_eq_zero apm_m02J06_boxKernel_support hε hf hx

/-- A fixed-scale convolution restricted to its common compact interval. -/
noncomputable def apm_m02J06_boxBCF
    (ε : ℝ) (hε : 0 < ε) (f : ℝ → ℝ) (hf : f ∈ apm_m02J06_K) :
    BoundedContinuousFunction {x : ℝ // x ∈ Icc (-(1 + ε)) (1 + ε)} ℝ :=
  BoundedContinuousFunction.mkOfCompact (α :=
      {x : ℝ // x ∈ Icc (-(1 + ε)) (1 + ε)})
    ⟨fun x ↦ apm_m02J06_convolution f
        (apm_m02J06_mollifier apm_m02J06_boxKernel ε) (x : ℝ),
      (apm_m02J06_box_convolution_continuous hε hf).comp
        (continuous_subtype_val : Continuous fun x :
          {x : ℝ // x ∈ Icc (-(1 + ε)) (1 + ε)} ↦ (x : ℝ))⟩

/-- The family of all fixed-scale compact-domain approximants. -/
def apm_m02J06_boxFamily (ε : ℝ) (hε : 0 < ε) :
    Set (BoundedContinuousFunction
      {x : ℝ // x ∈ Icc (-(1 + ε)) (1 + ε)} ℝ) :=
  {F | ∃ (f : ℝ → ℝ) (hf : f ∈ apm_m02J06_K),
    F = apm_m02J06_boxBCF ε hε f hf}

lemma apm_m02J06_boxFamily_range
    {ε : ℝ} (hε : 0 < ε)
    (F : BoundedContinuousFunction
      {x : ℝ // x ∈ Icc (-(1 + ε)) (1 + ε)} ℝ)
    (x : {x : ℝ // x ∈ Icc (-(1 + ε)) (1 + ε)})
    (hF : F ∈ apm_m02J06_boxFamily ε hε) :
    F x ∈ Icc (-((2 : ℝ)⁻¹ / ε)) ((2 : ℝ)⁻¹ / ε) := by
  rcases hF with ⟨f, hf, rfl⟩
  rw [mem_Icc]
  change -((2 : ℝ)⁻¹ / ε) ≤ apm_m02J06_convolution f
      (apm_m02J06_mollifier apm_m02J06_boxKernel ε) x ∧
    apm_m02J06_convolution f
      (apm_m02J06_mollifier apm_m02J06_boxKernel ε) x ≤ (2 : ℝ)⁻¹ / ε
  exact abs_le.mp (apm_m02J06_box_convolution_bound hε hf x)

lemma apm_m02J06_boxFamily_equicontinuous
    {ε : ℝ} (hε : 0 < ε) :
    Equicontinuous ((↑) : apm_m02J06_boxFamily ε hε →
      {x : ℝ // x ∈ Icc (-(1 + ε)) (1 + ε)} → ℝ) := by
  intro x₀
  rw [Metric.equicontinuousAt_iff_pair]
  intro η hη
  let C : ℝ := (2 : ℝ)⁻¹ / ε
  have hC : 0 < C := div_pos (by positivity) hε
  let δ : ℝ := (η / C) ^ 2
  have hδ : 0 < δ := sq_pos_of_pos (div_pos hη hC)
  refine ⟨Metric.ball x₀ (δ / 2), Metric.ball_mem_nhds x₀ (half_pos hδ), ?_⟩
  intro x hx y hy F
  rcases F.2 with ⟨f, hf, hF⟩
  have hxy : dist x y < δ := by
    calc
      dist x y ≤ dist x x₀ + dist y x₀ := dist_triangle_right _ _ _
      _ < δ / 2 + δ / 2 := add_lt_add hx hy
      _ = δ := add_halves δ
  have hsqrt : Real.sqrt |(x : ℝ) - (y : ℝ)| < η / C := by
    rw [Real.sqrt_lt' (div_pos hη hC)]
    simpa [δ, Real.dist_eq, sq] using hxy
  rw [hF]
  change dist
      (apm_m02J06_convolution f (apm_m02J06_mollifier apm_m02J06_boxKernel ε) x)
      (apm_m02J06_convolution f (apm_m02J06_mollifier apm_m02J06_boxKernel ε) y) < η
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (apm_m02J06_box_convolution_modulus hε hf x y) (by
    change C * Real.sqrt |(x : ℝ) - (y : ℝ)| < η
    calc
      C * Real.sqrt |(x : ℝ) - (y : ℝ)| < C * (η / C) :=
        mul_lt_mul_of_pos_left hsqrt hC
      _ = η := by field_simp)

lemma apm_m02J06_boxFamily_compact_closure
    {ε : ℝ} (hε : 0 < ε) :
    IsCompact (closure (apm_m02J06_boxFamily ε hε)) := by
  exact BoundedContinuousFunction.arzela_ascoli
    (Icc (-((2 : ℝ)⁻¹ / ε)) ((2 : ℝ)⁻¹ / ε)) isCompact_Icc
    (apm_m02J06_boxFamily ε hε)
    (fun F x hF ↦ apm_m02J06_boxFamily_range hε F x hF)
    (apm_m02J06_boxFamily_equicontinuous hε)

lemma apm_m02J06_boxFamily_totallyBounded
    {ε : ℝ} (hε : 0 < ε) :
    TotallyBounded (apm_m02J06_boxFamily ε hε) :=
  TotallyBounded.subset subset_closure
    (apm_m02J06_boxFamily_compact_closure hε).totallyBounded

/-- Extend a compact-interval approximant by zero to the full real line. -/
noncomputable def apm_m02J06_boxExtend
    (ε : ℝ)
    (F : BoundedContinuousFunction
      {x : ℝ // x ∈ Icc (-(1 + ε)) (1 + ε)} ℝ) : ℝ → ℝ :=
  fun x ↦ if hx : x ∈ Icc (-(1 + ε)) (1 + ε) then F ⟨x, hx⟩ else 0

lemma apm_m02J06_boxExtend_measurable
    (ε : ℝ)
    (F : BoundedContinuousFunction
      {x : ℝ // x ∈ Icc (-(1 + ε)) (1 + ε)} ℝ) :
    Measurable (apm_m02J06_boxExtend ε F) := by
  exact F.continuous.measurable.dite measurable_const measurableSet_Icc

lemma apm_m02J06_boxExtend_integrable
    {ε : ℝ} (_hε : 0 < ε)
    (F : BoundedContinuousFunction
      {x : ℝ // x ∈ Icc (-(1 + ε)) (1 + ε)} ℝ) :
    Integrable (apm_m02J06_boxExtend ε F) volume := by
  have hR : volume (Icc (-(1 + ε)) (1 + ε)) ≠ ⊤ := by
    simp [Real.volume_Icc]
  have hmajor : Integrable
      ((Icc (-(1 + ε)) (1 + ε)).indicator (fun _ : ℝ ↦ ‖F‖)) volume :=
    (integrableOn_const hR).integrable_indicator measurableSet_Icc
  apply hmajor.mono' (apm_m02J06_boxExtend_measurable ε F).aestronglyMeasurable
  filter_upwards with x
  by_cases hx : x ∈ Icc (-(1 + ε)) (1 + ε)
  · simp only [apm_m02J06_boxExtend, dif_pos hx, indicator_of_mem hx, Real.norm_eq_abs]
    exact BoundedContinuousFunction.norm_coe_le_norm F ⟨x, hx⟩
  · rw [apm_m02J06_boxExtend, dif_neg hx, Set.indicator_of_notMem hx]
    simp

lemma apm_m02J06_boxExtend_boxBCF
    {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ} (hf : f ∈ apm_m02J06_K) (x : ℝ) :
    apm_m02J06_boxExtend ε (apm_m02J06_boxBCF ε hε f hf) x =
      apm_m02J06_convolution f
        (apm_m02J06_mollifier apm_m02J06_boxKernel ε) x := by
  by_cases hx : x ∈ Icc (-(1 + ε)) (1 + ε)
  · rw [apm_m02J06_boxExtend, dif_pos hx]
    rfl
  · have hrad : 1 + ε ≤ |x| := by
      rw [mem_Icc, not_and_or] at hx
      rcases hx with hx | hx
      · have hxn : x < 0 := lt_of_lt_of_le (lt_of_not_ge hx) (by linarith)
        rw [abs_of_neg hxn]
        linarith [lt_of_not_ge hx]
      · have hxp : 0 < x := lt_of_le_of_lt (by linarith) (lt_of_not_ge hx)
        rw [abs_of_pos hxp]
        exact (lt_of_not_ge hx).le
    rw [apm_m02J06_boxExtend, dif_neg hx,
      apm_m02J06_box_convolution_support hε hf hrad]

lemma apm_m02J06_norm_toL1_eq_integral_abs
    (f : ℝ → ℝ) (hf : Integrable f volume) :
    ‖apm_m02J06_toL1 f hf‖ = ∫ x, |f x| ∂volume := by
  rw [apm_m02J06_toL1, Lp.norm_toLp,
    toReal_eLpNorm hf.aestronglyMeasurable]
  exact lpNorm_one_eq_integral_norm hf.aestronglyMeasurable

/-- Zero extension followed by the canonical `L¹` quotient map. -/
noncomputable def apm_m02J06_boxToL1
    (ε : ℝ) (hε : 0 < ε)
    (F : BoundedContinuousFunction
      {x : ℝ // x ∈ Icc (-(1 + ε)) (1 + ε)} ℝ) :
    Lp ℝ 1 (volume : Measure ℝ) :=
  apm_m02J06_toL1 (apm_m02J06_boxExtend ε F)
    (apm_m02J06_boxExtend_integrable hε F)

lemma apm_m02J06_boxToL1_dist_le
    {ε : ℝ} (hε : 0 < ε)
    (F G : BoundedContinuousFunction
      {x : ℝ // x ∈ Icc (-(1 + ε)) (1 + ε)} ℝ) :
    dist (apm_m02J06_boxToL1 ε hε F) (apm_m02J06_boxToL1 ε hε G) ≤
      (2 * (1 + ε)) * dist F G := by
  let f := apm_m02J06_boxExtend ε F
  let g := apm_m02J06_boxExtend ε G
  have hf : Integrable f volume := apm_m02J06_boxExtend_integrable hε F
  have hg : Integrable g volume := apm_m02J06_boxExtend_integrable hε G
  rw [dist_eq_norm]
  change ‖apm_m02J06_toL1 f hf - apm_m02J06_toL1 g hg‖ ≤ _
  change ‖hf.toL1 f - hg.toL1 g‖ ≤ _
  rw [← Integrable.toL1_sub]
  change ‖apm_m02J06_toL1 (f - g) (hf.sub hg)‖ ≤ _
  rw [apm_m02J06_norm_toL1_eq_integral_abs]
  have hR : volume (Icc (-(1 + ε)) (1 + ε)) ≠ ⊤ := by
    simp [Real.volume_Icc]
  have hmajor : Integrable
      ((Icc (-(1 + ε)) (1 + ε)).indicator (fun _ : ℝ ↦ dist F G)) volume :=
    (integrableOn_const hR).integrable_indicator measurableSet_Icc
  calc
    (∫ x, |(f - g) x| ∂volume) ≤
        ∫ x, (Icc (-(1 + ε)) (1 + ε)).indicator
          (fun _ : ℝ ↦ dist F G) x ∂volume := by
      apply integral_mono_ae (hf.sub hg).abs hmajor
      filter_upwards with x
      by_cases hx : x ∈ Icc (-(1 + ε)) (1 + ε)
      · simp only [f, g, Pi.sub_apply, apm_m02J06_boxExtend, dif_pos hx,
          indicator_of_mem hx]
        simpa [Real.dist_eq] using
          (BoundedContinuousFunction.dist_coe_le_dist (f := F) (g := G) ⟨x, hx⟩)
      · simp only [f, g, Pi.sub_apply]
        rw [apm_m02J06_boxExtend, dif_neg hx, apm_m02J06_boxExtend, dif_neg hx,
          Set.indicator_of_notMem hx]
        simp
    _ = (2 * (1 + ε)) * dist F G := by
      rw [integral_indicator measurableSet_Icc]
      simp
      left
      rw [max_eq_left]
      · ring
      · linarith

lemma apm_m02J06_boxToL1_lipschitz
    {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith ⟨2 * (1 + ε), by positivity⟩ (apm_m02J06_boxToL1 ε hε) := by
  apply LipschitzWith.of_dist_le_mul
  intro F G
  exact apm_m02J06_boxToL1_dist_le hε F G

/-- Compact `L¹` target containing every fixed-scale box convolution. -/
def apm_m02J06_boxL1Compact (ε : ℝ) (hε : 0 < ε) :
    Set (Lp ℝ 1 (volume : Measure ℝ)) :=
  apm_m02J06_boxToL1 ε hε '' closure (apm_m02J06_boxFamily ε hε)

lemma apm_m02J06_boxL1Compact_isCompact
    {ε : ℝ} (hε : 0 < ε) : IsCompact (apm_m02J06_boxL1Compact ε hε) := by
  exact (apm_m02J06_boxFamily_compact_closure hε).image
    (apm_m02J06_boxToL1_lipschitz hε).continuous

lemma apm_m02J06_boxL1Compact_contains
    {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ} (hf : f ∈ apm_m02J06_K) :
    apm_m02J06_toL1
        (apm_m02J06_convolution f
          (apm_m02J06_mollifier apm_m02J06_boxKernel ε))
        (by
          have heq : apm_m02J06_boxExtend ε (apm_m02J06_boxBCF ε hε f hf) =
              apm_m02J06_convolution f
                (apm_m02J06_mollifier apm_m02J06_boxKernel ε) := by
            funext x
            exact apm_m02J06_boxExtend_boxBCF hε hf x
          rw [← heq]
          exact apm_m02J06_boxExtend_integrable hε _) ∈
      apm_m02J06_boxL1Compact ε hε := by
  refine ⟨apm_m02J06_boxBCF ε hε f hf, subset_closure ?_, ?_⟩
  · exact ⟨f, hf, rfl⟩
  · apply apm_m02J06_toL1_congr_ae
    exact Filter.Eventually.of_forall (apm_m02J06_boxExtend_boxBCF hε hf)

lemma apm_m02J06_toL1_box_distance
    {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ} (hf : f ∈ apm_m02J06_K) :
    let g := apm_m02J06_convolution f
      (apm_m02J06_mollifier apm_m02J06_boxKernel ε)
    let hg : Integrable g volume := by
      have heq : apm_m02J06_boxExtend ε (apm_m02J06_boxBCF ε hε f hf) = g := by
        funext x
        exact apm_m02J06_boxExtend_boxBCF hε hf x
      rw [← heq]
      exact apm_m02J06_boxExtend_integrable hε _
    dist (apm_m02J06_toL1 f hf.1) (apm_m02J06_toL1 g hg) ≤ Real.sqrt ε := by
  dsimp only
  let g := apm_m02J06_convolution f
    (apm_m02J06_mollifier apm_m02J06_boxKernel ε)
  have hg : Integrable g volume := by
    have heq : apm_m02J06_boxExtend ε (apm_m02J06_boxBCF ε hε f hf) = g := by
      funext x
      exact apm_m02J06_boxExtend_boxBCF hε hf x
    rw [← heq]
    exact apm_m02J06_boxExtend_integrable hε _
  rw [dist_eq_norm]
  change ‖hf.1.toL1 f - hg.toL1 g‖ ≤ _
  rw [← Integrable.toL1_sub]
  change ‖apm_m02J06_toL1 (f - g) (hf.1.sub hg)‖ ≤ _
  rw [apm_m02J06_norm_toL1_eq_integral_abs]
  exact apm_m02J06_box_approximation hε hf

lemma apm_m02J06_KL1_totallyBounded : TotallyBounded apm_m02J06_KL1 := by
  rw [Metric.totallyBounded_iff]
  intro η hη
  let ε : ℝ := (η / 4) ^ 2
  have hε : 0 < ε := sq_pos_of_pos (div_pos hη (by norm_num))
  have hsqrt : Real.sqrt ε = η / 4 := by
    dsimp only [ε]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (div_pos hη (by norm_num))]
  obtain ⟨t, _htsub, htfin, htcover⟩ :=
    (apm_m02J06_boxL1Compact_isCompact hε).finite_cover_balls (half_pos hη)
  refine ⟨t, htfin, ?_⟩
  intro u hu
  rcases hu with ⟨f, hfint, hfK, rfl⟩
  let g := apm_m02J06_convolution f
    (apm_m02J06_mollifier apm_m02J06_boxKernel ε)
  have hg : Integrable g volume := by
    have heq : apm_m02J06_boxExtend ε (apm_m02J06_boxBCF ε hε f hfK) = g := by
      funext x
      exact apm_m02J06_boxExtend_boxBCF hε hfK x
    rw [← heq]
    exact apm_m02J06_boxExtend_integrable hε _
  have hvg : apm_m02J06_toL1 g hg ∈ apm_m02J06_boxL1Compact ε hε :=
    apm_m02J06_boxL1Compact_contains hε hfK
  have hdist : dist (apm_m02J06_toL1 f hfint) (apm_m02J06_toL1 g hg) ≤ η / 4 := by
    simpa [hsqrt] using apm_m02J06_toL1_box_distance hε hfK
  rcases mem_iUnion₂.mp (htcover hvg) with ⟨v, hvt, hvball⟩
  refine mem_iUnion₂.mpr ⟨v, hvt, ?_⟩
  rw [Metric.mem_ball] at hvball ⊢
  calc
    dist (apm_m02J06_toL1 f hfint) v ≤
        dist (apm_m02J06_toL1 f hfint) (apm_m02J06_toL1 g hg) +
          dist (apm_m02J06_toL1 g hg) v := dist_triangle _ _ _
    _ < η / 4 + η / 2 := add_lt_add_of_le_of_lt hdist hvball
    _ < η := by linarith

/-- Translation on `L¹`, packaged as the canonical linear isometry. -/
noncomputable def apm_m02J06_shiftL1 (h : ℝ) :
    Lp ℝ 1 (volume : Measure ℝ) →ₗᵢ[ℝ] Lp ℝ 1 (volume : Measure ℝ) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : ℝ ↦ x + h)
    (measurePreserving_add_right volume h)

lemma apm_m02J06_KL1_norm {u : Lp ℝ 1 (volume : Measure ℝ)}
    (hu : u ∈ apm_m02J06_KL1) : ‖u‖ ≤ 1 := by
  rcases hu with ⟨f, hf, hfK, rfl⟩
  rw [apm_m02J06_norm_toL1_eq_integral_abs]
  exact hfK.2.1

lemma apm_m02J06_KL1_shift {u : Lp ℝ 1 (volume : Measure ℝ)}
    (hu : u ∈ apm_m02J06_KL1) {h : ℝ} (hh : 0 < h) :
    ‖apm_m02J06_shiftL1 h u - u‖ ≤ Real.sqrt h := by
  rcases hu with ⟨f, hf, hfK, rfl⟩
  have hft : Integrable (fun x : ℝ ↦ f (x + h)) volume :=
    hf.comp_add_right h
  have heq : apm_m02J06_shiftL1 h (apm_m02J06_toL1 f hf) =
      apm_m02J06_toL1 (fun x ↦ f (x + h)) hft := by
    have hfx := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp
      (MemLp.coeFn_toLp (memLp_one_iff_integrable.2 hf))
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving
      (apm_m02J06_toL1 f hf) (measurePreserving_add_right volume h),
      hfx, MemLp.coeFn_toLp (memLp_one_iff_integrable.2 hft)] with x hx hfx hftx
    exact hx.trans hfx |>.trans hftx.symm
  rw [heq]
  change ‖hft.toL1 (fun x ↦ f (x + h)) - hf.toL1 f‖ ≤ _
  rw [← Integrable.toL1_sub]
  change ‖apm_m02J06_toL1 ((fun x ↦ f (x + h)) - f) (hft.sub hf)‖ ≤ _
  rw [apm_m02J06_norm_toL1_eq_integral_abs]
  simpa only [Pi.sub_apply] using hfK.2.2.1 h hh

lemma apm_m02J06_KL1_support_ae {u : Lp ℝ 1 (volume : Measure ℝ)}
    (hu : u ∈ apm_m02J06_KL1) :
    ∀ᵐ x ∂volume, x ∉ Icc (-1 : ℝ) 1 → u x = 0 := by
  rcases hu with ⟨f, hf, hfK, rfl⟩
  filter_upwards [MemLp.coeFn_toLp (memLp_one_iff_integrable.2 hf)] with x hx hxo
  rw [apm_m02J06_toL1, hx]
  apply hfK.2.2.2 x
  rw [mem_Icc, not_and_or] at hxo
  rcases hxo with hxo | hxo
  · have hxneg : x < 0 := lt_of_lt_of_le (lt_of_not_ge hxo) (by norm_num)
    rw [abs_of_neg hxneg]
    linarith
  · have hxpos : 0 < x := lt_of_le_of_lt (by norm_num) (lt_of_not_ge hxo)
    rw [abs_of_pos hxpos]
    exact (lt_of_not_ge hxo).le

lemma apm_m02J06_KL1_isClosed : IsClosed apm_m02J06_KL1 := by
  apply IsSeqClosed.isClosed
  intro u u₀ hu hut
  have hnorm : ‖u₀‖ ≤ 1 := by
    exact le_of_tendsto (tendsto_norm.comp hut) (Filter.Eventually.of_forall fun n ↦
      apm_m02J06_KL1_norm (hu n))
  have hshift : ∀ h : ℝ, 0 < h →
      ‖apm_m02J06_shiftL1 h u₀ - u₀‖ ≤ Real.sqrt h := by
    intro h hh
    have ht : Filter.Tendsto (fun n ↦ apm_m02J06_shiftL1 h (u n) - u n)
        Filter.atTop (nhds (apm_m02J06_shiftL1 h u₀ - u₀)) :=
      (((apm_m02J06_shiftL1 h).continuous.tendsto u₀).comp hut).sub hut
    exact le_of_tendsto (tendsto_norm.comp ht) (Filter.Eventually.of_forall fun n ↦
      apm_m02J06_KL1_shift (hu n) hh)
  obtain ⟨ns, _hns, hpoint⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hut).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂volume, ∀ n : ℕ,
      x ∉ Icc (-1 : ℝ) 1 → u (ns n) x = 0 :=
    ae_all_iff.2 (fun n ↦ apm_m02J06_KL1_support_ae (hu (ns n)))
  have hsupp : ∀ᵐ x ∂volume, x ∉ Icc (-1 : ℝ) 1 → u₀ x = 0 := by
    filter_upwards [hpoint, hall] with x hx hsx hxo
    exact tendsto_nhds_unique hx (tendsto_const_nhds.congr' <|
      Filter.Eventually.of_forall fun n ↦ (hsx n hxo).symm)
  have hboundary : ∀ᵐ x ∂volume, x ≠ (-1 : ℝ) ∧ x ≠ 1 := by
    have hm₁ : ∀ᵐ x ∂volume, x ≠ (-1 : ℝ) := ae_iff.2 (by simp)
    have hp₁ : ∀ᵐ x ∂volume, x ≠ (1 : ℝ) := ae_iff.2 (by simp)
    filter_upwards [hm₁, hp₁] with x hx₁ hx₂
    exact ⟨hx₁, hx₂⟩
  let f : ℝ → ℝ := (Ioo (-1 : ℝ) 1).indicator (fun x ↦ u₀ x)
  have hfmem : MemLp f 1 volume := (Lp.memLp u₀).indicator measurableSet_Ioo
  have hf : Integrable f volume := memLp_one_iff_integrable.1 hfmem
  have hfu : f =ᵐ[volume] fun x ↦ u₀ x := by
    filter_upwards [hsupp, hboundary] with x hx hb
    by_cases hxi : x ∈ Ioo (-1 : ℝ) 1
    · simp [f, hxi]
    · have hxo : x ∉ Icc (-1 : ℝ) 1 := by
        intro hc
        rw [mem_Icc] at hc
        rcases hc with ⟨hc₁, hc₂⟩
        apply hxi
        rw [mem_Ioo]
        exact And.intro (lt_of_le_of_ne hc₁ (Ne.symm hb.1))
          (lt_of_le_of_ne hc₂ hb.2)
      simp [f, hxi, hx hxo]
  have hto : apm_m02J06_toL1 f hf = u₀ := by
    rw [apm_m02J06_toL1]
    exact (MemLp.toLp_eq_toLp_iff hfmem (Lp.memLp u₀)).2 hfu
      |>.trans (Lp.toLp_coeFn u₀ (Lp.memLp u₀))
  change ∃ (g : ℝ → ℝ) (hg : Integrable g volume),
    g ∈ apm_m02J06_K ∧ u₀ = apm_m02J06_toL1 g hg
  refine ⟨f, hf, ?_, hto.symm⟩
  change Integrable f volume ∧ (∫ x, |f x| ∂volume) ≤ 1 ∧
    (∀ h : ℝ, 0 < h → (∫ x, |f (x + h) - f x| ∂volume) ≤ Real.sqrt h) ∧
    ∀ x : ℝ, 1 ≤ |x| → f x = 0
  refine ⟨hf, ?_, ?_, ?_⟩
  · calc
      (∫ x, |f x| ∂volume) = ‖apm_m02J06_toL1 f hf‖ :=
        (apm_m02J06_norm_toL1_eq_integral_abs f hf).symm
      _ = ‖u₀‖ := congrArg norm hto
      _ ≤ 1 := hnorm
  · intro h hh
    have hft : Integrable (fun x : ℝ ↦ f (x + h)) volume := hf.comp_add_right h
    have heq : apm_m02J06_toL1 (fun x ↦ f (x + h)) hft =
        apm_m02J06_shiftL1 h u₀ := by
      rw [← hto]
      have hfx := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp
        (MemLp.coeFn_toLp (memLp_one_iff_integrable.2 hf))
      apply Lp.ext
      filter_upwards [Lp.coeFn_compMeasurePreserving
        (apm_m02J06_toL1 f hf) (measurePreserving_add_right volume h),
        hfx, MemLp.coeFn_toLp (memLp_one_iff_integrable.2 hft)] with x hx hfx hftx
      exact hftx.trans (hfx.symm.trans hx.symm)
    let d : ℝ → ℝ := (fun x ↦ f (x + h)) - f
    have hd : Integrable d volume := hft.sub hf
    calc
      (∫ x, |f (x + h) - f x| ∂volume) = ∫ x, |d x| ∂volume := by rfl
      _ = ‖apm_m02J06_toL1 d hd‖ :=
        (apm_m02J06_norm_toL1_eq_integral_abs d hd).symm
      _ = ‖apm_m02J06_shiftL1 h u₀ - u₀‖ := by
        change ‖apm_m02J06_toL1 (fun x ↦ f (x + h)) hft -
          apm_m02J06_toL1 f hf‖ = _
        rw [heq, hto]
      _ ≤ Real.sqrt h := hshift h hh
  · intro x hx
    simp only [f, indicator]
    split_ifs with hxi
    · exfalso
      rw [mem_Ioo] at hxi
      have : |x| < 1 := abs_lt.2 hxi
      linarith
    · rfl

/-- Why this unblocks `apm_m02j06`: this is the remaining
Arzelà--Ascoli/finite-net/closedness interface after the two quantitative
estimates. It states compactness for the actual `L¹` quotient-set in the
frozen theorem, not merely for chosen function representatives. -/
theorem apm_m02J06_bridge_3 : IsCompact apm_m02J06_KL1 := by
  rw [isCompact_iff_totallyBounded_isComplete]
  exact ⟨apm_m02J06_KL1_totallyBounded,
    apm_m02J06_KL1_isClosed.isComplete⟩

theorem apm_m02j06 :
    ∀ (φ : ℝ → ℝ) (M : ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      (∀ x, 0 ≤ φ x) →
      ∫ x, φ x ∂volume = 1 →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      (∀ x, |φ x| ≤ M) →
      (∃ x, |φ x| = M) →
      (∀ ε : ℝ, 0 < ε → ∀ f ∈ apm_m02J06_K,
        ∫ x, |f x - apm_m02J06_convolution f
          (apm_m02J06_mollifier φ ε) x| ∂volume ≤ Real.sqrt ε) ∧
      (∀ ε : ℝ, 0 < ε → ∀ f ∈ apm_m02J06_K, ∀ x y : ℝ,
        |apm_m02J06_convolution f (apm_m02J06_mollifier φ ε) x -
          apm_m02J06_convolution f (apm_m02J06_mollifier φ ε) y| ≤
            (M / ε) * Real.sqrt |x - y|) ∧
      IsCompact apm_m02J06_KL1 := by
  /-
  SKIPPED (Kolmogorov–Riesz/L¹ quotient bridge). Mathlib searches found the
  general convolution integral API (`integral_convolution`) and abstract
  Arzelà–Ascoli theorems, but no Kolmogorov–Riesz compactness criterion for
  `Lp`, nor a compiled theorem transferring a uniformly supported,
  equicontinuous family of mollified representatives into total boundedness of
  their `L¹` equivalence classes.

  Closer hop 1 closes the first item in that list:
  `apm_m02J06_translation_estimate` extends the one-sided estimate to every
  real shift, using `integral_add_right_eq_self` (and the same translation
  principle as `integral_translate_norm` from solved artifact `a95J08`).
  `ConstructionTargets.YoungConvolution` supplies `convolution_memLp` and
  Young's inequality, but neither gives compactness.  A renewed search found
  `BoundedContinuousFunction.arzela_ascoli` and
  `isCompact_iff_totallyBounded_isComplete`; these can provide the abstract
  compactness step only after the mollified functions have been bundled with
  a common compact domain/range and their sup-norm nets transported to `Lp`.

  The remaining bridge is therefore to justify the Tonelli interchanges and
  rescaled-mollifier normalization/support bounds, build those bounded
  continuous maps, transfer their finite sup-norm nets to `L¹`, and prove
  `apm_m02J06_KL1` closed under changes of representatives modulo a.e.
  equality. `a96J02` contains convolution identities but no compactness route;
  `a96J03` only records an unfinished translation-continuity plan. The frozen
  statement was left unchanged.

  CLOSER HOP 2: the rescaling and representative prerequisites are now closed.
  `apm_m02J06_toL1_congr_ae` proves independence of the integrable
  representative. `apm_m02J06_mollifier_nonneg` and
  `apm_m02J06_mollifier_eq_zero` prove nonnegativity and support radius `ε`.
  `apm_m02J06_mollifier_integral_one` applies
  `Measure.integral_comp_mul_left` to prove exact normalization.

  Searches beyond hop 1 covered `ConstructionTargets.LpRepresentative`, Haar
  scaling, `LpSpace.Basic`, and convolution/Tonelli sources. They supplied the
  compiled quotient and scaling lemmas above, but no packaged route builds the
  equicontinuous compact-domain family or transfers Arzelà--Ascoli nets into
  `L¹`. The remaining bridge is the Tonelli estimates, bounded-continuous-map
  packaging, finite-net transfer, and final compactness argument. The frozen
  statement remains unchanged.

  CLOSER HOP 3 goes beyond the prior quotient/scaling work by proving
  `apm_m02J06_convolution_eq_zero`: every mollified representative vanishes
  outside radius `1 + ε`. The proof splits on whether the convolution variable
  lies outside the mollifier radius and otherwise uses the triangle inequality
  to put `x - t` outside the common support of `f`. Thus the common compact
  domain required by Arzelà--Ascoli is now compiled, rather than merely listed
  as a packaging obligation.

  Renewed searches covered Mathlib's general and bounded-continuous-function
  Arzelà--Ascoli theorems, total-boundedness/compactness criteria, convolution
  decay siblings (`a03J03`, `a97J03`), and the entire reusable module set. No
  Fréchet--Kolmogorov theorem or finite-net transfer into `Lp` was found. The
  remaining bridge is narrower: prove the two Tonelli convolution estimates,
  bundle the now uniformly supported mollifications as an equicontinuous
  bounded-continuous family, transport its sup-norm nets into `L¹`, and prove
  closedness of `apm_m02J06_KL1`. The frozen statement remains unchanged.
  -/
  intro φ M hφsmooth hφnonneg hφint hφsupport hφbound _hφmax
  exact ⟨apm_m02J06_bridge_1 hφnonneg hφint hφsupport,
    apm_m02J06_bridge_2 hφsmooth hφbound, apm_m02J06_bridge_3⟩
