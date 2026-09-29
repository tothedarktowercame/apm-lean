import Mathlib

/-!
# APM m99J02

## Statement repairs

Part (b) is given the standard minimal regularity hypothesis that `q` is continuous.
The source calls `u₁,u₂` classical solutions of `u'' + q u = 0` but states no
regularity for `q`; continuity makes the regular distribution `q g_y` unambiguous.

## Encoding questions

Distributional identities are stated in their exact weak form against every smooth,
compactly supported test function. No scalar or pointwise surrogate replaces `𝒟'(ℝ)`.
-/

noncomputable section

def apm_m99j02_IsTestFunction (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ

def apm_m99j02_g (u₁ u₂ : ℝ → ℝ) (y x : ℝ) : ℝ :=
  if x ≤ y then u₁ x * u₂ y else u₂ x * u₁ y

def apm_m99j02_Wronskian (u₁ u₂ : ℝ → ℝ) (y : ℝ) : ℝ :=
  u₁ y * deriv u₂ y - deriv u₁ y * u₂ y

def apm_m99j02_regularSecondDerivative
    (u₁ u₂ : ℝ → ℝ) (y x : ℝ) : ℝ :=
  if x < y then deriv (deriv u₁) x * u₂ y
  else deriv (deriv u₂) x * u₁ y

/-- The two branches of the Green kernel glue continuously, so its second
distributional derivative has no delta-prime contribution. -/
lemma apm_m99j02_g_continuous (u₁ u₂ : ℝ → ℝ)
    (hu₁ : Continuous u₁) (hu₂ : Continuous u₂) (y : ℝ) :
    Continuous (apm_m99j02_g u₁ u₂ y) := by
  unfold apm_m99j02_g
  apply (hu₁.mul continuous_const).if_le (hu₂.mul continuous_const)
    continuous_id continuous_const
  intro x hx
  change x = y at hx
  subst x
  exact mul_comm _ _

/-- The derivative of the glued kernel from the left. -/
lemma apm_m99j02_g_hasDerivWithinAt_Iic (u₁ u₂ : ℝ → ℝ)
    (hu₁ : Differentiable ℝ u₁) (y : ℝ) :
    HasDerivWithinAt (apm_m99j02_g u₁ u₂ y)
      (deriv u₁ y * u₂ y) (Set.Iic y) y := by
  have h := (hu₁ y).hasDerivAt.mul_const (u₂ y)
  apply h.hasDerivWithinAt.congr
  · intro x hx
    change x ≤ y at hx
    rw [apm_m99j02_g, if_pos hx]
  · simp [apm_m99j02_g]

/-- The derivative of the glued kernel from the right. -/
lemma apm_m99j02_g_hasDerivWithinAt_Ioi (u₁ u₂ : ℝ → ℝ)
    (hu₂ : Differentiable ℝ u₂) (y : ℝ) :
    HasDerivWithinAt (apm_m99j02_g u₁ u₂ y)
      (deriv u₂ y * u₁ y) (Set.Ioi y) y := by
  have h := (hu₂ y).hasDerivAt.mul_const (u₁ y)
  apply h.hasDerivWithinAt.congr
  · intro x hx
    change y < x at hx
    rw [apm_m99j02_g, if_neg (not_le.mpr hx)]
  · simp [apm_m99j02_g, mul_comm]

/-- The jump of the first derivative is exactly the Wronskian coefficient. -/
lemma apm_m99j02_g_derivative_jump (u₁ u₂ : ℝ → ℝ) (y : ℝ) :
    deriv u₂ y * u₁ y - deriv u₁ y * u₂ y =
      apm_m99j02_Wronskian u₁ u₂ y := by
  unfold apm_m99j02_Wronskian
  ring

/-- Multiplying a continuous coefficient by a test function gives an
integrable whole-line function.  This permits use of
`MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable`, avoiding
explicit limits at `±∞`. -/
lemma apm_m99j02_integrable_mul_test
    (u φ : ℝ → ℝ) (hu : Continuous u) (hφ : apm_m99j02_IsTestFunction φ) :
    MeasureTheory.Integrable (fun x : ℝ ↦ u x * φ x) MeasureTheory.volume := by
  apply (hu.mul hφ.1.continuous).integrable_of_hasCompactSupport
  simpa only [Pi.mul_apply] using hφ.2.mul_left (f := u)

/-- Integration by parts on a left half-line against a test function.  Compact
support supplies the boundary value at `-∞`. -/
lemma apm_m99j02_integral_Iic_mul_deriv
    (u φ : ℝ → ℝ) (hu : ContDiff ℝ 1 u)
    (hφ : apm_m99j02_IsTestFunction φ) (y : ℝ) :
    (∫ x in Set.Iic y, u x * deriv φ x) =
      u y * φ y - ∫ x in Set.Iic y, deriv u x * φ x := by
  have hat : Filter.atBot ≤ Filter.cocompact ℝ := by
    exact _root_.atBot_le_cocompact
  have h := MeasureTheory.integral_Iic_mul_deriv_eq_deriv_mul
      (a := y) (a' := u y * φ y) (b' := 0)
      (u := u) (v := φ) (u' := deriv u) (v' := deriv φ)
      (by
        intro x _
        exact (hu.differentiable (by norm_num) x).hasDerivAt)
      (by
        intro x _
        exact (hφ.1.differentiable (by simp) x).hasDerivAt)
      (by exact (apm_m99j02_integrable_mul_test u (deriv φ)
        hu.continuous ⟨(hφ.1.deriv' : ContDiff ℝ (⊤ : ℕ∞) (deriv φ)), hφ.2.deriv⟩).integrableOn)
      (by exact (apm_m99j02_integrable_mul_test (deriv u) φ
        hu.continuous_deriv_one hφ).integrableOn)
      (by exact (hu.continuous.mul hφ.1.continuous).continuousAt.continuousWithinAt)
      (by
        have hz := (hφ.2.mul_left (f := u)).is_zero_at_infty
        exact hz.mono_left hat)
  simpa only [Pi.mul_apply, sub_zero] using h

/-- The corresponding right-half-line integration-by-parts formula. -/
lemma apm_m99j02_integral_Ioi_mul_deriv
    (u φ : ℝ → ℝ) (hu : ContDiff ℝ 1 u)
    (hφ : apm_m99j02_IsTestFunction φ) (y : ℝ) :
    (∫ x in Set.Ioi y, u x * deriv φ x) =
      -(u y * φ y) - ∫ x in Set.Ioi y, deriv u x * φ x := by
  have hat : Filter.atTop ≤ Filter.cocompact ℝ := by
    exact _root_.atTop_le_cocompact
  have h := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
      (a := y) (a' := u y * φ y) (b' := 0)
      (u := u) (v := φ) (u' := deriv u) (v' := deriv φ)
      (by
        intro x _
        exact (hu.differentiable (by norm_num) x).hasDerivAt)
      (by
        intro x _
        exact (hφ.1.differentiable (by simp) x).hasDerivAt)
      (by exact (apm_m99j02_integrable_mul_test u (deriv φ)
        hu.continuous ⟨(hφ.1.deriv' : ContDiff ℝ (⊤ : ℕ∞) (deriv φ)), hφ.2.deriv⟩).integrableOn)
      (by exact (apm_m99j02_integrable_mul_test (deriv u) φ
        hu.continuous_deriv_one hφ).integrableOn)
      (by exact (hu.continuous.mul hφ.1.continuous).continuousAt.continuousWithinAt)
      (by
        have hz := (hφ.2.mul_left (f := u)).is_zero_at_infty
        exact hz.mono_left hat)
  simpa only [Pi.mul_apply, zero_sub] using h

lemma apm_m99j02_integral_Iic_mul_secondDeriv
    (u φ : ℝ → ℝ) (hu : ContDiff ℝ 2 u)
    (hφ : apm_m99j02_IsTestFunction φ) (y : ℝ) :
    (∫ x in Set.Iic y, u x * deriv (deriv φ) x) =
      u y * deriv φ y - deriv u y * φ y +
        ∫ x in Set.Iic y, deriv (deriv u) x * φ x := by
  have hφ' : apm_m99j02_IsTestFunction (deriv φ) :=
    ⟨(hφ.1.deriv' : ContDiff ℝ (⊤ : ℕ∞) (deriv φ)), hφ.2.deriv⟩
  rw [apm_m99j02_integral_Iic_mul_deriv u (deriv φ)
      (hu.of_le (by norm_num)) hφ' y,
    apm_m99j02_integral_Iic_mul_deriv (deriv u) φ
      (hu.deriv' : ContDiff ℝ 1 (deriv u)) hφ y]
  ring

lemma apm_m99j02_integral_Ioi_mul_secondDeriv
    (u φ : ℝ → ℝ) (hu : ContDiff ℝ 2 u)
    (hφ : apm_m99j02_IsTestFunction φ) (y : ℝ) :
    (∫ x in Set.Ioi y, u x * deriv (deriv φ) x) =
      -(u y * deriv φ y) + deriv u y * φ y +
        ∫ x in Set.Ioi y, deriv (deriv u) x * φ x := by
  have hφ' : apm_m99j02_IsTestFunction (deriv φ) :=
    ⟨(hφ.1.deriv' : ContDiff ℝ (⊤ : ℕ∞) (deriv φ)), hφ.2.deriv⟩
  rw [apm_m99j02_integral_Ioi_mul_deriv u (deriv φ)
      (hu.of_le (by norm_num)) hφ' y,
    apm_m99j02_integral_Ioi_mul_deriv (deriv u) φ
      (hu.deriv' : ContDiff ℝ 1 (deriv u)) hφ y]
  ring

lemma apm_m99j02_distributional_secondDerivative
    (u₁ u₂ : ℝ → ℝ) (hu₁ : ContDiff ℝ 2 u₁) (hu₂ : ContDiff ℝ 2 u₂)
    (y : ℝ) (φ : ℝ → ℝ) (hφ : apm_m99j02_IsTestFunction φ) :
    (∫ x : ℝ, apm_m99j02_g u₁ u₂ y x * deriv (deriv φ) x) =
      (∫ x : ℝ, apm_m99j02_regularSecondDerivative u₁ u₂ y x * φ x) +
        apm_m99j02_Wronskian u₁ u₂ y * φ y := by
  have hφ'' : apm_m99j02_IsTestFunction (deriv (deriv φ)) :=
    ⟨((hφ.1.deriv' : ContDiff ℝ (⊤ : ℕ∞) (deriv φ)).deriv' :
      ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv φ))), hφ.2.deriv.deriv⟩
  have hwhole := apm_m99j02_integrable_mul_test (apm_m99j02_g u₁ u₂ y)
    (deriv (deriv φ))
    (apm_m99j02_g_continuous u₁ u₂ hu₁.continuous hu₂.continuous y) hφ''
  rw [← intervalIntegral.integral_Iic_add_Ioi hwhole.integrableOn hwhole.integrableOn]
  have hleft : (∫ x in Set.Iic y,
      apm_m99j02_g u₁ u₂ y x * deriv (deriv φ) x) =
      u₂ y * (∫ x in Set.Iic y, u₁ x * deriv (deriv φ) x) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
    intro x hx
    change x ≤ y at hx
    simp only [apm_m99j02_g, if_pos hx]
    ring
  have hright : (∫ x in Set.Ioi y,
      apm_m99j02_g u₁ u₂ y x * deriv (deriv φ) x) =
      u₁ y * (∫ x in Set.Ioi y, u₂ x * deriv (deriv φ) x) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change y < x at hx
    simp only [apm_m99j02_g, if_neg (not_le.mpr hx)]
    ring
  rw [hleft, hright,
    apm_m99j02_integral_Iic_mul_secondDeriv u₁ φ hu₁ hφ y,
    apm_m99j02_integral_Ioi_mul_secondDeriv u₂ φ hu₂ hφ y]
  have hL0 : MeasureTheory.IntegrableOn
      (fun x ↦ deriv (deriv u₁) x * u₂ y * φ x) (Set.Iio y) :=
    (apm_m99j02_integrable_mul_test
      (fun x ↦ deriv (deriv u₁) x * u₂ y) φ
      ((hu₁.iterate_deriv' 0 2).continuous.mul continuous_const) hφ).integrableOn
  have hR0 : MeasureTheory.IntegrableOn
      (fun x ↦ deriv (deriv u₂) x * u₁ y * φ x) (Set.Ici y) :=
    (apm_m99j02_integrable_mul_test
      (fun x ↦ deriv (deriv u₂) x * u₁ y) φ
      ((hu₂.iterate_deriv' 0 2).continuous.mul continuous_const) hφ).integrableOn
  have hL : MeasureTheory.IntegrableOn
      (fun x ↦ apm_m99j02_regularSecondDerivative u₁ u₂ y x * φ x)
      (Set.Iio y) := by
    apply hL0.congr_fun
    · intro x hx
      change x < y at hx
      simp only [apm_m99j02_regularSecondDerivative, if_pos hx]
    · exact measurableSet_Iio
  have hR : MeasureTheory.IntegrableOn
      (fun x ↦ apm_m99j02_regularSecondDerivative u₁ u₂ y x * φ x)
      (Set.Ici y) := by
    apply hR0.congr_fun
    · intro x hx
      change y ≤ x at hx
      simp only [apm_m99j02_regularSecondDerivative, if_neg (not_lt.mpr hx)]
    · exact measurableSet_Ici
  rw [← intervalIntegral.integral_Iio_add_Ici hL hR]
  rw [MeasureTheory.integral_Iic_eq_integral_Iio,
    ← MeasureTheory.integral_Ici_eq_integral_Ioi]
  have hli : (∫ x in Set.Iio y,
      apm_m99j02_regularSecondDerivative u₁ u₂ y x * φ x) =
      u₂ y * ∫ x in Set.Iio y, deriv (deriv u₁) x * φ x := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Iio
    intro x hx
    change x < y at hx
    simp only [apm_m99j02_regularSecondDerivative, if_pos hx]
    ring
  have hri : (∫ x in Set.Ici y,
      apm_m99j02_regularSecondDerivative u₁ u₂ y x * φ x) =
      u₁ y * ∫ x in Set.Ici y, deriv (deriv u₂) x * φ x := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ici
    intro x hx
    change y ≤ x at hx
    simp only [apm_m99j02_regularSecondDerivative, if_neg (not_lt.mpr hx)]
    ring
  rw [hli, hri, apm_m99j02_Wronskian]
  ring

lemma apm_m99j02_wronskian_eq_zero
    (u₁ u₂ q : ℝ → ℝ) (hu₁ : ContDiff ℝ 2 u₁) (hu₂ : ContDiff ℝ 2 u₂)
    (hq₁ : ∀ x : ℝ, deriv (deriv u₁) x + q x * u₁ x = 0)
    (hq₂ : ∀ x : ℝ, deriv (deriv u₂) x + q x * u₂ x = 0) :
    ∀ y : ℝ, apm_m99j02_Wronskian u₁ u₂ y =
      apm_m99j02_Wronskian u₁ u₂ 0 := by
  have hu₁d : Differentiable ℝ u₁ := hu₁.differentiable (by norm_num)
  have hu₂d : Differentiable ℝ u₂ := hu₂.differentiable (by norm_num)
  have hdu₁d : Differentiable ℝ (deriv u₁) := hu₁.differentiable_deriv_two
  have hdu₂d : Differentiable ℝ (deriv u₂) := hu₂.differentiable_deriv_two
  have hW (x : ℝ) : HasDerivAt (apm_m99j02_Wronskian u₁ u₂) 0 x := by
    have hprod₁ := (hu₁d x).hasDerivAt.mul (hdu₂d x).hasDerivAt
    have hprod₂ := (hdu₁d x).hasDerivAt.mul (hu₂d x).hasDerivAt
    convert hprod₁.sub hprod₂ using 1
    rw [show deriv (deriv u₁) x = -(q x * u₁ x) from
        eq_neg_of_add_eq_zero_left (hq₁ x),
        show deriv (deriv u₂) x = -(q x * u₂ x) from
        eq_neg_of_add_eq_zero_left (hq₂ x)]
    ring
  intro y
  exact is_const_of_deriv_eq_zero
    (fun x => (hW x).differentiableAt) (fun x => (hW x).deriv) y 0

theorem apm_m99j02
    (u₁ u₂ : ℝ → ℝ) (hu₁ : ContDiff ℝ 2 u₁) (hu₂ : ContDiff ℝ 2 u₂) :
    (∀ (y : ℝ) (φ : ℝ → ℝ), apm_m99j02_IsTestFunction φ →
      (∫ x : ℝ, apm_m99j02_g u₁ u₂ y x * deriv (deriv φ) x) =
        (∫ x : ℝ, apm_m99j02_regularSecondDerivative u₁ u₂ y x * φ x) +
          apm_m99j02_Wronskian u₁ u₂ y * φ y) ∧
    ∀ q : ℝ → ℝ, Continuous q →
      (∀ x : ℝ, deriv (deriv u₁) x + q x * u₁ x = 0) →
      (∀ x : ℝ, deriv (deriv u₂) x + q x * u₂ x = 0) →
      ∀ (y : ℝ) (φ : ℝ → ℝ), apm_m99j02_IsTestFunction φ →
        (∫ x : ℝ, apm_m99j02_g u₁ u₂ y x *
          (deriv (deriv φ) x + q x * φ x)) =
            apm_m99j02_Wronskian u₁ u₂ 0 * φ y := by
  have hregular_cancel :
      ∀ (q : ℝ → ℝ),
        (∀ x : ℝ, deriv (deriv u₁) x + q x * u₁ x = 0) →
        (∀ x : ℝ, deriv (deriv u₂) x + q x * u₂ x = 0) →
        ∀ (y x : ℝ), x ≠ y →
          apm_m99j02_regularSecondDerivative u₁ u₂ y x +
              q x * apm_m99j02_g u₁ u₂ y x = 0 := by
    intro q hq₁ hq₂ y x hxy
    by_cases hlt : x < y
    · rw [apm_m99j02_regularSecondDerivative, if_pos hlt,
        apm_m99j02_g, if_pos hlt.le]
      rw [show deriv (deriv u₁) x = -(q x * u₁ x) from
        eq_neg_of_add_eq_zero_left (hq₁ x)]
      ring
    · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hxy)
      rw [apm_m99j02_regularSecondDerivative, if_neg hlt,
        apm_m99j02_g, if_neg (not_le.mpr hyx)]
      rw [show deriv (deriv u₂) x = -(q x * u₂ x) from
        eq_neg_of_add_eq_zero_left (hq₂ x)]
      ring
  constructor
  · intro y φ hφ
    exact apm_m99j02_distributional_secondDerivative u₁ u₂ hu₁ hu₂ y φ hφ
  · intro q hq hq₁ hq₂ y φ hφ
    have hgcont := apm_m99j02_g_continuous u₁ u₂ hu₁.continuous hu₂.continuous y
    have hφ'' : apm_m99j02_IsTestFunction (deriv (deriv φ)) :=
      ⟨((hφ.1.deriv' : ContDiff ℝ (⊤ : ℕ∞) (deriv φ)).deriv' :
        ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv φ))), hφ.2.deriv.deriv⟩
    have hsecond := apm_m99j02_integrable_mul_test
      (apm_m99j02_g u₁ u₂ y) (deriv (deriv φ)) hgcont hφ''
    have hqterm := apm_m99j02_integrable_mul_test
      (fun x ↦ apm_m99j02_g u₁ u₂ y x * q x) φ (hgcont.mul hq) hφ
    rw [show (∫ x : ℝ, apm_m99j02_g u₁ u₂ y x *
        (deriv (deriv φ) x + q x * φ x)) =
        (∫ x : ℝ, apm_m99j02_g u₁ u₂ y x * deriv (deriv φ) x) +
          ∫ x : ℝ, (apm_m99j02_g u₁ u₂ y x * q x) * φ x by
      rw [← MeasureTheory.integral_add hsecond hqterm]
      congr 1
      funext x
      ring]
    rw [apm_m99j02_distributional_secondDerivative u₁ u₂ hu₁ hu₂ y φ hφ]
    have hne : ∀ᵐ x : ℝ ∂MeasureTheory.volume, x ≠ y := by
      rw [MeasureTheory.ae_iff]
      simp
    have hae : (fun x ↦ apm_m99j02_regularSecondDerivative u₁ u₂ y x * φ x) =ᵐ[
        MeasureTheory.volume]
        (fun x ↦ -((apm_m99j02_g u₁ u₂ y x * q x) * φ x)) := by
      filter_upwards [hne] with x hx
      have hc := hregular_cancel q hq₁ hq₂ y x hx
      calc
        apm_m99j02_regularSecondDerivative u₁ u₂ y x * φ x =
            (apm_m99j02_regularSecondDerivative u₁ u₂ y x +
              q x * apm_m99j02_g u₁ u₂ y x) * φ x -
              (apm_m99j02_g u₁ u₂ y x * q x) * φ x := by ring
        _ = -((apm_m99j02_g u₁ u₂ y x * q x) * φ x) := by rw [hc]; ring
    have hreg : MeasureTheory.Integrable
        (fun x ↦ apm_m99j02_regularSecondDerivative u₁ u₂ y x * φ x) :=
      hqterm.neg.congr hae.symm
    have hcancel : (∫ x : ℝ,
        apm_m99j02_regularSecondDerivative u₁ u₂ y x * φ x) +
        ∫ x : ℝ, (apm_m99j02_g u₁ u₂ y x * q x) * φ x = 0 := by
      rw [← MeasureTheory.integral_add hreg hqterm]
      apply MeasureTheory.integral_eq_zero_of_ae
      filter_upwards [hne] with x hx
      have hc := hregular_cancel q hq₁ hq₂ y x hx
      calc
        apm_m99j02_regularSecondDerivative u₁ u₂ y x * φ x +
            apm_m99j02_g u₁ u₂ y x * q x * φ x =
          (apm_m99j02_regularSecondDerivative u₁ u₂ y x +
            q x * apm_m99j02_g u₁ u₂ y x) * φ x := by ring
        _ = 0 := by rw [hc, zero_mul]
    rw [← apm_m99j02_wronskian_eq_zero u₁ u₂ q hu₁ hu₂ hq₁ hq₂ y]
    linarith
