import Mathlib

/-!
# APM a98A05

## Statement repairs

None.

## Encoding questions

None.  The improper integral over `(0, ∞)` is represented as the Lebesgue
integral over `Set.Ioi 0`.
-/

open MeasureTheory Set Filter

noncomputable section

/-- The real partial-fraction decomposition, with positivity facts packaged so
later improper-integration steps have no pole side conditions. -/
lemma apm_a98a05_partial_fractions {x : ℝ} (hx : 0 ≤ x) :
    0 < x + 1 ∧ 0 < x ^ 2 - x + 1 ∧
      1 / (1 + x ^ 3) =
        (1 / 3 : ℝ) / (x + 1) + (2 - x) / (3 * (x ^ 2 - x + 1)) := by
  have hx1 : 0 < x + 1 := by linarith
  have hq : 0 < x ^ 2 - x + 1 := by
    nlinarith [sq_nonneg (x - (1 / 2 : ℝ))]
  refine ⟨hx1, hq, ?_⟩
  have hcubic : 1 + x ^ 3 = (x + 1) * (x ^ 2 - x + 1) := by ring
  rw [hcubic]
  let A : ℝ := x + 1
  let Q : ℝ := x ^ 2 - x + 1
  have hA : A ≠ 0 := by simpa [A] using ne_of_gt hx1
  have hQ : Q ≠ 0 := by simpa [Q] using ne_of_gt hq
  change 1 / (A * Q) = (1 / 3 : ℝ) / A + (2 - x) / (3 * Q)
  field_simp [hA, hQ]
  simp [A, Q]
  ring

/-- The real antiderivative used for the improper-integral evaluation. -/
def apm_a98a05_primitive (x : ℝ) : ℝ :=
  (1 / 3 : ℝ) * Real.log (x + 1) -
    (1 / 6 : ℝ) * Real.log (x ^ 2 - x + 1) +
      Real.sqrt 3 / 3 * Real.arctan ((2 * x - 1) / Real.sqrt 3)

/-- The displayed primitive differentiates to the integrand on the
nonnegative half-line.  The arctangent normalization follows the calculation
in the solved sibling `a94A06`. -/
lemma apm_a98a05_hasDerivAt_primitive {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt apm_a98a05_primitive (1 / (1 + x ^ 3)) x := by
  have hsqrt : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hq : 0 < x ^ 2 - x + 1 := (apm_a98a05_partial_fractions hx).2.1
  have h1 : HasDerivAt (fun y : ℝ => (1 / 3 : ℝ) * Real.log (y + 1))
      ((1 / 3 : ℝ) / (x + 1)) x := by
    have hd : HasDerivAt (fun y : ℝ => y + 1) 1 x :=
      (hasDerivAt_id x).add_const 1
    convert (hd.log (by linarith)).const_mul (1 / 3 : ℝ) using 1 <;> ring
  have h2 : HasDerivAt
      (fun y : ℝ => -(1 / 6 : ℝ) * Real.log (y ^ 2 - y + 1))
      ((2 * x - 1) / (x ^ 2 - x + 1) * (-(1 / 6 : ℝ))) x := by
    have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      convert hasDerivAt_pow 2 x using 1 <;> ring
    have hd : HasDerivAt (fun y : ℝ => y ^ 2 - y + 1) (2 * x - 1) x :=
      (hp.sub (hasDerivAt_id x)).add_const 1
    convert (hd.log hq.ne').const_mul (-(1 / 6 : ℝ)) using 1 <;> ring
  have h3 : HasDerivAt
      (fun y : ℝ => Real.sqrt 3 / 3 *
        Real.arctan ((2 * y - 1) / Real.sqrt 3))
      (1 / (2 * (x ^ 2 - x + 1))) x := by
    have hd : HasDerivAt (fun y : ℝ => (2 * y - 1) / Real.sqrt 3)
        (2 / Real.sqrt 3) x := by
      convert ((hasDerivAt_id x).const_mul 2).sub_const 1 |>.div_const
        (Real.sqrt 3) using 1 <;> ring
    convert hd.arctan.const_mul (Real.sqrt 3 / 3) using 1
    rw [div_pow, hsqrt]
    rw [show x ^ 2 - x + 1 = 1 - x + x ^ 2 by ring]
    have hq' : (1 - x + x ^ 2 : ℝ) ≠ 0 := by nlinarith
    field_simp [hq']
    ring
  unfold apm_a98a05_primitive
  convert h1.add h2 |>.add h3 using 1
  · funext y
    simp only [Pi.add_apply]
    congr 2 <;> ring
  · rw [(apm_a98a05_partial_fractions hx).2.2]
    field_simp [hq.ne']
    ring

/-- The logarithmic terms in the primitive cancel at infinity.  This is the
same ratio-to-one argument used in the solved exact-integral sibling
`a94A06`, specialized to the quadratic denominator here. -/
lemma apm_a98a05_tendsto_primitive :
    Tendsto apm_a98a05_primitive atTop
      (nhds (Real.sqrt 3 * Real.pi / 6)) := by
  have hi : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hi2 : Tendsto (fun x : ℝ => (x⁻¹) ^ 2) atTop (nhds 0) := by
    simpa using hi.pow 2
  have hn : Tendsto (fun x : ℝ => (1 + x⁻¹) ^ 2) atTop (nhds 1) := by
    convert (tendsto_const_nhds.add hi).pow 2 using 1 <;> norm_num
  have hd : Tendsto (fun x : ℝ => 1 - x⁻¹ + (x⁻¹) ^ 2) atTop (nhds 1) := by
    convert (tendsto_const_nhds.sub hi).add hi2 using 1 <;> norm_num
  have hratio : Tendsto
      (fun x : ℝ => (x + 1) ^ 2 / (x ^ 2 - x + 1)) atTop (nhds 1) := by
    have hdiv := hn.div hd (by norm_num : (1 : ℝ) ≠ 0)
    have heq :
        (fun x : ℝ => (x + 1) ^ 2 / (x ^ 2 - x + 1)) =ᶠ[atTop]
          (fun x : ℝ => (1 + x⁻¹) ^ 2 / (1 - x⁻¹ + (x⁻¹) ^ 2)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      field_simp [hx0]
    convert hdiv.congr' heq.symm using 1 <;> norm_num
  have hlogratio : Tendsto
      (fun x : ℝ => Real.log ((x + 1) ^ 2 / (x ^ 2 - x + 1)))
      atTop (nhds 0) := by
    simpa using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  have hlogs : Tendsto (fun x : ℝ =>
      (1 / 3 : ℝ) * Real.log (x + 1) -
        (1 / 6 : ℝ) * Real.log (x ^ 2 - x + 1)) atTop (nhds 0) := by
    have hscaled := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 / 6 : ℝ))
      atTop (nhds (1 / 6))).mul hlogratio
    have heqlogs : (fun x : ℝ =>
        (1 / 3 : ℝ) * Real.log (x + 1) -
          (1 / 6 : ℝ) * Real.log (x ^ 2 - x + 1)) =ᶠ[atTop]
        (fun x : ℝ => (1 / 6 : ℝ) *
          Real.log ((x + 1) ^ 2 / (x ^ 2 - x + 1))) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hA : 0 < x + 1 := by linarith
      have hQ : 0 < x ^ 2 - x + 1 := by
        nlinarith [sq_nonneg (x - (1 / 2 : ℝ))]
      rw [Real.log_div (pow_ne_zero 2 hA.ne') hQ.ne', Real.log_pow]
      ring
    simpa only [mul_zero] using hscaled.congr' heqlogs.symm
  have hinner : Tendsto (fun x : ℝ => (2 * x - 1) / Real.sqrt 3)
      atTop atTop := by
    have hmul : Tendsto (fun x : ℝ => 2 * x) atTop atTop :=
      tendsto_id.const_mul_atTop (by norm_num)
    have hsub : Tendsto (fun x : ℝ => 2 * x - 1) atTop atTop := by
      simpa only [sub_eq_add_neg] using hmul.atTop_add tendsto_const_nhds
    exact hsub.atTop_div_const (Real.sqrt_pos.2 (by norm_num))
  have harctan : Tendsto
      (fun x : ℝ => Real.arctan ((2 * x - 1) / Real.sqrt 3)) atTop
      (nhds (Real.pi / 2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin (Real.tendsto_arctan_atTop.comp hinner)
  unfold apm_a98a05_primitive
  convert hlogs.add (tendsto_const_nhds.mul harctan) using 1 <;> ring

theorem apm_a98a05 :
    ∫ x in Ioi (0 : ℝ), 1 / (1 + x ^ 3) ∂volume =
      2 * Real.pi / (3 * Real.sqrt 3) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (0 : ℝ)) (g := apm_a98a05_primitive)
    (g' := fun x : ℝ => 1 / (1 + x ^ 3))
    (l := Real.sqrt 3 * Real.pi / 6)
    (fun x hx => apm_a98a05_hasDerivAt_primitive hx)
    (fun x hx => one_div_nonneg.mpr (by
      have hx3 : 0 < x ^ 3 := pow_pos hx 3
      linarith))
    apm_a98a05_tendsto_primitive
  have hsqrt : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hzero : apm_a98a05_primitive 0 = -(Real.sqrt 3 * Real.pi / 18) := by
    unfold apm_a98a05_primitive
    rw [show ((2 * (0 : ℝ) - 1) / Real.sqrt 3) = -(Real.sqrt 3)⁻¹ by
      field_simp [Real.sqrt_ne_zero'.2 (by norm_num : (0 : ℝ) < 3)] <;> ring]
    rw [Real.arctan_neg, Real.arctan_inv_sqrt_three]
    norm_num
    ring
  rw [hzero] at h
  rw [h]
  field_simp [Real.sqrt_ne_zero'.2 (by norm_num : (0 : ℝ) < 3)]
  nlinarith
