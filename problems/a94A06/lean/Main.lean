import Mathlib

open Real Filter Set MeasureTheory Topology

noncomputable section

/-!
# APM a94A06: ∫₀^∞ x⁷/(1+x¹²) dx = π√3/18

Informal proof uses the residue theorem on a pie-slice contour of angle π/6.
For the Lean proof, we use a real-variable approach: compute the antiderivative
explicitly via partial fractions and evaluate at the limits.
-/

namespace ApmCanaries.A94A06

lemma pos_quad (u : ℝ) : 0 < u^2 - u + 1 := by nlinarith [sq_nonneg (u - 1/2)]

lemma sq_sqrt3 : (Real.sqrt 3 : ℝ)^2 = 3 := sq_sqrt (by norm_num)

lemma alg_h3 (u : ℝ) :
    Real.sqrt 3 / 3 * (1 / (1 + ((2*u - 1) / Real.sqrt 3)^2) * (2 / Real.sqrt 3)) =
    1 / (2 * (u^2 - u + 1)) := by
  rw [div_pow, sq_sqrt3]
  have hq : (1 - u + u^2 : ℝ) ≠ 0 := by nlinarith [sq_nonneg (u - 1/2)]
  rw [show u^2 - u + 1 = 1 - u + u^2 from by ring]
  field_simp [hq]
  ring

lemma alg_sum (u : ℝ) (hu : 0 ≤ u) :
    u / ((u + 1) * (u^2 - u + 1)) =
    1 / (u + 1) * (-(1:ℝ)/3) + (2*u - 1) / (u^2 - u + 1) * ((1:ℝ)/6)
      + 1 / (2 * (u^2 - u + 1)) := by
  have hq : (1 - u + u^2 : ℝ) ≠ 0 := by nlinarith [sq_nonneg (u - 1/2)]
  have hu1 : (u + 1 : ℝ) ≠ 0 := by linarith
  rw [show u^2 - u + 1 = 1 - u + u^2 from by ring]
  field_simp [hq, hu1]
  ring

def H (u : ℝ) : ℝ :=
  -(1:ℝ)/3 * Real.log (u + 1) + (1:ℝ)/6 * Real.log (u^2 - u + 1)
    + Real.sqrt 3 / 3 * Real.arctan ((2*u - 1) / Real.sqrt 3)

lemma hasDerivAt_H (u : ℝ) (hu : 0 ≤ u) : HasDerivAt H (u / (1 + u^3)) u := by
  unfold H
  have h1 : HasDerivAt (fun x : ℝ => -(1:ℝ)/3 * Real.log (x + 1))
      (1 / (u + 1) * (-(1:ℝ)/3)) u := by
    have hd : HasDerivAt (fun x : ℝ => x + 1) (1 : ℝ) u := (hasDerivAt_id u).add_const 1
    have hlog : HasDerivAt (fun x : ℝ => Real.log (x + 1)) (1 / (u + 1)) u := by
      convert hd.log (by linarith) using 1
    convert hlog.const_mul (-(1:ℝ)/3) using 1; first | ring | skip
  have h2 : HasDerivAt (fun x : ℝ => (1:ℝ)/6 * Real.log (x^2 - x + 1))
      ((2*u-1) / (u^2 - u + 1) * ((1:ℝ)/6)) u := by
    have hpow : HasDerivAt (fun x : ℝ => x^2) (2 * u : ℝ) u := by
      convert hasDerivAt_pow 2 u using 1; first | ring | skip
    have hd : HasDerivAt (fun x : ℝ => x^2 - x + 1) (2*u - 1 : ℝ) u := by
      convert hpow.sub (hasDerivAt_id (x := u)) |>.add_const 1 using 1
    have hlog : HasDerivAt (fun x : ℝ => Real.log (x^2 - x + 1)) ((2*u - 1) / (u^2 - u + 1)) u := by
      convert hd.log (pos_quad u).ne' using 1
    convert hlog.const_mul ((1:ℝ)/6) using 1; first | ring | skip
  have h3 : HasDerivAt (fun x : ℝ => Real.sqrt 3 / 3 * Real.arctan ((2*x - 1) / Real.sqrt 3))
      (1 / (2 * (u^2 - u + 1))) u := by
    have hd : HasDerivAt (fun x : ℝ => (2*x - 1) / Real.sqrt 3) (2 / Real.sqrt 3 : ℝ) u := by
      convert (hasDerivAt_id (x := u)).const_mul 2 |>.sub_const 1 |>.div_const (Real.sqrt 3) using 1; first | ring | skip
    have ha := hd.arctan
    convert ha.const_mul (Real.sqrt 3 / 3) using 1
    exact (alg_h3 u).symm
  convert (h1.add h2 |>.add h3) using 1
  rw [show 1 + u^3 = (u + 1) * (u^2 - u + 1) from by ring]
  exact alg_sum u hu

/-- The antiderivative G of x⁷/(1+x¹²), written directly without composition. -/
def G (x : ℝ) : ℝ :=
  -(1:ℝ)/12 * Real.log (x^4 + 1) + (1:ℝ)/24 * Real.log (x^8 - x^4 + 1)
    + Real.sqrt 3 / 12 * Real.arctan ((2*x^4 - 1) / Real.sqrt 3)

/-- Key algebraic identity: the derivative of G equals x⁷/(1+x¹²). -/
lemma alg_G_deriv (x : ℝ) :
    4 * x^3 / (x^4 + 1) * (-(1:ℝ)/12) +
    (8*x^7 - 4*x^3) / (x^8 - x^4 + 1) * ((1:ℝ)/24) +
    (1 / (1 + ((2*x^4 - 1) / Real.sqrt 3)^2) * ((2 * (4 * x^3)) / Real.sqrt 3))
      * (Real.sqrt 3 / 12) = x^7 / (1 + x^12) := by
  rw [div_pow, sq_sqrt3]
  rw [show x^8 - x^4 + 1 = 1 - x^4 + x^8 from by ring]
  have hq : (1 - x^4 + x^8 : ℝ) ≠ 0 := by
    have h : (0:ℝ) < 1 - x^4 + x^8 := by nlinarith [sq_nonneg (x^4 - 1/2)]
    exact h.ne'
  have hq4 : (x^4 + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hq, hq4]
  ring

lemma hasDerivAt_G (x : ℝ) : HasDerivAt G (x^7 / (1 + x^12)) x := by
  unfold G
  have h1 : HasDerivAt (fun y : ℝ => -(1:ℝ)/12 * Real.log (y^4 + 1))
      (4 * x^3 / (x^4 + 1) * (-(1:ℝ)/12)) x := by
    have hp4 : HasDerivAt (fun y : ℝ => y^4) (4 * x^3) x := by
      convert hasDerivAt_pow 4 x using 1; first | (push_cast; ring) | skip
    have hadd : HasDerivAt (fun y : ℝ => y^4 + 1) (4 * x^3) x := hp4.add_const 1
    have hlog : HasDerivAt (fun y : ℝ => Real.log (y^4 + 1)) (4 * x^3 / (x^4 + 1)) x := by
      convert hadd.log (by positivity) using 1
    convert hlog.const_mul (-(1:ℝ)/12) using 1; first | ring | skip
  have h2 : HasDerivAt (fun y : ℝ => (1:ℝ)/24 * Real.log (y^8 - y^4 + 1))
      ((8*x^7 - 4*x^3) / (x^8 - x^4 + 1) * ((1:ℝ)/24)) x := by
    have hp8 : HasDerivAt (fun y : ℝ => y^8) (8 * x^7) x := by
      convert hasDerivAt_pow 8 x using 1; first | (push_cast; ring) | skip
    have hp4 : HasDerivAt (fun y : ℝ => y^4) (4 * x^3) x := by
      convert hasDerivAt_pow 4 x using 1; first | (push_cast; ring) | skip
    have hsub : HasDerivAt (fun y : ℝ => y^8 - y^4) (8*x^7 - 4*x^3) x := by
      convert hp8.sub hp4 using 1; first | ring | skip
    have hadd : HasDerivAt (fun y : ℝ => y^8 - y^4 + 1) (8*x^7 - 4*x^3) x := hsub.add_const 1
    have hpos : (0 : ℝ) < x^8 - x^4 + 1 := by
      have : x^8 - x^4 + 1 = (x^4 - 1/2)^2 + 3/4 := by ring
      rw [this]; nlinarith [sq_nonneg (x^4 - 1/2)]
    have hlog : HasDerivAt (fun y : ℝ => Real.log (y^8 - y^4 + 1))
        ((8*x^7 - 4*x^3) / (x^8 - x^4 + 1)) x := by
      convert hadd.log hpos.ne' using 1
    convert hlog.const_mul ((1:ℝ)/24) using 1; first | ring | skip
  have h3 : HasDerivAt (fun y : ℝ => Real.sqrt 3 / 12 * Real.arctan ((2*y^4 - 1) / Real.sqrt 3))
      ((1 / (1 + ((2*x^4 - 1) / Real.sqrt 3)^2) * ((2 * (4 * x^3)) / Real.sqrt 3))
        * (Real.sqrt 3 / 12)) x := by
    have hp4 : HasDerivAt (fun y : ℝ => y^4) (4 * x^3) x := by
      convert hasDerivAt_pow 4 x using 1; first | (push_cast; ring) | skip
    have h2p4 : HasDerivAt (fun y : ℝ => 2 * y^4) (2 * (4 * x^3)) x := by
      convert hp4.const_mul 2 using 1; first | ring | skip
    have hinner : HasDerivAt (fun y : ℝ => (2*y^4 - 1) / Real.sqrt 3)
        ((2 * (4 * x^3)) / Real.sqrt 3) x := by
      convert h2p4.sub_const 1 |>.div_const (Real.sqrt 3) using 1; first | ring | skip
    have harctan : HasDerivAt (fun y : ℝ => Real.arctan ((2*y^4 - 1) / Real.sqrt 3))
        (1 / (1 + ((2*x^4 - 1) / Real.sqrt 3)^2) * ((2 * (4 * x^3)) / Real.sqrt 3)) x := by
      convert hinner.arctan using 1
    convert harctan.const_mul (Real.sqrt 3 / 12) using 1; first | ring | skip
  convert (h1.add h2 |>.add h3) using 1
  exact (alg_G_deriv x).symm

/-- Value of G at 0: G(0) = -π√3/72. -/
lemma G_zero : G 0 = -(Real.sqrt 3 * π) / 72 := by
  unfold G
  simp [pow_zero, zero_add, zero_sub]
  have hneg : Real.arctan (-(1:ℝ) / Real.sqrt 3) = -Real.arctan (1 / Real.sqrt 3) := by
    have : -(1:ℝ) / Real.sqrt 3 = -(1 / Real.sqrt 3) := by rw [neg_div]
    rw [this, Real.arctan_neg]
  rw [hneg]
  rw [show (1:ℝ) / Real.sqrt 3 = (Real.sqrt 3)⁻¹ from one_div _]
  rw [Real.arctan_inv_sqrt_three]
  -- arctan((√3)⁻¹) uses (√3)⁻¹ but we have 1/√3
  field_simp; ring

/-- Limit of G as x → ∞: lim = π√3/24. -/
lemma tendsto_G_atTop : Tendsto G atTop (nhds (Real.sqrt 3 * π / 24)) := by
  have hi : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hi4 : Tendsto (fun x : ℝ => (x⁻¹)^4) atTop (nhds 0) := by
    simpa using hi.pow 4
  have hi8 : Tendsto (fun x : ℝ => (x⁻¹)^8) atTop (nhds 0) := by
    simpa using hi.pow 8
  have hn : Tendsto (fun x : ℝ => 1 - (x⁻¹)^4 + (x⁻¹)^8) atTop (nhds 1) := by
    convert (tendsto_const_nhds.sub hi4).add hi8 using 1 <;> norm_num
  have hd : Tendsto (fun x : ℝ => 1 + 2 * (x⁻¹)^4 + (x⁻¹)^8) atTop (nhds 1) := by
    convert (tendsto_const_nhds.add (tendsto_const_nhds.mul hi4)).add hi8 using 1 <;> norm_num
  have hratio :
      Tendsto (fun x : ℝ => (x^8 - x^4 + 1) / (x^4 + 1)^2) atTop (nhds 1) := by
    have hdiv := hn.div hd (by norm_num : (1 : ℝ) ≠ 0)
    have heq :
        (fun x : ℝ => (x^8 - x^4 + 1) / (x^4 + 1)^2) =ᶠ[atTop]
          (fun x : ℝ => (1 - (x⁻¹)^4 + (x⁻¹)^8) /
            (1 + 2 * (x⁻¹)^4 + (x⁻¹)^8)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      field_simp [hx0]
      ring
    simpa using hdiv.congr' heq.symm
  have hlogratio :
      Tendsto (fun x : ℝ => Real.log ((x^8 - x^4 + 1) / (x^4 + 1)^2))
        atTop (nhds 0) := by
    simpa using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  have hlogs :
      Tendsto (fun x : ℝ =>
        -(1:ℝ)/12 * Real.log (x^4 + 1) +
          (1:ℝ)/24 * Real.log (x^8 - x^4 + 1)) atTop (nhds 0) := by
    have hscaled :
        Tendsto (fun x : ℝ =>
          (1 / 24 : ℝ) * Real.log ((x^8 - x^4 + 1) / (x^4 + 1)^2))
          atTop (nhds 0) := by
      simpa using
        ((tendsto_const_nhds :
          Tendsto (fun _ : ℝ => (1/24 : ℝ)) atTop (nhds (1/24))).mul hlogratio)
    apply hscaled.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hA : 0 < x^4 + 1 := by positivity
    have hB : 0 < x^8 - x^4 + 1 := by
      nlinarith [sq_nonneg (x^4 - 1/2)]
    rw [Real.log_div hB.ne' (pow_ne_zero 2 hA.ne'), Real.log_pow]
    ring
  have hp4 : Tendsto (fun x : ℝ => x^4) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hinner : Tendsto (fun x : ℝ => (2*x^4 - 1) / Real.sqrt 3) atTop atTop := by
    have hmul : Tendsto (fun x : ℝ => 2 * x^4) atTop atTop :=
      hp4.const_mul_atTop (by norm_num)
    have hsub : Tendsto (fun x : ℝ => 2 * x^4 - 1) atTop atTop := by
      simpa only [sub_eq_add_neg] using hmul.atTop_add tendsto_const_nhds
    exact hsub.atTop_div_const (Real.sqrt_pos.2 (by norm_num))
  have harctan :
      Tendsto (fun x : ℝ => Real.arctan ((2*x^4 - 1) / Real.sqrt 3))
        atTop (nhds (π / 2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin (Real.tendsto_arctan_atTop.comp hinner)
  unfold G
  convert hlogs.add (tendsto_const_nhds.mul harctan) using 1 <;> ring

/-- Main result: ∫₀^∞ x⁷/(1+x¹²) dx = π√3/18. -/
theorem integral_x7_over_1_plus_x12 :
    ∫ x in Ioi (0:ℝ), x^7 / (1 + x^12) = Real.sqrt 3 * π / 18 := by
  have h :=
    integral_Ioi_of_hasDerivAt_of_nonneg'
      (a := (0 : ℝ)) (g := G) (g' := fun x : ℝ => x^7 / (1 + x^12))
      (l := Real.sqrt 3 * π / 24)
      (fun x _ => hasDerivAt_G x)
      (fun x hx => div_nonneg (pow_nonneg hx.le _) (by positivity))
      tendsto_G_atTop
  rw [G_zero] at h
  convert h using 1 <;> ring

end ApmCanaries.A94A06
