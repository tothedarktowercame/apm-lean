import Mathlib

/-!
# APM m93J03: A nonlinear integral equation near its trivial branch

## Statement repairs

The printed global uniqueness claim is stronger than, and is not established
by, the intended implicit-function argument. The exact finite-dimensional
reduction has additional nonzero branches already at `ε = 0`; the invertible
Jacobian proves uniqueness only in a neighborhood of the trivial solution.
We therefore state the minimally repaired local result: fixed radii `δ,η > 0`
give a unique solution with `|ε| < δ` and uniform size below `η`.

## Encoding questions

None. The equation uses the Lebesgue integral on `[-π,π]`; continuity and
uniqueness are both restricted to that exact interval.
-/

open MeasureTheory Set

noncomputable section

def apm_m93J03_isSolution (ε : ℝ) (x : ℝ → ℝ) : Prop :=
  ContinuousOn x (Icc (-Real.pi) Real.pi) ∧
  ∀ t ∈ Icc (-Real.pi) Real.pi,
    x t = ε + ∫ s in Icc (-Real.pi) Real.pi, Real.sin (t + s + x s)

def apm_m93J03_isSmall (x : ℝ → ℝ) (η : ℝ) : Prop :=
  ∀ t ∈ Icc (-Real.pi) Real.pi, |x t| < η

lemma apm_m93J03_isSmall_mono {x : ℝ → ℝ} {η η' : ℝ}
    (hx : apm_m93J03_isSmall x η) (hη : η ≤ η') :
    apm_m93J03_isSmall x η' := by
  intro t ht
  exact (hx t ht).trans_le hη

lemma apm_m93J03_zero_isSmall {η : ℝ} (hη : 0 < η) :
    apm_m93J03_isSmall (fun _ ↦ 0) η := by
  intro t ht
  simpa using hη

/-- Separating `sin (t + s + x s)` shows that every solution belongs to the
three-dimensional affine span of `1`, `sin`, and `cos`.  This is the exact
function-level reduction needed before applying the finite-dimensional
implicit-function theorem. -/
lemma apm_m93J03_solution_eq_affine_trig {ε : ℝ} {x : ℝ → ℝ}
    (hx : apm_m93J03_isSolution ε x) :
    ∃ a b : ℝ, ∀ t ∈ Icc (-Real.pi) Real.pi,
      x t = ε + a * Real.sin t + b * Real.cos t := by
  let u : ℝ → ℝ := fun s ↦ s + x s
  have hu : ContinuousOn u (Icc (-Real.pi) Real.pi) :=
    continuousOn_id.add hx.1
  have hcos : IntegrableOn (fun s ↦ Real.cos (u s))
      (Icc (-Real.pi) Real.pi) :=
    (Real.continuous_cos.comp_continuousOn hu).integrableOn_Icc
  have hsin : IntegrableOn (fun s ↦ Real.sin (u s))
      (Icc (-Real.pi) Real.pi) :=
    (Real.continuous_sin.comp_continuousOn hu).integrableOn_Icc
  refine ⟨∫ s in Icc (-Real.pi) Real.pi, Real.cos (u s),
    ∫ s in Icc (-Real.pi) Real.pi, Real.sin (u s), ?_⟩
  intro t ht
  rw [hx.2 t ht]
  have hpoint : ∀ s : ℝ,
      Real.sin (t + s + x s) =
        Real.sin t * Real.cos (u s) + Real.cos t * Real.sin (u s) := by
    intro s
    rw [show t + s + x s = t + u s by simp [u, add_assoc], Real.sin_add]
  rw [setIntegral_congr_fun measurableSet_Icc (fun s _ ↦ hpoint s)]
  rw [integral_add (hcos.const_mul _) (hsin.const_mul _),
    integral_const_mul, integral_const_mul]
  ring

def apm_m93J03_affineTrig (ε a b t : ℝ) : ℝ :=
  ε + a * Real.sin t + b * Real.cos t

/-- The exact two-dimensional residual to which the implicit-function theorem
is applied after the affine-trigonometric reduction. -/
def apm_m93J03_residual (ε : ℝ) (q : ℝ × ℝ) : ℝ × ℝ :=
  (q.1 - ∫ s in Icc (-Real.pi) Real.pi,
      Real.cos (s + apm_m93J03_affineTrig ε q.1 q.2 s),
    q.2 - ∫ s in Icc (-Real.pi) Real.pi,
      Real.sin (s + apm_m93J03_affineTrig ε q.1 q.2 s))

/-- A zero of the reduced residual reconstructs a genuine solution of the
original function-valued equation. -/
lemma apm_m93J03_isSolution_affineTrig_of_residual_eq_zero
    {ε a b : ℝ} (hres : apm_m93J03_residual ε (a, b) = 0) :
    apm_m93J03_isSolution ε (apm_m93J03_affineTrig ε a b) := by
  have ha : a = ∫ s in Icc (-Real.pi) Real.pi,
      Real.cos (s + apm_m93J03_affineTrig ε a b s) := by
    have h := congrArg Prod.fst hres
    simpa [apm_m93J03_residual] using sub_eq_zero.mp h
  have hb : b = ∫ s in Icc (-Real.pi) Real.pi,
      Real.sin (s + apm_m93J03_affineTrig ε a b s) := by
    have h := congrArg Prod.snd hres
    simpa [apm_m93J03_residual] using sub_eq_zero.mp h
  have hcont : Continuous (apm_m93J03_affineTrig ε a b) :=
    (continuous_const.add (continuous_const.mul Real.continuous_sin)).add
      (continuous_const.mul Real.continuous_cos)
  constructor
  · exact hcont.continuousOn
  · intro t ht
    have hu : ContinuousOn
        (fun s ↦ s + apm_m93J03_affineTrig ε a b s)
        (Icc (-Real.pi) Real.pi) := continuousOn_id.add hcont.continuousOn
    have hcos : IntegrableOn
        (fun s ↦ Real.cos (s + apm_m93J03_affineTrig ε a b s))
        (Icc (-Real.pi) Real.pi) :=
      (Real.continuous_cos.comp_continuousOn hu).integrableOn_Icc
    have hsin : IntegrableOn
        (fun s ↦ Real.sin (s + apm_m93J03_affineTrig ε a b s))
        (Icc (-Real.pi) Real.pi) :=
      (Real.continuous_sin.comp_continuousOn hu).integrableOn_Icc
    have hpoint : ∀ s : ℝ,
        Real.sin (t + s + apm_m93J03_affineTrig ε a b s) =
          Real.sin t * Real.cos (s + apm_m93J03_affineTrig ε a b s) +
          Real.cos t * Real.sin (s + apm_m93J03_affineTrig ε a b s) := by
      intro s
      rw [show t + s + apm_m93J03_affineTrig ε a b s =
        t + (s + apm_m93J03_affineTrig ε a b s) by ring, Real.sin_add]
    have hint : (∫ s in Icc (-Real.pi) Real.pi,
        Real.sin (t + s + apm_m93J03_affineTrig ε a b s)) =
        Real.sin t * a + Real.cos t * b := by
      rw [setIntegral_congr_fun measurableSet_Icc (fun s _ ↦ hpoint s),
        integral_add (hcos.const_mul _) (hsin.const_mul _),
        integral_const_mul, integral_const_mul, ← ha, ← hb]
    rw [hint]
    simp only [apm_m93J03_affineTrig]
    ring

/-- The trivial branch is completely explicit: over one full period the
shifted sine kernel has integral zero. -/
lemma apm_m93J03_const_isSolution (ε : ℝ) :
    apm_m93J03_isSolution ε (fun _ ↦ ε) := by
  constructor
  · exact continuousOn_const
  · intro t ht
    have hpi : -Real.pi ≤ Real.pi := (neg_le_self Real.pi_pos.le)
    have hperiod :
        (∫ s in Icc (-Real.pi) Real.pi, Real.sin (s + (t + ε))) = 0 := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi,
        intervalIntegral.integral_comp_add_right, integral_sin]
      rw [show Real.pi + (t + ε) = (-Real.pi + (t + ε)) + 2 * Real.pi by ring,
        Real.cos_add_two_pi]
      ring
    simpa [add_assoc, add_left_comm, add_comm] using hperiod

/-- Existence does not require the implicit-function theorem: `(0,0)` is a
zero of the reduced residual for every parameter. -/
lemma apm_m93J03_residual_zero (ε : ℝ) :
    apm_m93J03_residual ε (0, 0) = 0 := by
  have hpi : -Real.pi ≤ Real.pi := (neg_le_self Real.pi_pos.le)
  have hsin :
      (∫ s in Icc (-Real.pi) Real.pi, Real.sin (s + ε)) = 0 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi,
      intervalIntegral.integral_comp_add_right, integral_sin]
    rw [show Real.pi + ε = (-Real.pi + ε) + 2 * Real.pi by ring,
      Real.cos_add_two_pi]
    ring
  have hcos :
      (∫ s in Icc (-Real.pi) Real.pi, Real.cos (s + ε)) = 0 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi,
      intervalIntegral.integral_comp_add_right, integral_cos]
    rw [show Real.pi + ε = (-Real.pi + ε) + 2 * Real.pi by ring,
      Real.sin_add_two_pi]
    ring
  simp [apm_m93J03_residual, apm_m93J03_affineTrig, hsin, hcos]

/-- Conversely, an affine-trigonometric solution has zero reduced residual.
The two coefficient equations are recovered by evaluating the original
equation at `0` and `π / 2`. -/
lemma apm_m93J03_residual_eq_zero_of_isSolution_affineTrig
    {ε a b : ℝ}
    (hx : apm_m93J03_isSolution ε (apm_m93J03_affineTrig ε a b)) :
    apm_m93J03_residual ε (a, b) = 0 := by
  have hzero : (0 : ℝ) ∈ Icc (-Real.pi) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  have hhalf : Real.pi / 2 ∈ Icc (-Real.pi) Real.pi := by
    constructor <;> nlinarith [Real.pi_pos]
  have hb := hx.2 0 hzero
  have ha := hx.2 (Real.pi / 2) hhalf
  simp only [apm_m93J03_affineTrig, Real.sin_zero, mul_zero, Real.cos_zero,
    mul_one, add_zero, zero_add] at hb
  simp only [apm_m93J03_affineTrig, Real.sin_pi_div_two, mul_one,
    Real.cos_pi_div_two, mul_zero, add_zero] at ha
  have hb' : b = ∫ s in Icc (-Real.pi) Real.pi,
      Real.sin (s + apm_m93J03_affineTrig ε a b s) := by
    have hb0 := add_left_cancel hb
    simpa [apm_m93J03_affineTrig] using hb0
  have ha' : a = ∫ s in Icc (-Real.pi) Real.pi,
      Real.cos (s + apm_m93J03_affineTrig ε a b s) := by
    have ha0 := add_left_cancel ha
    simpa [apm_m93J03_affineTrig, add_assoc, Real.sin_add] using ha0
  apply Prod.ext
  · simpa [apm_m93J03_residual] using sub_eq_zero.mpr ha'
  · simpa [apm_m93J03_residual] using sub_eq_zero.mpr hb'

/-- The explicit branch supplies the existence and radius clauses of the main
theorem; only local uniqueness remains analytic. -/
lemma apm_m93J03_exists_small_solution {ε η : ℝ} (hε : |ε| < η) :
    ∃ x : ℝ → ℝ,
      apm_m93J03_isSolution ε x ∧ apm_m93J03_isSmall x η := by
  refine ⟨fun _ ↦ ε, apm_m93J03_const_isSolution ε, ?_⟩
  intro t ht
  exact hε

/-- Uniform smallness controls the two coefficients in the exact
finite-dimensional reduction.  Evaluating at `0` and `π / 2` avoids any
integral estimates. -/
lemma apm_m93J03_small_solution_coefficients {ε δ η : ℝ} {y : ℝ → ℝ}
    (hy : apm_m93J03_isSolution ε y) (hsmall : apm_m93J03_isSmall y η)
    (hε : |ε| < δ) :
    ∃ a b : ℝ,
      (∀ t ∈ Icc (-Real.pi) Real.pi,
        y t = ε + a * Real.sin t + b * Real.cos t) ∧
      |a| < η + δ ∧ |b| < η + δ := by
  rcases apm_m93J03_solution_eq_affine_trig hy with ⟨a, b, hab⟩
  have hzero : (0 : ℝ) ∈ Icc (-Real.pi) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  have hhalf : Real.pi / 2 ∈ Icc (-Real.pi) Real.pi := by
    constructor <;> nlinarith [Real.pi_pos]
  have hb : b = y 0 - ε := by
    have := hab 0 hzero
    simp only [Real.sin_zero, mul_zero, Real.cos_zero, mul_one, add_zero] at this
    linarith
  have ha : a = y (Real.pi / 2) - ε := by
    have := hab (Real.pi / 2) hhalf
    simp only [Real.sin_pi_div_two, mul_one, Real.cos_pi_div_two, mul_zero,
      add_zero] at this
    linarith
  refine ⟨a, b, hab, ?_, ?_⟩
  · rw [ha]
    exact (abs_sub _ _).trans_lt
      (add_lt_add (hsmall (Real.pi / 2) hhalf) hε)
  · rw [hb]
    exact (abs_sub _ _).trans_lt (add_lt_add (hsmall 0 hzero) hε)

/-- Replacing a solution by an equal affine representative on the integration
interval preserves the equation. -/
lemma apm_m93J03_isSolution_affineTrig_of_eqOn {ε a b : ℝ} {y : ℝ → ℝ}
    (hy : apm_m93J03_isSolution ε y)
    (heq : EqOn y (apm_m93J03_affineTrig ε a b)
      (Icc (-Real.pi) Real.pi)) :
    apm_m93J03_isSolution ε (apm_m93J03_affineTrig ε a b) := by
  constructor
  · exact ((continuous_const.add (continuous_const.mul Real.continuous_sin)).add
      (continuous_const.mul Real.continuous_cos)).continuousOn
  · intro t ht
    rw [← heq ht, hy.2 t ht]
    congr 1
    exact setIntegral_congr_fun measurableSet_Icc (fun s hs ↦ by rw [heq hs])

/-- Every small solution gives a bounded zero of the exact two-dimensional
residual.  This is the complete interface needed by the remaining local
zero-isolation argument. -/
lemma apm_m93J03_small_solution_reduction {ε δ η : ℝ} {y : ℝ → ℝ}
    (hy : apm_m93J03_isSolution ε y) (hsmall : apm_m93J03_isSmall y η)
    (hε : |ε| < δ) :
    ∃ a b : ℝ,
      EqOn y (apm_m93J03_affineTrig ε a b) (Icc (-Real.pi) Real.pi) ∧
      apm_m93J03_residual ε (a, b) = 0 ∧
      |a| < η + δ ∧ |b| < η + δ := by
  rcases apm_m93J03_small_solution_coefficients hy hsmall hε with
    ⟨a, b, hab, ha, hb⟩
  refine ⟨a, b, hab, ?_, ha, hb⟩
  exact apm_m93J03_residual_eq_zero_of_isSolution_affineTrig
    (apm_m93J03_isSolution_affineTrig_of_eqOn hy hab)

/-- A coarse quadratic Taylor remainder for sine, proved from the mean-value
inequality and the global Lipschitz bound for cosine. -/
lemma apm_m93J03_abs_sin_add_sub_linear_le (u z : ℝ) :
    |Real.sin (u + z) - Real.sin u - Real.cos u * z| ≤ |z| ^ 2 := by
  let f : ℝ → ℝ := fun w ↦ Real.sin (u + w) - Real.cos u * w
  have hf : ∀ w ∈ uIcc (0 : ℝ) z,
      HasDerivWithinAt f (Real.cos (u + w) - Real.cos u) (uIcc (0 : ℝ) z) w := by
    intro w hw
    have h : HasDerivAt f (Real.cos (u + w) - Real.cos u) w := by
      convert ((Real.hasDerivAt_sin (u + w)).comp w
        ((hasDerivAt_const w u).add (hasDerivAt_id w))).sub
        ((hasDerivAt_const w (Real.cos u)).mul (hasDerivAt_id w)) using 1
      norm_num [f]
    exact h.hasDerivWithinAt
  have hbound : ∀ w ∈ uIcc (0 : ℝ) z,
      ‖Real.cos (u + w) - Real.cos u‖ ≤ |z| := by
    intro w hw
    rw [Real.norm_eq_abs]
    refine (Real.abs_cos_sub_cos_le (u + w) u).trans ?_
    simpa using (abs_sub_left_of_mem_uIcc hw)
  have h := (convex_uIcc (0 : ℝ) z).norm_image_sub_le_of_norm_hasDerivWithin_le
    hf hbound left_mem_uIcc right_mem_uIcc
  simp only [f, Real.norm_eq_abs, sub_zero, add_zero, mul_zero, pow_two] at h ⊢
  rw [show Real.sin (u + z) - Real.sin u - Real.cos u * z =
    Real.sin (u + z) - Real.cos u * z - Real.sin u by ring]
  exact h

/-- The companion coarse quadratic Taylor remainder for cosine. -/
lemma apm_m93J03_abs_cos_add_sub_linear_le (u z : ℝ) :
    |Real.cos (u + z) - Real.cos u + Real.sin u * z| ≤ |z| ^ 2 := by
  let f : ℝ → ℝ := fun w ↦ Real.cos (u + w) + Real.sin u * w
  have hf : ∀ w ∈ uIcc (0 : ℝ) z,
      HasDerivWithinAt f (-Real.sin (u + w) + Real.sin u) (uIcc (0 : ℝ) z) w := by
    intro w hw
    have h : HasDerivAt f (-Real.sin (u + w) + Real.sin u) w := by
      convert ((Real.hasDerivAt_cos (u + w)).comp w
        ((hasDerivAt_const w u).add (hasDerivAt_id w))).add
        ((hasDerivAt_const w (Real.sin u)).mul (hasDerivAt_id w)) using 1
      norm_num [f]
    exact h.hasDerivWithinAt
  have hbound : ∀ w ∈ uIcc (0 : ℝ) z,
      ‖-Real.sin (u + w) + Real.sin u‖ ≤ |z| := by
    intro w hw
    rw [Real.norm_eq_abs, show -Real.sin (u + w) + Real.sin u =
      -(Real.sin (u + w) - Real.sin u) by ring, abs_neg]
    refine (Real.abs_sin_sub_sin_le (u + w) u).trans ?_
    simpa using (abs_sub_left_of_mem_uIcc hw)
  have h := (convex_uIcc (0 : ℝ) z).norm_image_sub_le_of_norm_hasDerivWithin_le
    hf hbound left_mem_uIcc right_mem_uIcc
  simp only [f, Real.norm_eq_abs, sub_zero, add_zero, mul_zero, pow_two] at h ⊢
  rw [show Real.cos (u + z) - Real.cos u + Real.sin u * z =
    Real.cos (u + z) + Real.sin u * z - Real.cos u by ring]
  exact h

lemma apm_m93J03_integral_sin_sq :
    (∫ s in Icc (-Real.pi) Real.pi, Real.sin s ^ 2) = Real.pi := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_sin_sq]
  simp

lemma apm_m93J03_integral_sin_shift (ε : ℝ) :
    (∫ s in Icc (-Real.pi) Real.pi, Real.sin (s + ε)) = 0 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    intervalIntegral.integral_comp_add_right, integral_sin]
  rw [show Real.pi + ε = (-Real.pi + ε) + 2 * Real.pi by ring,
    Real.cos_add_two_pi]
  ring

lemma apm_m93J03_integral_cos_shift (ε : ℝ) :
    (∫ s in Icc (-Real.pi) Real.pi, Real.cos (s + ε)) = 0 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    intervalIntegral.integral_comp_add_right, integral_cos]
  rw [show Real.pi + ε = (-Real.pi + ε) + 2 * Real.pi by ring,
    Real.sin_add_two_pi]
  ring

lemma apm_m93J03_integral_cos_sq :
    (∫ s in Icc (-Real.pi) Real.pi, Real.cos s ^ 2) = Real.pi := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_cos_sq]
  simp

lemma apm_m93J03_integral_sin_mul_cos :
    (∫ s in Icc (-Real.pi) Real.pi, Real.sin s * Real.cos s) = 0 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_sin_mul_cos₁]
  simp

lemma apm_m93J03_integral_sin_shift_mul_affine (ε a b : ℝ) :
    (∫ s in Icc (-Real.pi) Real.pi,
      Real.sin (s + ε) * (a * Real.sin s + b * Real.cos s)) =
      Real.pi * (a * Real.cos ε + b * Real.sin ε) := by
  have hs2 : IntegrableOn (fun s : ℝ ↦ Real.sin s ^ 2)
      (Icc (-Real.pi) Real.pi) := (Real.continuous_sin.pow 2).integrableOn_Icc
  have hc2 : IntegrableOn (fun s : ℝ ↦ Real.cos s ^ 2)
      (Icc (-Real.pi) Real.pi) := (Real.continuous_cos.pow 2).integrableOn_Icc
  have hsc : IntegrableOn (fun s : ℝ ↦ Real.sin s * Real.cos s)
      (Icc (-Real.pi) Real.pi) :=
    (Real.continuous_sin.mul Real.continuous_cos).integrableOn_Icc
  have hpoint : ∀ s : ℝ,
      Real.sin (s + ε) * (a * Real.sin s + b * Real.cos s) =
        (a * Real.cos ε) * Real.sin s ^ 2 +
        (b * Real.sin ε) * Real.cos s ^ 2 +
        (b * Real.cos ε + a * Real.sin ε) * (Real.sin s * Real.cos s) := by
    intro s
    rw [Real.sin_add]
    ring
  rw [setIntegral_congr_fun measurableSet_Icc (fun s _ ↦ hpoint s),
    integral_add, integral_add,
    integral_const_mul, integral_const_mul, integral_const_mul,
    apm_m93J03_integral_sin_sq, apm_m93J03_integral_cos_sq,
    apm_m93J03_integral_sin_mul_cos]
  ring
  · exact hs2.const_mul _
  · exact hc2.const_mul _
  · exact (hs2.const_mul _).add (hc2.const_mul _)
  · exact hsc.const_mul _

lemma apm_m93J03_integral_cos_shift_mul_affine (ε a b : ℝ) :
    (∫ s in Icc (-Real.pi) Real.pi,
      Real.cos (s + ε) * (a * Real.sin s + b * Real.cos s)) =
      Real.pi * (b * Real.cos ε - a * Real.sin ε) := by
  have hs2 : IntegrableOn (fun s : ℝ ↦ Real.sin s ^ 2)
      (Icc (-Real.pi) Real.pi) := (Real.continuous_sin.pow 2).integrableOn_Icc
  have hc2 : IntegrableOn (fun s : ℝ ↦ Real.cos s ^ 2)
      (Icc (-Real.pi) Real.pi) := (Real.continuous_cos.pow 2).integrableOn_Icc
  have hsc : IntegrableOn (fun s : ℝ ↦ Real.sin s * Real.cos s)
      (Icc (-Real.pi) Real.pi) :=
    (Real.continuous_sin.mul Real.continuous_cos).integrableOn_Icc
  have hpoint : ∀ s : ℝ,
      Real.cos (s + ε) * (a * Real.sin s + b * Real.cos s) =
        (b * Real.cos ε) * Real.cos s ^ 2 -
        (a * Real.sin ε) * Real.sin s ^ 2 +
        (a * Real.cos ε - b * Real.sin ε) * (Real.sin s * Real.cos s) := by
    intro s
    rw [Real.cos_add]
    ring
  rw [setIntegral_congr_fun measurableSet_Icc (fun s _ ↦ hpoint s),
    integral_add, integral_sub,
    integral_const_mul, integral_const_mul, integral_const_mul,
    apm_m93J03_integral_sin_sq, apm_m93J03_integral_cos_sq,
    apm_m93J03_integral_sin_mul_cos]
  ring
  · exact hc2.const_mul _
  · exact hs2.const_mul _
  · exact (hc2.const_mul _).sub (hs2.const_mul _)
  · exact hsc.const_mul _

lemma apm_m93J03_integral_sin_remainder_bound (ε a b : ℝ) :
    |∫ s in Icc (-Real.pi) Real.pi,
      (Real.sin ((s + ε) + (a * Real.sin s + b * Real.cos s)) -
        Real.sin (s + ε) -
        Real.cos (s + ε) * (a * Real.sin s + b * Real.cos s))| ≤
      (|a| + |b|) ^ 2 * (2 * Real.pi) := by
  have hpoint : ∀ s ∈ Icc (-Real.pi) Real.pi,
      ‖Real.sin ((s + ε) + (a * Real.sin s + b * Real.cos s)) -
        Real.sin (s + ε) -
        Real.cos (s + ε) * (a * Real.sin s + b * Real.cos s)‖ ≤
        (|a| + |b|) ^ 2 := by
    intro s hs
    rw [Real.norm_eq_abs]
    refine (apm_m93J03_abs_sin_add_sub_linear_le (s + ε)
      (a * Real.sin s + b * Real.cos s)).trans ?_
    have hz : |a * Real.sin s + b * Real.cos s| ≤ |a| + |b| := by
      calc
        |a * Real.sin s + b * Real.cos s| ≤
            |a * Real.sin s| + |b * Real.cos s| := abs_add_le _ _
        _ = |a| * |Real.sin s| + |b| * |Real.cos s| := by rw [abs_mul, abs_mul]
        _ ≤ |a| * 1 + |b| * 1 := add_le_add
          (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one s) (abs_nonneg a))
          (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one s) (abs_nonneg b))
        _ = |a| + |b| := by ring
    exact (sq_le_sq₀ (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))).2 hz
  have h := norm_setIntegral_le_of_norm_le_const
    (measure_Icc_lt_top (μ := volume)) hpoint
  rw [Real.norm_eq_abs] at h
  have hvol : volume.real (Icc (-Real.pi) Real.pi) = 2 * Real.pi := by
    simp [Measure.real, Real.pi_pos.le]
    ring
  rw [hvol] at h
  exact h

lemma apm_m93J03_integral_cos_remainder_bound (ε a b : ℝ) :
    |∫ s in Icc (-Real.pi) Real.pi,
      (Real.cos ((s + ε) + (a * Real.sin s + b * Real.cos s)) -
        Real.cos (s + ε) +
        Real.sin (s + ε) * (a * Real.sin s + b * Real.cos s))| ≤
      (|a| + |b|) ^ 2 * (2 * Real.pi) := by
  have hpoint : ∀ s ∈ Icc (-Real.pi) Real.pi,
      ‖Real.cos ((s + ε) + (a * Real.sin s + b * Real.cos s)) -
        Real.cos (s + ε) +
        Real.sin (s + ε) * (a * Real.sin s + b * Real.cos s)‖ ≤
        (|a| + |b|) ^ 2 := by
    intro s hs
    rw [Real.norm_eq_abs]
    refine (apm_m93J03_abs_cos_add_sub_linear_le (s + ε)
      (a * Real.sin s + b * Real.cos s)).trans ?_
    have hz : |a * Real.sin s + b * Real.cos s| ≤ |a| + |b| := by
      calc
        |a * Real.sin s + b * Real.cos s| ≤
            |a * Real.sin s| + |b * Real.cos s| := abs_add_le _ _
        _ = |a| * |Real.sin s| + |b| * |Real.cos s| := by rw [abs_mul, abs_mul]
        _ ≤ |a| * 1 + |b| * 1 := add_le_add
          (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one s) (abs_nonneg a))
          (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one s) (abs_nonneg b))
        _ = |a| + |b| := by ring
    exact (sq_le_sq₀ (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))).2 hz
  have h := norm_setIntegral_le_of_norm_le_const
    (measure_Icc_lt_top (μ := volume)) hpoint
  rw [Real.norm_eq_abs] at h
  have hvol : volume.real (Icc (-Real.pi) Real.pi) = 2 * Real.pi := by
    simp [Measure.real, Real.pi_pos.le]
    ring
  rw [hvol] at h
  exact h

/-- A residual zero satisfies the explicit linearized system up to two
quadratically small remainder coordinates. -/
lemma apm_m93J03_residual_linearized_bounds {ε a b : ℝ}
    (hres : apm_m93J03_residual ε (a, b) = 0) :
    |a + Real.pi * (a * Real.cos ε + b * Real.sin ε)| ≤
        (|a| + |b|) ^ 2 * (2 * Real.pi) ∧
    |b - Real.pi * (b * Real.cos ε - a * Real.sin ε)| ≤
        (|a| + |b|) ^ 2 * (2 * Real.pi) := by
  let z : ℝ → ℝ := fun s ↦ a * Real.sin s + b * Real.cos s
  have ha : a = ∫ s in Icc (-Real.pi) Real.pi,
      Real.cos ((s + ε) + z s) := by
    have h := congrArg Prod.fst hres
    have h0 := sub_eq_zero.mp (by simpa [apm_m93J03_residual] using h)
    rw [h0]
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    simp only [z, apm_m93J03_affineTrig]
    congr 1
    ring
  have hb : b = ∫ s in Icc (-Real.pi) Real.pi,
      Real.sin ((s + ε) + z s) := by
    have h := congrArg Prod.snd hres
    have h0 := sub_eq_zero.mp (by simpa [apm_m93J03_residual] using h)
    rw [h0]
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    simp only [z, apm_m93J03_affineTrig]
    congr 1
    ring
  have hcosN : IntegrableOn (fun s : ℝ ↦ Real.cos ((s + ε) + z s))
      (Icc (-Real.pi) Real.pi) := (by fun_prop : Continuous _).integrableOn_Icc
  have hsinN : IntegrableOn (fun s : ℝ ↦ Real.sin ((s + ε) + z s))
      (Icc (-Real.pi) Real.pi) := (by fun_prop : Continuous _).integrableOn_Icc
  have hcos0 : IntegrableOn (fun s : ℝ ↦ Real.cos (s + ε))
      (Icc (-Real.pi) Real.pi) := (by fun_prop : Continuous _).integrableOn_Icc
  have hsin0 : IntegrableOn (fun s : ℝ ↦ Real.sin (s + ε))
      (Icc (-Real.pi) Real.pi) := (by fun_prop : Continuous _).integrableOn_Icc
  have hsinZ : IntegrableOn (fun s : ℝ ↦ Real.sin (s + ε) * z s)
      (Icc (-Real.pi) Real.pi) := (by fun_prop : Continuous _).integrableOn_Icc
  have hcosZ : IntegrableOn (fun s : ℝ ↦ Real.cos (s + ε) * z s)
      (Icc (-Real.pi) Real.pi) := (by fun_prop : Continuous _).integrableOn_Icc
  have hA : a + Real.pi * (a * Real.cos ε + b * Real.sin ε) =
      ∫ s in Icc (-Real.pi) Real.pi,
        (Real.cos ((s + ε) + z s) - Real.cos (s + ε) +
          Real.sin (s + ε) * z s) := by
    change _ = ∫ s, (Real.cos ((s + ε) + z s) - Real.cos (s + ε) +
      Real.sin (s + ε) * z s) ∂volume.restrict (Icc (-Real.pi) Real.pi)
    rw [integral_add, integral_sub, ← ha, apm_m93J03_integral_cos_shift,
      show (∫ s in Icc (-Real.pi) Real.pi, Real.sin (s + ε) * z s) =
        Real.pi * (a * Real.cos ε + b * Real.sin ε) by
          simpa [z] using apm_m93J03_integral_sin_shift_mul_affine ε a b]
    ring
    · exact hcosN
    · exact hcos0
    · exact hcosN.sub hcos0
    · exact hsinZ
  have hB : b - Real.pi * (b * Real.cos ε - a * Real.sin ε) =
      ∫ s in Icc (-Real.pi) Real.pi,
        (Real.sin ((s + ε) + z s) - Real.sin (s + ε) -
          Real.cos (s + ε) * z s) := by
    change _ = ∫ s, (Real.sin ((s + ε) + z s) - Real.sin (s + ε) -
      Real.cos (s + ε) * z s) ∂volume.restrict (Icc (-Real.pi) Real.pi)
    rw [integral_sub, integral_sub, ← hb, apm_m93J03_integral_sin_shift,
      show (∫ s in Icc (-Real.pi) Real.pi, Real.cos (s + ε) * z s) =
        Real.pi * (b * Real.cos ε - a * Real.sin ε) by
          simpa [z] using apm_m93J03_integral_cos_shift_mul_affine ε a b]
    ring
    · exact hsinN
    · exact hsin0
    · exact hsinN.sub hsin0
    · exact hcosZ
  constructor
  · rw [hA]
    simpa [z] using apm_m93J03_integral_cos_remainder_bound ε a b
  · rw [hB]
    simpa [z] using apm_m93J03_integral_sin_remainder_bound ε a b

/-- The phase-dependent linear system stays uniformly invertible on the
explicit parameter interval `|ε| ≤ 1/16`. -/
lemma apm_m93J03_linearized_lower_bound {ε a b : ℝ}
    (hε : |ε| ≤ (1 : ℝ) / 16) :
    |a| + |b| ≤
      |a + Real.pi * (a * Real.cos ε + b * Real.sin ε)| +
      |b - Real.pi * (b * Real.cos ε - a * Real.sin ε)| := by
  let A := a + Real.pi * (a * Real.cos ε + b * Real.sin ε)
  let B := b - Real.pi * (b * Real.cos ε - a * Real.sin ε)
  let A₀ := (1 + Real.pi) * a
  let B₀ := (1 - Real.pi) * b
  let q := |a| + |b|
  have hsin : |Real.sin ε| ≤ (1 : ℝ) / 16 :=
    Real.abs_sin_le_abs.trans hε
  have hcos : |Real.cos ε - 1| ≤ (1 : ℝ) / 16 := by
    have h := Real.abs_cos_sub_cos_le ε 0
    have h' : |Real.cos ε - 1| ≤ |ε| := by simpa using h
    exact h'.trans hε
  have hq : 0 ≤ q := add_nonneg (abs_nonneg a) (abs_nonneg b)
  have hinnerA :
      |a * (Real.cos ε - 1) + b * Real.sin ε| ≤ q / 16 := by
    calc
      |a * (Real.cos ε - 1) + b * Real.sin ε| ≤
          |a * (Real.cos ε - 1)| + |b * Real.sin ε| := abs_add_le _ _
      _ = |a| * |Real.cos ε - 1| + |b| * |Real.sin ε| := by
        rw [abs_mul, abs_mul]
      _ ≤ |a| * ((1 : ℝ) / 16) + |b| * ((1 : ℝ) / 16) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hcos (abs_nonneg a))
          (mul_le_mul_of_nonneg_left hsin (abs_nonneg b))
      _ = q / 16 := by simp [q]; ring
  have hinnerB :
      |b * (Real.cos ε - 1) - a * Real.sin ε| ≤ q / 16 := by
    calc
      |b * (Real.cos ε - 1) - a * Real.sin ε| ≤
          |b * (Real.cos ε - 1)| + |a * Real.sin ε| := by
            rw [sub_eq_add_neg]
            simpa using abs_add_le (b * (Real.cos ε - 1)) (-(a * Real.sin ε))
      _ = |b| * |Real.cos ε - 1| + |a| * |Real.sin ε| := by
        rw [abs_mul, abs_mul]
      _ ≤ |b| * ((1 : ℝ) / 16) + |a| * ((1 : ℝ) / 16) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hcos (abs_nonneg b))
          (mul_le_mul_of_nonneg_left hsin (abs_nonneg a))
      _ = q / 16 := by simp [q]; ring
  have hAdiff : A - A₀ =
      Real.pi * (a * (Real.cos ε - 1) + b * Real.sin ε) := by
    simp only [A, A₀]
    ring
  have hBdiff : B - B₀ =
      -Real.pi * (b * (Real.cos ε - 1) - a * Real.sin ε) := by
    simp only [B, B₀]
    ring
  have hpertA : |A - A₀| ≤ Real.pi * (q / 16) := by
    rw [hAdiff, abs_mul, abs_of_pos Real.pi_pos]
    exact mul_le_mul_of_nonneg_left hinnerA Real.pi_pos.le
  have hpertB : |B - B₀| ≤ Real.pi * (q / 16) := by
    rw [hBdiff, abs_mul, abs_neg, abs_of_pos Real.pi_pos]
    exact mul_le_mul_of_nonneg_left hinnerB Real.pi_pos.le
  have hpert : |A - A₀| + |B - B₀| ≤ q / 2 := by
    calc
      |A - A₀| + |B - B₀| ≤
          Real.pi * (q / 16) + Real.pi * (q / 16) := add_le_add hpertA hpertB
      _ = Real.pi * (q / 8) := by ring
      _ ≤ 4 * (q / 8) :=
        mul_le_mul_of_nonneg_right Real.pi_le_four (by positivity)
      _ = q / 2 := by ring
  have hbase : 2 * q ≤ |A₀| + |B₀| := by
    have hp1 : 0 < 1 + Real.pi := by positivity
    have h1p : 1 - Real.pi < 0 := by linarith [Real.pi_gt_three]
    simp only [A₀, B₀, abs_mul, abs_of_pos hp1, abs_of_neg h1p]
    simp only [q]
    nlinarith [Real.pi_gt_three, abs_nonneg a, abs_nonneg b]
  have htriA : |A₀| ≤ |A| + |A - A₀| := by
    calc
      |A₀| = |A + -(A - A₀)| := by congr 1; ring
      _ ≤ |A| + |-(A - A₀)| := abs_add_le _ _
      _ = |A| + |A - A₀| := by rw [abs_neg]
  have htriB : |B₀| ≤ |B| + |B - B₀| := by
    calc
      |B₀| = |B + -(B - B₀)| := by congr 1; ring
      _ ≤ |B| + |-(B - B₀)| := abs_add_le _ _
      _ = |B| + |B - B₀| := by rw [abs_neg]
  change q ≤ |A| + |B|
  linarith

lemma apm_m93J03_residual_zero_isolated {ε a b : ℝ}
    (hε : |ε| ≤ (1 : ℝ) / 16)
    (hq : |a| + |b| < (1 : ℝ) / 32)
    (hres : apm_m93J03_residual ε (a, b) = 0) :
    a = 0 ∧ b = 0 := by
  let q := |a| + |b|
  let A := a + Real.pi * (a * Real.cos ε + b * Real.sin ε)
  let B := b - Real.pi * (b * Real.cos ε - a * Real.sin ε)
  have hq0 : 0 ≤ q := add_nonneg (abs_nonneg a) (abs_nonneg b)
  have hlower : q ≤ |A| + |B| := by
    simpa [q, A, B] using apm_m93J03_linearized_lower_bound (a := a) (b := b) hε
  have hr := apm_m93J03_residual_linearized_bounds hres
  have hupper : |A| + |B| ≤ 4 * Real.pi * q ^ 2 := by
    simp only [A, B]
    have := add_le_add hr.1 hr.2
    simp only [q]
    nlinarith
  have hqsmall : q < (1 : ℝ) / 32 := by simpa [q] using hq
  have hqeq : q = 0 := by
    by_contra hn
    have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hn)
    have hpq : 4 * Real.pi * q < 1 := by
      have hprod : 0 < (4 - Real.pi) * q :=
        mul_pos (sub_pos.mpr Real.pi_lt_four) hqpos
      nlinarith
    have hstrict : 4 * Real.pi * q ^ 2 < q := by
      have := mul_lt_mul_of_pos_right hpq hqpos
      nlinarith
    nlinarith
  have ha0 : |a| = 0 := by
    simp only [q] at hqeq
    nlinarith [abs_nonneg a, abs_nonneg b]
  have hb0 : |b| = 0 := by
    simp only [q] at hqeq
    nlinarith [abs_nonneg a, abs_nonneg b]
  exact ⟨abs_eq_zero.mp ha0, abs_eq_zero.mp hb0⟩

theorem apm_m93j03 :
    ∃ δ η : ℝ, 0 < δ ∧ 0 < η ∧
      ∀ ε : ℝ, |ε| < δ →
        ∃ x : ℝ → ℝ,
          apm_m93J03_isSolution ε x ∧
          apm_m93J03_isSmall x η ∧
          ∀ y : ℝ → ℝ,
            apm_m93J03_isSolution ε y →
            apm_m93J03_isSmall y η →
            EqOn x y (Icc (-Real.pi) Real.pi) := by
  /-
  CLOSER HOPS 5--6 (partial). The existence side is now entirely closed
  without any implicit-function machinery: `apm_m93J03_const_isSolution`
  proves that `x t = ε` is an exact solution for every parameter, using
  full-period cancellation, and `apm_m93J03_exists_small_solution` supplies
  its uniform size bound. `apm_m93J03_residual_zero` records the same fact in
  the finite-dimensional presentation.

  The uniqueness input has also been sharpened to a bounded-zero interface.
  `apm_m93J03_small_solution_coefficients` bounds both affine coefficients by
  `η + δ` simply by evaluating at `0` and `π/2`.
  `apm_m93J03_isSolution_affineTrig_of_eqOn` transports the equation across
  interval equality, and `apm_m93J03_small_solution_reduction` combines these
  facts: every candidate small solution yields a residual zero `(a,b)` in an
  explicit coefficient box and is equal on the interval to its affine
  representative. Thus the only remaining theorem is isolation of `(0,0)`
  among residual zeros in some parameter/coefficient box; existence and the
  function-to-coefficient conversion no longer depend on that theorem.

  CLOSER HOP 7 (partial). The two scalar analytic estimates needed to isolate
  the zero are now compiled as
  `apm_m93J03_abs_sin_add_sub_linear_le` and
  `apm_m93J03_abs_cos_add_sub_linear_le`.  They give global quadratic
  remainders (with constant one) for linearization at an arbitrary phase.
  Their proofs use the mean-value inequality on the unordered interval from
  `0` to the increment and Mathlib's global one-Lipschitz estimates for sine
  and cosine.  The remaining work is to integrate these pointwise bounds for
  `z(s)=a sin s+b cos s`, calculate the resulting rotated `2 x 2` linear
  coefficient map, and combine its lower bound with the quadratic remainder
  and the compiled coefficient box.

  CLOSER HOP 8 (partial). The integration layer of that plan is now compiled.
  The exact orthogonality identities for `sin²`, `cos²`, and `sin*cos` on
  the frozen interval yield closed formulas for the two shifted linear terms:
  `π (a cos ε + b sin ε)` and `π (b cos ε - a sin ε)`.
  The pointwise quadratic Taylor estimates have also been lifted through the
  set integral: each integrated remainder is bounded by
  `2π (|a|+|b|)²`. The remaining algebraic step is to obtain a uniform lower
  bound for the resulting phase-dependent linear system when `|ε|` is small,
  then compare that bound with these quadratic upper bounds.

  CLOSER HOP 9 (partial). `apm_m93J03_residual_linearized_bounds` now performs
  the complete residual-to-inequality conversion. For every residual zero its
  two coordinates satisfy
  `|a + π(a cos ε + b sin ε)| ≤ 2π(|a|+|b|)²` and
  `|b - π(b cos ε - a sin ε)| ≤ 2π(|a|+|b|)²`.
  Shifted sine/cosine cancellation lemmas and all integrability bookkeeping
  are compiled inside this bridge. Consequently no integral goals remain in
  the uniqueness argument: it is now a real-algebra lower bound for this
  `2 x 2` system under `|ε|` small, followed by the quadratic comparison.

  CLOSER HOP 1 (partial). The uniform-radius bookkeeping is now compiled:
  `apm_m93J03_isSmall_mono` permits enlarging a valid solution radius and
  `apm_m93J03_zero_isSmall` supplies the trivial-branch base case.

  The remaining boundary: the intended proof first separates the sine kernel and proves
  that every solution on the interval has the exact form
  `ε + a * sin t + b * cos t`. It must then define the resulting map
  `H : ℝ × (ℝ × ℝ) → ℝ × ℝ`, establish its strict Frechet
  derivative by differentiating two parameterized interval integrals, and
  identify the partial Jacobian at zero with the invertible diagonal map
  having entries `1 + π` and `1 - π`.

  Renewed searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, solved
  implicit-function artifacts, the parametric-integral sources, and git
  history found no complete reduction. Mathlib's product-domain implicit-function APIs
  `ContDiffAt.implicitFunction`,
  `ContDiffAt.eventually_apply_eq_iff_implicitFunction`, and
  `HasStrictFDerivAt.implicitFunctionOfProdDomain`. Applying them here still
  requires the missing derivative-under-the-integral construction and the
  final conversion of their neighborhood uniqueness into the statement's
  uniform `apm_m93J03_isSmall` radius for arbitrary function-valued
  solutions. No compiled sibling supplied those bridges in this pass.

  CLOSER HOP 2 (partial). The function-level finite-dimensional reduction is
  now closed by `apm_m93J03_solution_eq_affine_trig`. For every frozen
  solution it constructs the two coefficients as the integrals of
  `cos (s + x s)` and `sin (s + x s)` and proves pointwise on the interval
  that `x t = ε + a * sin t + b * cos t`. Continuity of the solution supplies
  both restricted integrability obligations, and `Real.sin_add` plus
  `integral_add` and `integral_const_mul` perform the exact separation. Thus
  arbitrary function-valued uniqueness can now be reduced to uniqueness of
  the coefficient pair once the local finite-dimensional theorem is built.

  Searches beyond hop 1 inspected the repository's compiled parameter-
  differentiation users (`a01A09`, `a99J09`, `m93A04`, and `m98A03`) and
  Mathlib's dominated derivative-under-integral API. They confirm an available
  route but do not package the two-variable strict Frechet derivative needed
  here. The remaining bridge is to define the coefficient residual map,
  establish that derivative and its invertibility at zero, apply the product-
  domain implicit-function theorem, and extract uniform scalar radii. The
  frozen statement remains unchanged.

  CLOSER HOP 3 (partial). The finite-dimensional equation is now explicitly
  packaged. `apm_m93J03_affineTrig` defines the reconstructed function and
  `apm_m93J03_residual` defines the exact pair of coefficient residuals.
  `apm_m93J03_isSolution_affineTrig_of_residual_eq_zero` proves that every
  zero of this residual gives a genuine solution of the original integral
  equation, including continuity and the full pointwise identity on the
  frozen interval. It reuses the sine-addition separation and restricted-
  integral calculation from hop 2, so the future implicit-function theorem
  no longer needs to manipulate function-valued solutions on its existence
  side.

  I additionally inspected `Analysis.Calculus.Implicit`,
  `ImplicitFunction.ProdDomain`, `ImplicitContDiff`, the parameter-integral
  differentiation sources, and sibling `m98A05`. They provide the abstract
  local implicit-function machinery, but still no packaged strict Frechet
  derivative for these two parameterized set integrals. The remaining bridge
  is precisely that derivative/Jacobian computation, its invertibility, and
  extraction of uniform scalar radii plus coefficient uniqueness. The frozen
  statement remains unchanged.

  HOP 4 inspected
  `hasFDerivAt_integral_of_dominated_of_fderiv_le`, its set/interval
  variants, and `HasStrictFDerivAt.implicitFunctionOfProdDomain`. The former
  produces only an ordinary Frechet derivative, while the latter genuinely
  requires a strict derivative. No theorem in this snapshot upgrades these
  parameter integrals to a strict derivative or packages their smoothness.

  The exact missing lemma is:

    `∃ L : (ℝ × (ℝ × ℝ)) →L[ℝ] (ℝ × ℝ),
      HasStrictFDerivAt
        (fun z : ℝ × (ℝ × ℝ) => apm_m93J03_residual z.1 z.2)
        L (0, (0, 0)) ∧
      ∀ h : ℝ × (ℝ × ℝ),
        L h = ((1 + Real.pi) * h.2.1,
          (1 - Real.pi) * h.2.2)`.

  The formula follows by differentiating under the two restricted integrals:
  the mixed and epsilon entries integrate `sin`, `cos`, or `sin*cos` to zero,
  while `sin^2` and `cos^2` both integrate to `π`. Its partial map in the
  coefficient variables is therefore diagonal with nonzero entries
  `1 + π` and `1 - π`, exactly what the product-domain implicit-function
  theorem needs. Proving this strict estimate (or a `ContDiff` theorem that
  implies it) remains the identified Mathlib hole; no weaker assertion was
  introduced and the frozen statement is unchanged.
  -/
  refine ⟨(1 : ℝ) / 256, (1 : ℝ) / 256, by norm_num, by norm_num, ?_⟩
  intro ε hε
  refine ⟨fun _ ↦ ε, apm_m93J03_const_isSolution ε, ?_, ?_⟩
  · intro t ht
    exact hε
  · intro y hy hsmall
    rcases apm_m93J03_small_solution_reduction hy hsmall hε with
      ⟨a, b, heq, hres, ha, hb⟩
    have hε' : |ε| ≤ (1 : ℝ) / 16 := by
      exact (le_of_lt hε).trans (by norm_num)
    have hq : |a| + |b| < (1 : ℝ) / 32 := by
      norm_num at ha hb ⊢
      linarith
    rcases apm_m93J03_residual_zero_isolated hε' hq hres with ⟨rfl, rfl⟩
    intro t ht
    have h := heq ht
    simpa [apm_m93J03_affineTrig] using h.symm
