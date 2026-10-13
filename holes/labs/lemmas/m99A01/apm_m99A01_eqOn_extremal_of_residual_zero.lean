import Mathlib

/-!
# APM m99A01

## Statement repairs

The source does not specify the admissible function class. The functional is
encoded on `C¹` curves, and extremals are `C²` stationary curves, the standard
minimal regularity needed for the classical Euler--Lagrange formulation.

The classification of extremals is up to equality on `[0, π/2]`. Curves are
functions `ℝ → ℝ` and the functional only sees `[0, π/2]`, so a stationary
curve changed by a smooth bump outside the interval is still stationary; the
earlier conclusion `y = apm_m99A01_extremal` on all of `ℝ` was false (the
same defect as m02A05 and m95A03, repaired 2026-09-30).

## Encoding questions

An extremal is encoded intrinsically by vanishing first variation for every
`C¹` endpoint-fixing variation, rather than by taking the Euler--Lagrange ODE
as its definition.
-/

open Set intervalIntegral

/-- The functional in the problem. -/
noncomputable def apm_m99A01_functional (y : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..(Real.pi / 2), (deriv y t) ^ 2 + (y t) ^ 2 + 2 * y t

/-- Curves satisfying the stated endpoint constraints. -/
def apm_m99A01_admissible : Set (ℝ → ℝ) :=
  {y | ContDiff ℝ 1 y ∧ y 0 = 0 ∧ y (Real.pi / 2) = 0}

/-- Stationarity under all endpoint-fixing first variations. -/
def apm_m99A01_stationary (y : ℝ → ℝ) : Prop :=
  ∀ η : ℝ → ℝ, ContDiff ℝ 1 η → η 0 = 0 → η (Real.pi / 2) = 0 →
    HasDerivAt
      (fun s ↦ apm_m99A01_functional (fun t ↦ y t + s * η t)) 0 0

/-- The unique candidate extremal obtained from the boundary-value problem. -/
noncomputable def apm_m99A01_extremal (t : ℝ) : ℝ :=
  Real.cosh t - Real.tanh (Real.pi / 4) * Real.sinh t - 1

/-- Euler--Lagrange residual for the inhomogeneous equation `y'' - y = 1`. -/
noncomputable def apm_m99A01_residual (y : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (deriv y) t - y t - 1

/-- The displayed candidate solves the inhomogeneous Euler--Lagrange ODE. -/
lemma apm_m99A01_extremal_ode (t : ℝ) :
    deriv (deriv apm_m99A01_extremal) t - apm_m99A01_extremal t = 1 := by
  have h₁ : deriv apm_m99A01_extremal =
      fun x ↦ Real.sinh x - Real.tanh (Real.pi / 4) * Real.cosh x := by
    funext x
    change deriv (fun z ↦ Real.cosh z - Real.tanh (Real.pi / 4) * Real.sinh z - 1) x = _
    simpa using ((Real.hasDerivAt_cosh x).sub
      ((hasDerivAt_const x (Real.tanh (Real.pi / 4))).mul
        (Real.hasDerivAt_sinh x))).sub_const 1 |>.deriv
  have h₂ : deriv (fun x ↦
      Real.sinh x - Real.tanh (Real.pi / 4) * Real.cosh x) =
      fun x ↦ Real.cosh x - Real.tanh (Real.pi / 4) * Real.sinh x := by
    funext x
    simpa using ((Real.hasDerivAt_sinh x).sub
      ((hasDerivAt_const x (Real.tanh (Real.pi / 4))).mul
        (Real.hasDerivAt_cosh x))) |>.deriv
  rw [h₁, h₂]
  unfold apm_m99A01_extremal
  ring

/-- A concrete endpoint-fixing family used to witness unboundedness above. -/
lemma apm_m99A01_sine_family_admissible (n : ℝ) :
    (fun t : ℝ ↦ n * Real.sin (2 * t)) ∈ apm_m99A01_admissible := by
  refine ⟨by fun_prop, by simp, ?_⟩
  dsimp
  rw [show 2 * (Real.pi / 2) = Real.pi by ring]
  simp

/-- Derivative of the endpoint-fixing family used in the unboundedness
argument. -/
lemma apm_m99A01_deriv_sine_family (n t : ℝ) :
    deriv (fun x : ℝ => n * Real.sin (2 * x)) t =
      2 * n * Real.cos (2 * t) := by
  have h := ((Real.hasDerivAt_sin (2 * t)).comp t
    ((hasDerivAt_id t).const_mul 2)).const_mul n
  convert h.deriv using 1 <;> ring

lemma apm_m99A01_integral_cos_sq_two_mul :
    ∫ t in (0 : ℝ)..(Real.pi / 2), Real.cos (2 * t) ^ 2 = Real.pi / 4 := by
  have h := intervalIntegral.mul_integral_comp_mul_left
    (f := fun x : ℝ => Real.cos x ^ 2) (a := (0 : ℝ))
    (b := Real.pi / 2) (c := (2 : ℝ))
  rw [integral_cos_sq] at h
  norm_num [show 2 * (Real.pi / 2) = Real.pi by ring] at h ⊢
  linarith

lemma apm_m99A01_integral_sin_sq_two_mul :
    ∫ t in (0 : ℝ)..(Real.pi / 2), Real.sin (2 * t) ^ 2 = Real.pi / 4 := by
  have h := intervalIntegral.mul_integral_comp_mul_left
    (f := fun x : ℝ => Real.sin x ^ 2) (a := (0 : ℝ))
    (b := Real.pi / 2) (c := (2 : ℝ))
  rw [integral_sin_sq] at h
  norm_num [show 2 * (Real.pi / 2) = Real.pi by ring] at h ⊢
  linarith

lemma apm_m99A01_integral_sin_two_mul :
    ∫ t in (0 : ℝ)..(Real.pi / 2), Real.sin (2 * t) = 1 := by
  have h := intervalIntegral.mul_integral_comp_mul_left
    (f := Real.sin) (a := (0 : ℝ)) (b := Real.pi / 2) (c := (2 : ℝ))
  rw [integral_sin] at h
  norm_num [show 2 * (Real.pi / 2) = Real.pi by ring] at h ⊢

/-- Exact value of the functional on the unbounded endpoint-zero family. -/
lemma apm_m99A01_functional_sine_family (n : ℝ) :
    apm_m99A01_functional (fun t : ℝ => n * Real.sin (2 * t)) =
      (5 * Real.pi / 4) * n ^ 2 + 2 * n := by
  unfold apm_m99A01_functional
  simp_rw [apm_m99A01_deriv_sine_family n]
  have hpoint : (fun t : ℝ =>
      (2 * n * Real.cos (2 * t)) ^ 2 + (n * Real.sin (2 * t)) ^ 2 +
        2 * (n * Real.sin (2 * t))) =
      fun t => 4 * n ^ 2 * (Real.cos (2 * t) ^ 2) +
        n ^ 2 * (Real.sin (2 * t) ^ 2) + 2 * n * Real.sin (2 * t) := by
    funext t
    ring
  rw [hpoint]
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_add]
    · simp only [intervalIntegral.integral_const_mul]
      rw [apm_m99A01_integral_cos_sq_two_mul,
        apm_m99A01_integral_sin_sq_two_mul,
        apm_m99A01_integral_sin_two_mul]
      ring
    · apply Continuous.intervalIntegrable
      fun_prop
    · apply Continuous.intervalIntegrable
      fun_prop
  · apply Continuous.intervalIntegrable
    fun_prop
  · apply Continuous.intervalIntegrable
    fun_prop

/-- The functional is unbounded above on the admissible class. -/
lemma apm_m99A01_no_maximum :
    ¬ ∃ y ∈ apm_m99A01_admissible, ∀ z ∈ apm_m99A01_admissible,
      apm_m99A01_functional z ≤ apm_m99A01_functional y := by
  rintro ⟨y, hy, hmax⟩
  let n : ℝ := |apm_m99A01_functional y| + 1
  have hnmem := apm_m99A01_sine_family_admissible n
  have hle := hmax (fun t : ℝ => n * Real.sin (2 * t)) hnmem
  rw [apm_m99A01_functional_sine_family] at hle
  have hquad : 0 ≤ (5 * Real.pi / 4) * n ^ 2 := by positivity
  have habs : apm_m99A01_functional y ≤ |apm_m99A01_functional y| :=
    le_abs_self _
  dsimp [n] at hle hquad
  have htwo : 2 * (|apm_m99A01_functional y| + 1) ≤
      apm_m99A01_functional y := by
    exact le_trans (by linarith only [hquad]) hle
  linarith [abs_nonneg (apm_m99A01_functional y)]

/-- Continuity upgrades the almost-everywhere conclusion of Mathlib's
distributional fundamental lemma to the pointwise statement needed for the
Euler--Lagrange ODE. -/
lemma apm_m99A01_eq_zero_on_Ioo_of_ae
    (f : ℝ → ℝ) (hf : ContinuousOn f (Ioo 0 (Real.pi / 2)))
    (hae : ∀ᵐ x ∂MeasureTheory.volume,
      x ∈ Ioo 0 (Real.pi / 2) → f x = 0) :
    ∀ x ∈ Ioo 0 (Real.pi / 2), f x = 0 := by
  have hae' : f =ᵐ[MeasureTheory.volume.restrict (Ioo 0 (Real.pi / 2))]
      (0 : ℝ → ℝ) := by
    change ∀ᵐ x ∂MeasureTheory.volume.restrict (Ioo 0 (Real.pi / 2)), f x = 0
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact hae
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo hf
    continuous_zero.continuousOn

lemma apm_m99A01_extremal_cross_zero
    (h : ℝ → ℝ) (hh : ContDiff ℝ 1 h)
    (hh0 : h 0 = 0) (hhpi : h (Real.pi / 2) = 0) :
    ∫ t in (0 : ℝ)..(Real.pi / 2),
      deriv apm_m99A01_extremal t * deriv h t +
        (apm_m99A01_extremal t + 1) * h t = 0 := by
  have he : ContDiff ℝ 2 apm_m99A01_extremal := by
    unfold apm_m99A01_extremal
    fun_prop
  have hde : ContDiff ℝ 1 (deriv apm_m99A01_extremal) := he.deriv'
  have hue : ∀ x ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv apm_m99A01_extremal)
        (apm_m99A01_extremal x + 1) x := by
    intro x hx
    have hd := hde.differentiable (by norm_num) x |>.hasDerivAt
    convert hd using 1
    linarith [apm_m99A01_extremal_ode x]
  have hv : ∀ x ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
      HasDerivAt h (deriv h x) x := by
    intro x hx
    exact (hh.differentiable (by norm_num) x).hasDerivAt
  have hu'int : IntervalIntegrable (fun x ↦ apm_m99A01_extremal x + 1)
      MeasureTheory.volume 0 (Real.pi / 2) :=
    (he.continuous.add continuous_const).intervalIntegrable _ _
  have hdh : ContDiff ℝ 0 (deriv h) := hh.deriv'
  have hv'int : IntervalIntegrable (deriv h) MeasureTheory.volume 0 (Real.pi / 2) :=
    hdh.continuous.intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hue hv hu'int hv'int
  rw [hh0, hhpi] at hibp
  rw [intervalIntegral.integral_add]
  · linarith
  · exact hv'int.continuousOn_mul hde.continuous.continuousOn
  · exact hu'int.mul_continuousOn hh.continuous.continuousOn

lemma apm_m99A01_functional_sub_extremal
    (y : ℝ → ℝ) (hy : y ∈ apm_m99A01_admissible) :
    apm_m99A01_functional y = apm_m99A01_functional apm_m99A01_extremal +
      ∫ t in (0 : ℝ)..(Real.pi / 2),
        deriv (fun x ↦ y x - apm_m99A01_extremal x) t ^ 2 +
          (y t - apm_m99A01_extremal t) ^ 2 := by
  let h := fun x ↦ y x - apm_m99A01_extremal x
  have he : ContDiff ℝ 2 apm_m99A01_extremal := by
    unfold apm_m99A01_extremal
    fun_prop
  have hh : ContDiff ℝ 1 h := hy.1.sub (he.of_le (by norm_num))
  have hde : ContDiff ℝ 1 (deriv apm_m99A01_extremal) := he.deriv'
  have hdh : ContDiff ℝ 0 (deriv h) := hh.deriv'
  have he0 : apm_m99A01_extremal 0 = 0 := by simp [apm_m99A01_extremal]
  have hepi : apm_m99A01_extremal (Real.pi / 2) = 0 := by
    unfold apm_m99A01_extremal
    have hc : Real.cosh (Real.pi / 4) ≠ 0 := ne_of_gt (Real.cosh_pos _)
    rw [show Real.pi / 2 = 2 * (Real.pi / 4) by ring,
      Real.cosh_two_mul, Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
    field_simp [hc]
    nlinarith [Real.cosh_sq_sub_sinh_sq (Real.pi / 4)]
  have hcross := apm_m99A01_extremal_cross_zero h hh
    (by simp [h, hy.2.1, he0]) (by simp [h, hy.2.2, hepi])
  have hpoint : (fun t ↦ deriv y t ^ 2 + y t ^ 2 + 2 * y t) =
      fun t ↦
        (deriv apm_m99A01_extremal t ^ 2 + apm_m99A01_extremal t ^ 2 +
          2 * apm_m99A01_extremal t) +
        (deriv h t ^ 2 + h t ^ 2) +
        2 * (deriv apm_m99A01_extremal t * deriv h t +
          (apm_m99A01_extremal t + 1) * h t) := by
    funext t
    have hyd := hy.1.differentiable (by norm_num) t
    have hed := he.differentiable (by norm_num) t
    have hdecomp : y = fun x ↦ apm_m99A01_extremal x + h x := by
      funext x
      simp [h]
    rw [hdecomp]
    have hdadd : deriv (fun x ↦ apm_m99A01_extremal x + h x) t =
        deriv apm_m99A01_extremal t + deriv h t := by
      simpa only [Pi.add_apply] using
        deriv_add hed (hh.differentiable (by norm_num) t)
    rw [hdadd]
    ring
  unfold apm_m99A01_functional
  rw [hpoint]
  have hbase : IntervalIntegrable (fun t ↦
      deriv apm_m99A01_extremal t ^ 2 + apm_m99A01_extremal t ^ 2 +
        2 * apm_m99A01_extremal t) MeasureTheory.volume 0 (Real.pi / 2) :=
    ((hde.continuous.pow 2).add (he.continuous.pow 2) |>.add
      (continuous_const.mul he.continuous)).intervalIntegrable _ _
  have hsquares : IntervalIntegrable (fun t ↦ deriv h t ^ 2 + h t ^ 2)
      MeasureTheory.volume 0 (Real.pi / 2) :=
    ((hdh.continuous.pow 2).add (hh.continuous.pow 2)).intervalIntegrable _ _
  have hcrossint : IntervalIntegrable (fun t ↦ 2 *
      (deriv apm_m99A01_extremal t * deriv h t +
        (apm_m99A01_extremal t + 1) * h t)) MeasureTheory.volume 0 (Real.pi / 2) :=
    (continuous_const.mul ((hde.continuous.mul hdh.continuous).add
      ((he.continuous.add continuous_const).mul hh.continuous))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hbase.add hsquares) hcrossint,
    intervalIntegral.integral_add hbase hsquares,
    intervalIntegral.integral_const_mul, hcross]
  simp [h]

lemma apm_m99A01_line_to_extremal
    (y : ℝ → ℝ) (hy : y ∈ apm_m99A01_admissible) (s : ℝ) :
    apm_m99A01_functional
        (fun t ↦ y t + s * (apm_m99A01_extremal t - y t)) =
      apm_m99A01_functional apm_m99A01_extremal +
        (1 - s) ^ 2 *
          (∫ t in (0 : ℝ)..(Real.pi / 2),
            deriv (fun x ↦ y x - apm_m99A01_extremal x) t ^ 2 +
              (y t - apm_m99A01_extremal t) ^ 2) := by
  let z := fun t ↦ y t + s * (apm_m99A01_extremal t - y t)
  have he : apm_m99A01_extremal ∈ apm_m99A01_admissible := by
    refine ⟨?_, by simp [apm_m99A01_extremal], ?_⟩
    · unfold apm_m99A01_extremal
      fun_prop
    · unfold apm_m99A01_extremal
      have hc : Real.cosh (Real.pi / 4) ≠ 0 := ne_of_gt (Real.cosh_pos _)
      rw [show Real.pi / 2 = 2 * (Real.pi / 4) by ring,
        Real.cosh_two_mul, Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
      field_simp [hc]
      nlinarith [Real.cosh_sq_sub_sinh_sq (Real.pi / 4)]
  have hz : z ∈ apm_m99A01_admissible := by
    refine ⟨hy.1.add ((he.1.sub hy.1).const_smul s), ?_, ?_⟩
    · simp [z, hy.2.1, he.2.1]
    · simp [z, hy.2.2, he.2.2]
  rw [show (fun t ↦ y t + s * (apm_m99A01_extremal t - y t)) = z from rfl,
    apm_m99A01_functional_sub_extremal z hz]
  rw [← intervalIntegral.integral_const_mul]
  apply congrArg (fun r : ℝ ↦ apm_m99A01_functional apm_m99A01_extremal + r)
  apply intervalIntegral.integral_congr
  intro t ht
  have hyD := hy.1.differentiable (by norm_num) t
  have heD := he.1.differentiable (by norm_num) t
  have hsubD := hyD.sub heD
  have hzsub : (fun x ↦ z x - apm_m99A01_extremal x) =
      fun x ↦ (1 - s) * (y x - apm_m99A01_extremal x) := by
    funext x
    simp [z]
    ring
  rw [hzsub]
  have hdscale : deriv (fun x ↦ (1 - s) *
      (y x - apm_m99A01_extremal x)) t =
      (1 - s) * deriv (fun x ↦ y x - apm_m99A01_extremal x) t := by
    exact deriv_const_mul (1 - s) hsubD
  change deriv (fun x ↦ (1 - s) * (y x - apm_m99A01_extremal x)) t ^ 2 +
      (z t - apm_m99A01_extremal t) ^ 2 =
    (1 - s) ^ 2 * (deriv (fun x ↦ y x - apm_m99A01_extremal x) t ^ 2 +
      (y t - apm_m99A01_extremal t) ^ 2)
  rw [hdscale]
  simp [z]
  ring

lemma apm_m99A01_extremal_stationary :
    apm_m99A01_stationary apm_m99A01_extremal := by
  intro η hη hη0 hηpi
  have he : apm_m99A01_extremal ∈ apm_m99A01_admissible := by
    refine ⟨?_, by simp [apm_m99A01_extremal], ?_⟩
    · unfold apm_m99A01_extremal
      fun_prop
    · unfold apm_m99A01_extremal
      have hc : Real.cosh (Real.pi / 4) ≠ 0 := ne_of_gt (Real.cosh_pos _)
      rw [show Real.pi / 2 = 2 * (Real.pi / 4) by ring,
        Real.cosh_two_mul, Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
      field_simp [hc]
      nlinarith [Real.cosh_sq_sub_sinh_sq (Real.pi / 4)]
  let y := fun t ↦ apm_m99A01_extremal t + η t
  have hy : y ∈ apm_m99A01_admissible := by
    refine ⟨he.1.add hη, ?_, ?_⟩
    · simp [y, he.2.1, hη0]
    · simp [y, he.2.2, hηpi]
  let Q := ∫ t in (0 : ℝ)..(Real.pi / 2),
    deriv (fun x ↦ y x - apm_m99A01_extremal x) t ^ 2 +
      (y t - apm_m99A01_extremal t) ^ 2
  have hline : (fun s ↦ apm_m99A01_functional
      (fun t ↦ apm_m99A01_extremal t + s * η t)) =
      fun s ↦ apm_m99A01_functional apm_m99A01_extremal + s ^ 2 * Q := by
    funext s
    have h := apm_m99A01_line_to_extremal y hy (1 - s)
    calc
      apm_m99A01_functional (fun t ↦ apm_m99A01_extremal t + s * η t) =
          apm_m99A01_functional
            (fun t ↦ y t + (1 - s) * (apm_m99A01_extremal t - y t)) := by
              congr 1
              funext t
              simp [y]
              ring
      _ = apm_m99A01_functional apm_m99A01_extremal + (1 - (1 - s)) ^ 2 * Q := h
      _ = apm_m99A01_functional apm_m99A01_extremal + s ^ 2 * Q := by ring
  rw [hline]
  simpa [id] using ((((hasDerivAt_id (x := (0 : ℝ))).pow 2).mul_const Q).const_add
    (apm_m99A01_functional apm_m99A01_extremal))

noncomputable def apm_m99A01_counterBump : ContDiffBump (-2 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

lemma apm_m99A01_counterBump_at_center : apm_m99A01_counterBump (-2) = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  simp [apm_m99A01_counterBump]

lemma apm_m99A01_counterBump_notMem_tsupport {x : ℝ} (hx : 0 ≤ x) :
    x ∉ tsupport apm_m99A01_counterBump := by
  rw [ContDiffBump.tsupport_eq]
  simp only [Metric.mem_closedBall, not_le]
  change (1 / 2 : ℝ) < dist x (-2)
  rw [Real.dist_eq]
  have : 0 ≤ x + 2 := by linarith
  rw [show x - -2 = x + 2 by ring, abs_of_nonneg this]
  linarith

lemma apm_m99A01_counterBump_hasDerivAt_zero {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt apm_m99A01_counterBump 0 x := by
  apply HasDerivAt.of_notMem_tsupport
  exact apm_m99A01_counterBump_notMem_tsupport hx

lemma apm_m99A01_counterBump_zero {x : ℝ} (hx : 0 ≤ x) :
    apm_m99A01_counterBump x = 0 := by
  exact image_eq_zero_of_notMem_tsupport (apm_m99A01_counterBump_notMem_tsupport hx)

/-! ## Remaining classification bridges -/

theorem apm_m99A01_stationary_residual_zero
    (y : ℝ → ℝ) (hy2 : ContDiff ℝ 2 y) (hyadm : y ∈ apm_m99A01_admissible)
    (hystat : apm_m99A01_stationary y) :
    ∀ t ∈ Set.Ioo 0 (Real.pi / 2), apm_m99A01_residual y t = 0 := by
  have hy1 : ContDiff ℝ 1 y := hy2.of_le (by norm_num)
  have hyd1 : ContDiff ℝ 1 (deriv y) := hy2.deriv'
  have hfirst : ∀ η : ℝ → ℝ, ContDiff ℝ 1 η → η 0 = 0 →
      η (Real.pi / 2) = 0 →
      ∫ t in (0 : ℝ)..(Real.pi / 2),
        deriv y t * deriv η t + (y t + 1) * η t = 0 := by
    intro η hη hη0 hηpi
    let A := ∫ t in (0 : ℝ)..(Real.pi / 2),
      deriv y t * deriv η t + (y t + 1) * η t
    let B := ∫ t in (0 : ℝ)..(Real.pi / 2),
      (deriv η t) ^ 2 + (η t) ^ 2
    have hdη : ContDiff ℝ 0 (deriv η) := hη.deriv'
    have hbase : IntervalIntegrable
        (fun t ↦ deriv y t ^ 2 + y t ^ 2 + 2 * y t)
        MeasureTheory.volume 0 (Real.pi / 2) :=
      (((hyd1.continuous.pow 2).add (hy1.continuous.pow 2)).add
        (continuous_const.mul hy1.continuous)).intervalIntegrable _ _
    have hcross : IntervalIntegrable
        (fun t ↦ deriv y t * deriv η t + (y t + 1) * η t)
        MeasureTheory.volume 0 (Real.pi / 2) :=
      ((hyd1.continuous.mul hdη.continuous).add
        ((hy1.continuous.add continuous_const).mul hη.continuous)).intervalIntegrable _ _
    have hsquare : IntervalIntegrable
        (fun t ↦ deriv η t ^ 2 + η t ^ 2)
        MeasureTheory.volume 0 (Real.pi / 2) :=
      ((hdη.continuous.pow 2).add (hη.continuous.pow 2)).intervalIntegrable _ _
    have hline : (fun s ↦ apm_m99A01_functional (fun t ↦ y t + s * η t)) =
        fun s ↦ apm_m99A01_functional y + 2 * s * A + s ^ 2 * B := by
      funext s
      have hp : (fun t ↦
          deriv (fun x ↦ y x + s * η x) t ^ 2 +
            (y t + s * η t) ^ 2 + 2 * (y t + s * η t)) =
          fun t ↦ (deriv y t ^ 2 + y t ^ 2 + 2 * y t) +
            (2 * s) * (deriv y t * deriv η t + (y t + 1) * η t) +
            s ^ 2 * ((deriv η t) ^ 2 + (η t) ^ 2) := by
        funext t
        have hsder : deriv (fun x ↦ s * η x) t = s * deriv η t :=
          deriv_const_mul s (hη.differentiable (by norm_num) t)
        have hd : deriv (fun x ↦ y x + s * η x) t =
            deriv y t + s * deriv η t := by
          change deriv (y + fun x ↦ s * η x) t = _
          rw [deriv_add (hy1.differentiable (by norm_num) t)
            ((hη.differentiable (by norm_num) t).const_mul s), hsder]
        rw [hd]
        ring
      unfold apm_m99A01_functional
      rw [hp, intervalIntegral.integral_add (hbase.add (hcross.const_mul (2 * s)))
        (hsquare.const_mul (s ^ 2)),
        intervalIntegral.integral_add hbase (hcross.const_mul (2 * s)),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    have hs := hystat η hη hη0 hηpi
    rw [hline] at hs
    have hp : HasDerivAt
        (fun s : ℝ ↦ apm_m99A01_functional y + 2 * s * A + s ^ 2 * B)
        (2 * A) 0 := by
      convert (((hasDerivAt_const (0 : ℝ) (apm_m99A01_functional y)).add
        ((hasDerivAt_id (x := (0 : ℝ))).const_mul 2 |>.mul_const A)).add
        (((hasDerivAt_id (x := (0 : ℝ))).pow 2).mul_const B)) using 1 <;>
        norm_num [id] <;> ring
    have : (2 : ℝ) * A = 0 := hp.unique hs
    simpa [A] using (mul_eq_zero.mp this).resolve_left (by norm_num)
  have hloc : MeasureTheory.LocallyIntegrableOn
      (apm_m99A01_residual y) (Ioo 0 (Real.pi / 2)) MeasureTheory.volume := by
    have hc : Continuous (apm_m99A01_residual y) := by
      unfold apm_m99A01_residual
      exact (hyd1.continuous_deriv (by norm_num) |>.sub hy1.continuous).sub continuous_const
    exact (hc.locallyIntegrable (μ := MeasureTheory.volume)).locallyIntegrableOn _
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun g hg hgc hgs ↦ by
      have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
      have hg0 : g 0 = 0 := by
        by_contra hn
        have hm : 0 ∈ tsupport g := subset_tsupport _ hn
        exact (hgs hm).1.false
      have hgb : g (Real.pi / 2) = 0 := by
        by_contra hn
        have hm : Real.pi / 2 ∈ tsupport g := subset_tsupport _ hn
        exact (hgs hm).2.false
      have hzero := hfirst g hg1 hg0 hgb
      have hydd : ∀ x ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
          HasDerivAt (deriv y) (deriv (deriv y) x) x := by
        intro x hx
        exact (hyd1.differentiable (by norm_num) x).hasDerivAt
      have hgd : ∀ x ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
          HasDerivAt g (deriv g x) x := by
        intro x hx
        exact (hg1.differentiable (by norm_num) x).hasDerivAt
      have hyddint : IntervalIntegrable (deriv (deriv y)) MeasureTheory.volume
          0 (Real.pi / 2) :=
        (hyd1.continuous_deriv (by norm_num)).intervalIntegrable _ _
      have hgdint : IntervalIntegrable (deriv g) MeasureTheory.volume
          0 (Real.pi / 2) :=
        (hg1.continuous_deriv (by norm_num)).intervalIntegrable _ _
      have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
        hydd hgd hyddint hgdint
      rw [hg0, hgb] at hibp
      simp only [mul_zero, sub_self] at hibp
      have hi : ∫ t in (0 : ℝ)..(Real.pi / 2),
          g t * apm_m99A01_residual y t = 0 := by
        unfold apm_m99A01_residual
        have hcongr : (fun t ↦ g t * (deriv (deriv y) t - y t - 1)) =
            fun t ↦ deriv (deriv y) t * g t - (y t + 1) * g t := by
          funext t
          ring
        have hleft : IntervalIntegrable (fun t ↦ deriv (deriv y) t * g t)
            MeasureTheory.volume 0 (Real.pi / 2) :=
          ((hyd1.continuous_deriv (by norm_num)).mul hg.continuous).intervalIntegrable _ _
        have hright : IntervalIntegrable (fun t ↦ (y t + 1) * g t)
            MeasureTheory.volume 0 (Real.pi / 2) :=
          ((hy1.continuous.add continuous_const).mul hg.continuous).intervalIntegrable _ _
        have hcross : IntervalIntegrable (fun t ↦ deriv y t * deriv g t)
            MeasureTheory.volume 0 (Real.pi / 2) :=
          (hyd1.continuous.mul (hg1.continuous_deriv (by norm_num))).intervalIntegrable _ _
        rw [intervalIntegral.integral_add hcross hright] at hzero
        rw [hcongr, intervalIntegral.integral_sub hleft hright]
        linarith
      rw [← intervalIntegral.integral_eq_integral_of_support_subset
        (a := (0 : ℝ)) (b := Real.pi / 2)]
      · simpa [smul_eq_mul] using hi
      · intro x hx
        have hgx : g x ≠ 0 := by
          intro hz
          exact hx (by simp [hz])
        exact ⟨(hgs (subset_tsupport g hgx)).1,
          (hgs (subset_tsupport g hgx)).2.le⟩)
  apply apm_m99A01_eq_zero_on_Ioo_of_ae (apm_m99A01_residual y)
  · unfold apm_m99A01_residual
    exact (((hyd1.continuous_deriv (by norm_num)).sub hy1.continuous).sub
      continuous_const).continuousOn
  · exact hae

-- BEGIN SEAT AREA
theorem apm_m99A01_eqOn_extremal_of_residual_zero
    (y : ℝ → ℝ) (hy2 : ContDiff ℝ 2 y) (hyadm : y ∈ apm_m99A01_admissible)
    (hres : ∀ t ∈ Set.Ioo 0 (Real.pi / 2), apm_m99A01_residual y t = 0) :
    Set.EqOn y apm_m99A01_extremal (Set.Icc 0 (Real.pi / 2)) := by
  sorry
-- END SEAT AREA

theorem apm_m99A01_stationary_of_eqOn_extremal
    (y : ℝ → ℝ) (hy2 : ContDiff ℝ 2 y) (hyadm : y ∈ apm_m99A01_admissible)
    (heq : Set.EqOn y apm_m99A01_extremal (Set.Icc 0 (Real.pi / 2))) :
    apm_m99A01_stationary y := by
  sorry

theorem apm_m99a01 :
    (∀ y : ℝ → ℝ, ContDiff ℝ 2 y → y ∈ apm_m99A01_admissible →
      (apm_m99A01_stationary y ↔
        Set.EqOn y apm_m99A01_extremal (Set.Icc 0 (Real.pi / 2)))) ∧
    apm_m99A01_extremal ∈ apm_m99A01_admissible ∧
    (∀ y ∈ apm_m99A01_admissible,
      apm_m99A01_functional apm_m99A01_extremal ≤ apm_m99A01_functional y) ∧
    ¬ ∃ y ∈ apm_m99A01_admissible, ∀ z ∈ apm_m99A01_admissible,
      apm_m99A01_functional z ≤ apm_m99A01_functional y := by
  constructor
  · intro y hy2 hyadm
    constructor
    · intro hystat
      exact apm_m99A01_eqOn_extremal_of_residual_zero y hy2 hyadm
        (apm_m99A01_stationary_residual_zero y hy2 hyadm hystat)
    · exact apm_m99A01_stationary_of_eqOn_extremal y hy2 hyadm
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · unfold apm_m99A01_extremal
      fun_prop
    · simp [apm_m99A01_extremal]
    · unfold apm_m99A01_extremal
      have hc : Real.cosh (Real.pi / 4) ≠ 0 :=
        ne_of_gt (Real.cosh_pos (Real.pi / 4))
      rw [show Real.pi / 2 = 2 * (Real.pi / 4) by ring,
        Real.cosh_two_mul, Real.sinh_two_mul,
        Real.tanh_eq_sinh_div_cosh]
      field_simp [hc]
      nlinarith [Real.cosh_sq_sub_sinh_sq (Real.pi / 4)]
  ·
    constructor
    · intro y hy
      rw [apm_m99A01_functional_sub_extremal y hy]
      have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..(Real.pi / 2),
          deriv (fun x ↦ y x - apm_m99A01_extremal x) t ^ 2 +
            (y t - apm_m99A01_extremal t) ^ 2 := by
        apply intervalIntegral.integral_nonneg (by positivity)
        intro t ht
        positivity
      linarith
    · exact apm_m99A01_no_maximum

#print axioms apm_m99a01
