import Mathlib

/-!
# APM m02A05 — a coupled variational problem

## Statement repairs

2026 repair (guide, attempt 1, obligation
d6fd972b4c8b2dd896da1fde27e5ddb5536d78914a38729d0de77935beacb6e6,
frame f203): the first conjunct originally concluded the global function
equalities `x = apm_m02a05_extremal` and `y = apm_m02a05_extremal`, which is
refuted by adding a smooth bump supported outside `[0, π/2]`. The conclusion
is now `Set.EqOn` on `Icc 0 (π/2)`, the interval on which the boundary
conditions, the ODE, and the functional constrain the pair. The second and
third conjuncts are unchanged. No logical problem-id change.
-/

open Set MeasureTheory

def apm_m02a05_admissible (x y : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 x ∧ ContDiff ℝ 2 y ∧
  x 0 = 0 ∧ y 0 = 0 ∧ x (Real.pi / 2) = 1 ∧ y (Real.pi / 2) = 1

noncomputable def apm_m02a05_J (x y : ℝ → ℝ) : ℝ :=
  ∫ t in Icc 0 (Real.pi / 2),
    (deriv x t) ^ 2 + (deriv y t) ^ 2 + 2 * x t * y t

noncomputable def apm_m02a05_extremal (t : ℝ) : ℝ :=
  Real.sinh t / Real.sinh (Real.pi / 2)

lemma apm_m02a05_extremal_admissible :
    apm_m02a05_admissible apm_m02a05_extremal apm_m02a05_extremal := by
  have hpi : 0 < Real.pi / 2 := by positivity
  have hsinh : Real.sinh (Real.pi / 2) ≠ 0 := ne_of_gt (Real.sinh_pos_iff.2 hpi)
  have hsmooth : ContDiff ℝ 2 apm_m02a05_extremal := by
    simpa [apm_m02a05_extremal] using
      (Real.contDiff_sinh.div_const (Real.sinh (Real.pi / 2)))
  refine ⟨hsmooth, hsmooth, ?_, ?_, ?_, ?_⟩
  · simp [apm_m02a05_extremal]
  · simp [apm_m02a05_extremal]
  · simp [apm_m02a05_extremal, hsinh]
  · simp [apm_m02a05_extremal, hsinh]

lemma apm_m02a05_deriv_extremal (t : ℝ) :
    deriv apm_m02a05_extremal t =
      Real.cosh t / Real.sinh (Real.pi / 2) := by
  change deriv (fun x : ℝ => Real.sinh x / Real.sinh (Real.pi / 2)) t = _
  exact ((Real.hasDerivAt_sinh t).div_const (Real.sinh (Real.pi / 2))).deriv

lemma apm_m02a05_second_deriv_extremal (t : ℝ) :
    deriv (deriv apm_m02a05_extremal) t = apm_m02a05_extremal t := by
  rw [funext apm_m02a05_deriv_extremal]
  simpa [apm_m02a05_extremal] using
    (Real.hasDerivAt_cosh t).div_const (Real.sinh (Real.pi / 2)) |>.deriv

lemma apm_m02a05_extremal_solves_ode :
    ∀ t ∈ Ioo 0 (Real.pi / 2),
      deriv (deriv apm_m02a05_extremal) t = apm_m02a05_extremal t ∧
      deriv (deriv apm_m02a05_extremal) t = apm_m02a05_extremal t := by
  intro t _
  exact ⟨apm_m02a05_second_deriv_extremal t,
    apm_m02a05_second_deriv_extremal t⟩

noncomputable def apm_m02a05_trialX (A t : ℝ) : ℝ :=
  2 * t / Real.pi + A * Real.sin (2 * t)

noncomputable def apm_m02a05_trialY (A t : ℝ) : ℝ :=
  2 * t / Real.pi - A * Real.sin (2 * t)

lemma apm_m02a05_trial_admissible (A : ℝ) :
    apm_m02a05_admissible (apm_m02a05_trialX A) (apm_m02a05_trialY A) := by
  have hx : ContDiff ℝ 2 (apm_m02a05_trialX A) := by
    unfold apm_m02a05_trialX
    fun_prop
  have hy : ContDiff ℝ 2 (apm_m02a05_trialY A) := by
    unfold apm_m02a05_trialY
    fun_prop
  refine ⟨hx, hy, ?_, ?_, ?_, ?_⟩
  · simp [apm_m02a05_trialX]
  · simp [apm_m02a05_trialY]
  · rw [apm_m02a05_trialX, show 2 * (Real.pi / 2) = Real.pi by ring,
      Real.sin_pi]
    field_simp
    simp
  · rw [apm_m02a05_trialY, show 2 * (Real.pi / 2) = Real.pi by ring,
      Real.sin_pi]
    field_simp
    simp

lemma apm_m02a05_deriv_trialX (A t : ℝ) :
    deriv (apm_m02a05_trialX A) t =
      2 / Real.pi + 2 * A * Real.cos (2 * t) := by
  have hlin := ((hasDerivAt_id t).const_mul 2).div_const Real.pi
  have harg := (hasDerivAt_id t).const_mul 2
  have hsin := ((Real.hasDerivAt_sin (2 * t)).comp t harg).const_mul A
  change deriv (fun u : ℝ => 2 * u / Real.pi + A * Real.sin (2 * u)) t = _
  convert (hlin.add hsin).deriv using 1 <;> ring

lemma apm_m02a05_deriv_trialY (A t : ℝ) :
    deriv (apm_m02a05_trialY A) t =
      2 / Real.pi - 2 * A * Real.cos (2 * t) := by
  have hlin := ((hasDerivAt_id t).const_mul 2).div_const Real.pi
  have harg := (hasDerivAt_id t).const_mul 2
  have hsin := ((Real.hasDerivAt_sin (2 * t)).comp t harg).const_mul A
  change deriv (fun u : ℝ => 2 * u / Real.pi - A * Real.sin (2 * u)) t = _
  convert (hlin.sub hsin).deriv using 1 <;> ring

lemma apm_m02a05_trial_density (A t : ℝ) :
    (deriv (apm_m02a05_trialX A) t) ^ 2 +
        (deriv (apm_m02a05_trialY A) t) ^ 2 +
        2 * apm_m02a05_trialX A t * apm_m02a05_trialY A t =
      8 / Real.pi ^ 2 + 8 * t ^ 2 / Real.pi ^ 2 +
        A ^ 2 * (8 * Real.cos (2 * t) ^ 2 - 2 * Real.sin (2 * t) ^ 2) := by
  rw [apm_m02a05_deriv_trialX, apm_m02a05_deriv_trialY]
  simp only [apm_m02a05_trialX, apm_m02a05_trialY]
  field_simp [Real.pi_ne_zero]
  ring

lemma apm_m02a05_integral_cos_two_sq :
    (∫ t in (0 : ℝ)..Real.pi / 2, Real.cos (2 * t) ^ 2) = Real.pi / 4 := by
  have h := intervalIntegral.mul_integral_comp_mul_left
    (f := fun u : ℝ => Real.cos u ^ 2) 2 (a := 0) (b := Real.pi / 2)
  rw [integral_cos_sq] at h
  ring_nf at h
  simp at h
  have heq : 2 * (∫ t in (0 : ℝ)..Real.pi / 2, Real.cos (2 * t) ^ 2) =
      Real.pi / 2 := by
    convert h using 1 <;> ring
  linarith

lemma apm_m02a05_integral_sin_two_sq :
    (∫ t in (0 : ℝ)..Real.pi / 2, Real.sin (2 * t) ^ 2) = Real.pi / 4 := by
  have h := intervalIntegral.mul_integral_comp_mul_left
    (f := fun u : ℝ => Real.sin u ^ 2) 2 (a := 0) (b := Real.pi / 2)
  rw [integral_sin_sq] at h
  ring_nf at h
  simp at h
  have heq : 2 * (∫ t in (0 : ℝ)..Real.pi / 2, Real.sin (2 * t) ^ 2) =
      Real.pi / 2 := by
    convert h using 1 <;> ring
  linarith

lemma apm_m02a05_integral_sq :
    (∫ t in (0 : ℝ)..Real.pi / 2, t ^ 2) = Real.pi ^ 3 / 24 := by
  rw [integral_pow]
  ring

lemma apm_m02a05_trial_J (A : ℝ) :
    apm_m02a05_J (apm_m02a05_trialX A) (apm_m02a05_trialY A) =
      4 / Real.pi + Real.pi / 3 + (3 * Real.pi / 2) * A ^ 2 := by
  rw [apm_m02a05_J]
  simp_rw [apm_m02a05_trial_density]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add]
  · have hconst : (∫ _t in (0 : ℝ)..Real.pi / 2, 8 / Real.pi ^ 2) =
        4 / Real.pi := by
      simp [Real.pi_ne_zero]
      field_simp [Real.pi_ne_zero]
      ring
    have hsq : (∫ t in (0 : ℝ)..Real.pi / 2, 8 * t ^ 2 / Real.pi ^ 2) =
        Real.pi / 3 := by
      calc
        _ = (∫ t in (0 : ℝ)..Real.pi / 2, (8 / Real.pi ^ 2) * t ^ 2) := by
          apply intervalIntegral.integral_congr
          intro t _
          ring
        _ = (8 / Real.pi ^ 2) * (∫ t in (0 : ℝ)..Real.pi / 2, t ^ 2) := by
          rw [intervalIntegral.integral_const_mul]
        _ = Real.pi / 3 := by
          rw [apm_m02a05_integral_sq]
          field_simp [Real.pi_ne_zero]
          ring
    have htrig : (∫ t in (0 : ℝ)..Real.pi / 2,
        A ^ 2 * (8 * Real.cos (2 * t) ^ 2 - 2 * Real.sin (2 * t) ^ 2)) =
        (3 * Real.pi / 2) * A ^ 2 := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        apm_m02a05_integral_cos_two_sq, apm_m02a05_integral_sin_two_sq]
      ring
      all_goals apply Continuous.intervalIntegrable <;> fun_prop
    rw [hconst, hsq, htrig]
  all_goals apply Continuous.intervalIntegrable <;> fun_prop

lemma apm_m02a05_unbounded_above :
    ∀ B : ℝ, ∃ x y : ℝ → ℝ,
      apm_m02a05_admissible x y ∧ B < apm_m02a05_J x y := by
  intro B
  let A : ℝ := |B| + 1
  refine ⟨apm_m02a05_trialX A, apm_m02a05_trialY A,
    apm_m02a05_trial_admissible A, ?_⟩
  rw [apm_m02a05_trial_J]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hc : 1 < 3 * Real.pi / 2 := by
    have := Real.pi_gt_three
    nlinarith
  have hA : 0 < A := by
    dsimp [A]
    exact add_pos_of_nonneg_of_pos (abs_nonneg B) zero_lt_one
  have hBA : B < A ^ 2 := by
    have habs : B ≤ |B| := le_abs_self B
    have habs0 : 0 ≤ |B| := abs_nonneg B
    dsimp [A]
    nlinarith
  have hbase : 0 < 4 / Real.pi + Real.pi / 3 := by positivity
  nlinarith [sq_pos_of_pos hA]

lemma apm_m02a05_characterization_reverse (x y : ℝ → ℝ)
    (hEq : Set.EqOn x apm_m02a05_extremal (Icc 0 (Real.pi / 2)) ∧
      Set.EqOn y apm_m02a05_extremal (Icc 0 (Real.pi / 2))) :
    ∀ t ∈ Ioo 0 (Real.pi / 2),
      deriv (deriv x) t = y t ∧ deriv (deriv y) t = x t := by
  rintro t ht
  have hxt : x =ᶠ[nhds t] apm_m02a05_extremal := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hEq.1 (Ioo_subset_Icc_self hs)
  have hyt : y =ᶠ[nhds t] apm_m02a05_extremal := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hEq.2 (Ioo_subset_Icc_self hs)
  have hxt' : deriv (deriv x) t = deriv (deriv apm_m02a05_extremal) t :=
    hxt.deriv.deriv_eq
  have hyt' : deriv (deriv y) t = deriv (deriv apm_m02a05_extremal) t :=
    hyt.deriv.deriv_eq
  constructor
  · calc
      deriv (deriv x) t = deriv (deriv apm_m02a05_extremal) t := hxt'
      _ = apm_m02a05_extremal t := apm_m02a05_second_deriv_extremal t
      _ = y t := (hEq.2 (Ioo_subset_Icc_self ht)).symm
  · calc
      deriv (deriv y) t = deriv (deriv apm_m02a05_extremal) t := hyt'
      _ = apm_m02a05_extremal t := apm_m02a05_second_deriv_extremal t
      _ = x t := (hEq.1 (Ioo_subset_Icc_self ht)).symm

lemma apm_m02a05_diagonal_odes (x y : ℝ → ℝ)
    (hx : ContDiff ℝ 2 x) (hy : ContDiff ℝ 2 y)
    (hode : ∀ t ∈ Ioo 0 (Real.pi / 2),
      deriv (deriv x) t = y t ∧ deriv (deriv y) t = x t) :
    (∀ t ∈ Ioo 0 (Real.pi / 2),
      deriv (deriv (fun s => x s + y s)) t = x t + y t) ∧
    (∀ t ∈ Ioo 0 (Real.pi / 2),
      deriv (deriv (fun s => x s - y s)) t = -(x t - y t)) := by
  have hdx : Differentiable ℝ x := hx.differentiable (by norm_num)
  have hdy : Differentiable ℝ y := hy.differentiable (by norm_num)
  have hddx : Differentiable ℝ (deriv x) := hx.differentiable_deriv_two
  have hddy : Differentiable ℝ (deriv y) := hy.differentiable_deriv_two
  constructor
  · intro t ht
    change deriv (deriv (x + y)) t = _
    have hadd : deriv (x + y) = deriv x + deriv y := by
      funext s
      exact deriv_add hdx.differentiableAt hdy.differentiableAt
    rw [hadd, deriv_add hddx.differentiableAt hddy.differentiableAt]
    rcases hode t ht with ⟨hxy, hyx⟩
    rw [hxy, hyx]
    ring
  · intro t ht
    change deriv (deriv (x - y)) t = _
    have hsub : deriv (x - y) = deriv x - deriv y := by
      funext s
      exact deriv_sub hdx.differentiableAt hdy.differentiableAt
    rw [hsub, deriv_sub hddx.differentiableAt hddy.differentiableAt]
    rcases hode t ht with ⟨hxy, hyx⟩
    rw [hxy, hyx]
    ring

lemma apm_m02a05_diagonal_boundary (x y : ℝ → ℝ)
    (h : apm_m02a05_admissible x y) :
    (x 0 + y 0 = 0 ∧ x (Real.pi / 2) + y (Real.pi / 2) = 2) ∧
    (x 0 - y 0 = 0 ∧ x (Real.pi / 2) - y (Real.pi / 2) = 0) := by
  rcases h with ⟨_, _, hx0, hy0, hx1, hy1⟩
  norm_num [hx0, hy0, hx1, hy1]

noncomputable def apm_m02a05_hyperbolicWronskian (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv u t * Real.sinh t - u t * Real.cosh t

noncomputable def apm_m02a05_trigWronskian (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv u t * Real.sin t - u t * Real.cos t

lemma apm_m02a05_hyperbolicWronskian_deriv_zero (u : ℝ → ℝ)
    (hu : ContDiff ℝ 2 u)
    (hode : ∀ t ∈ Ioo 0 (Real.pi / 2), deriv (deriv u) t = u t) :
    ∀ t ∈ Ioo 0 (Real.pi / 2),
      deriv (apm_m02a05_hyperbolicWronskian u) t = 0 := by
  intro t ht
  have hu1 : HasDerivAt u (deriv u t) t :=
    (hu.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hu2 : HasDerivAt (deriv u) (deriv (deriv u) t) t :=
    hu.differentiable_deriv_two.differentiableAt.hasDerivAt
  change deriv (fun s => deriv u s * Real.sinh s - u s * Real.cosh s) t = 0
  convert ((hu2.mul (Real.hasDerivAt_sinh t)).sub
    (hu1.mul (Real.hasDerivAt_cosh t))).deriv using 1
  rw [hode t ht]
  ring

lemma apm_m02a05_trigWronskian_deriv_zero (u : ℝ → ℝ)
    (hu : ContDiff ℝ 2 u)
    (hode : ∀ t ∈ Ioo 0 (Real.pi / 2), deriv (deriv u) t = -u t) :
    ∀ t ∈ Ioo 0 (Real.pi / 2),
      deriv (apm_m02a05_trigWronskian u) t = 0 := by
  intro t ht
  have hu1 : HasDerivAt u (deriv u t) t :=
    (hu.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hu2 : HasDerivAt (deriv u) (deriv (deriv u) t) t :=
    hu.differentiable_deriv_two.differentiableAt.hasDerivAt
  change deriv (fun s => deriv u s * Real.sin s - u s * Real.cos s) t = 0
  convert ((hu2.mul (Real.hasDerivAt_sin t)).sub
    (hu1.mul (Real.hasDerivAt_cos t))).deriv using 1
  rw [hode t ht]
  ring

lemma apm_m02a05_hyperbolicWronskian_const (u : ℝ → ℝ)
    (hu : ContDiff ℝ 2 u)
    (hode : ∀ t ∈ Ioo 0 (Real.pi / 2), deriv (deriv u) t = u t)
    {s t : ℝ} (hs : s ∈ Ioo 0 (Real.pi / 2)) (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    apm_m02a05_hyperbolicWronskian u s =
      apm_m02a05_hyperbolicWronskian u t := by
  apply isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
  · apply Differentiable.differentiableOn
    unfold apm_m02a05_hyperbolicWronskian
    exact (hu.differentiable_deriv_two.mul Real.differentiable_sinh).sub
      ((hu.differentiable (by norm_num)).mul Real.differentiable_cosh)
  · exact apm_m02a05_hyperbolicWronskian_deriv_zero u hu hode
  · exact hs
  · exact ht

lemma apm_m02a05_trigWronskian_const (u : ℝ → ℝ)
    (hu : ContDiff ℝ 2 u)
    (hode : ∀ t ∈ Ioo 0 (Real.pi / 2), deriv (deriv u) t = -u t)
    {s t : ℝ} (hs : s ∈ Ioo 0 (Real.pi / 2)) (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    apm_m02a05_trigWronskian u s = apm_m02a05_trigWronskian u t := by
  apply isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
  · apply Differentiable.differentiableOn
    unfold apm_m02a05_trigWronskian
    exact (hu.differentiable_deriv_two.mul Real.differentiable_sin).sub
      ((hu.differentiable (by norm_num)).mul Real.differentiable_cos)
  · exact apm_m02a05_trigWronskian_deriv_zero u hu hode
  · exact hs
  · exact ht

lemma apm_m02a05_hyperbolicWronskian_const_closed (u : ℝ → ℝ)
    (hu : ContDiff ℝ 2 u)
    (hode : ∀ t ∈ Ioo 0 (Real.pi / 2), deriv (deriv u) t = u t)
    {s t : ℝ} (hs : s ∈ Icc 0 (Real.pi / 2)) (ht : t ∈ Icc 0 (Real.pi / 2)) :
    apm_m02a05_hyperbolicWronskian u s = apm_m02a05_hyperbolicWronskian u t := by
  let c := apm_m02a05_hyperbolicWronskian u (Real.pi / 4)
  have hmid : Real.pi / 4 ∈ Ioo 0 (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have heq : Set.EqOn (apm_m02a05_hyperbolicWronskian u) (fun _ => c)
      (Ioo 0 (Real.pi / 2)) := by
    intro z hz
    exact apm_m02a05_hyperbolicWronskian_const u hu hode hz hmid
  have hcont : Continuous (apm_m02a05_hyperbolicWronskian u) := by
    unfold apm_m02a05_hyperbolicWronskian
    exact (hu.continuous_deriv (by norm_num)).mul Real.continuous_sinh |>.sub
      (hu.continuous.mul Real.continuous_cosh)
  have hclosed := heq.closure hcont continuous_const
  rw [closure_Ioo (ne_of_lt (by positivity : (0 : ℝ) < Real.pi / 2))] at hclosed
  exact (hclosed hs).trans (hclosed ht).symm

lemma apm_m02a05_trigWronskian_const_closed (u : ℝ → ℝ)
    (hu : ContDiff ℝ 2 u)
    (hode : ∀ t ∈ Ioo 0 (Real.pi / 2), deriv (deriv u) t = -u t)
    {s t : ℝ} (hs : s ∈ Icc 0 (Real.pi / 2)) (ht : t ∈ Icc 0 (Real.pi / 2)) :
    apm_m02a05_trigWronskian u s = apm_m02a05_trigWronskian u t := by
  let c := apm_m02a05_trigWronskian u (Real.pi / 4)
  have hmid : Real.pi / 4 ∈ Ioo 0 (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  have heq : Set.EqOn (apm_m02a05_trigWronskian u) (fun _ => c)
      (Ioo 0 (Real.pi / 2)) := by
    intro z hz
    exact apm_m02a05_trigWronskian_const u hu hode hz hmid
  have hcont : Continuous (apm_m02a05_trigWronskian u) := by
    unfold apm_m02a05_trigWronskian
    exact (hu.continuous_deriv (by norm_num)).mul Real.continuous_sin |>.sub
      (hu.continuous.mul Real.continuous_cos)
  have hclosed := heq.closure hcont continuous_const
  rw [closure_Ioo (ne_of_lt (by positivity : (0 : ℝ) < Real.pi / 2))] at hclosed
  exact (hclosed hs).trans (hclosed ht).symm

lemma apm_m02a05_hyperbolic_solution_form (u : ℝ → ℝ)
    (hu : ContDiff ℝ 2 u) (hu0 : u 0 = 0)
    (hode : ∀ t ∈ Ioo 0 (Real.pi / 2), deriv (deriv u) t = u t) :
    ∃ C : ℝ, Set.EqOn u (fun t => C * Real.sinh t) (Icc 0 (Real.pi / 2)) := by
  have hW : ∀ t ∈ Icc 0 (Real.pi / 2),
      apm_m02a05_hyperbolicWronskian u t = 0 := by
    intro t ht
    have hc := apm_m02a05_hyperbolicWronskian_const_closed u hu hode
      ht (left_mem_Icc.2 (by positivity : (0 : ℝ) ≤ Real.pi / 2))
    simpa [apm_m02a05_hyperbolicWronskian, hu0] using hc
  have hquot : ∀ t ∈ Ioo 0 (Real.pi / 2),
      deriv (fun s => u s / Real.sinh s) t = 0 := by
    intro t ht
    have hu1 : HasDerivAt u (deriv u t) t :=
      (hu.differentiable (by norm_num)).differentiableAt.hasDerivAt
    have hs : Real.sinh t ≠ 0 := Real.sinh_ne_zero.2 (ne_of_gt ht.1)
    rw [show deriv (fun s => u s / Real.sinh s) t =
        (deriv u t * Real.sinh t - u t * Real.cosh t) / Real.sinh t ^ 2 by
      convert (hu1.div (Real.hasDerivAt_sinh t) hs).deriv using 1 <;> ring]
    rw [show deriv u t * Real.sinh t - u t * Real.cosh t = 0 by
      simpa [apm_m02a05_hyperbolicWronskian] using hW t (Ioo_subset_Icc_self ht)]
    simp
  obtain ⟨C, hC⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    ((hu.differentiable (by norm_num)).differentiableOn.div
      Real.differentiable_sinh.differentiableOn
      (fun t ht => Real.sinh_ne_zero.2 (ne_of_gt ht.1))) hquot
  refine ⟨C, ?_⟩
  have hi : Set.EqOn u (fun t => C * Real.sinh t) (Ioo 0 (Real.pi / 2)) := by
    intro t ht
    have hs : Real.sinh t ≠ 0 := Real.sinh_ne_zero.2 (ne_of_gt ht.1)
    have := hC t ht
    exact (div_eq_iff hs).mp this
  have hc1 : Continuous u := hu.continuous
  have hc2 : Continuous (fun t => C * Real.sinh t) := continuous_const.mul Real.continuous_sinh
  have hclosed := hi.closure hc1 hc2
  rw [closure_Ioo (ne_of_lt (by positivity : (0 : ℝ) < Real.pi / 2))] at hclosed
  exact hclosed

lemma apm_m02a05_trig_solution_form (u : ℝ → ℝ)
    (hu : ContDiff ℝ 2 u) (hu0 : u 0 = 0)
    (hode : ∀ t ∈ Ioo 0 (Real.pi / 2), deriv (deriv u) t = -u t) :
    ∃ C : ℝ, Set.EqOn u (fun t => C * Real.sin t) (Icc 0 (Real.pi / 2)) := by
  have hW : ∀ t ∈ Icc 0 (Real.pi / 2), apm_m02a05_trigWronskian u t = 0 := by
    intro t ht
    have hc := apm_m02a05_trigWronskian_const_closed u hu hode
      ht (left_mem_Icc.2 (by positivity : (0 : ℝ) ≤ Real.pi / 2))
    simpa [apm_m02a05_trigWronskian, hu0] using hc
  have hsin : ∀ t ∈ Ioo 0 (Real.pi / 2), Real.sin t ≠ 0 := by
    intro t ht
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht.1 (ht.2.trans (by linarith [Real.pi_pos])))
  have hquot : ∀ t ∈ Ioo 0 (Real.pi / 2), deriv (fun s => u s / Real.sin s) t = 0 := by
    intro t ht
    have hu1 : HasDerivAt u (deriv u t) t :=
      (hu.differentiable (by norm_num)).differentiableAt.hasDerivAt
    rw [show deriv (fun s => u s / Real.sin s) t =
        (deriv u t * Real.sin t - u t * Real.cos t) / Real.sin t ^ 2 by
      convert (hu1.div (Real.hasDerivAt_sin t) (hsin t ht)).deriv using 1 <;> ring]
    rw [show deriv u t * Real.sin t - u t * Real.cos t = 0 by
      simpa [apm_m02a05_trigWronskian] using hW t (Ioo_subset_Icc_self ht)]
    simp
  obtain ⟨C, hC⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    ((hu.differentiable (by norm_num)).differentiableOn.div
      Real.differentiable_sin.differentiableOn hsin) hquot
  refine ⟨C, ?_⟩
  have hi : Set.EqOn u (fun t => C * Real.sin t) (Ioo 0 (Real.pi / 2)) := by
    intro t ht
    exact (div_eq_iff (hsin t ht)).mp (hC t ht)
  have hclosed := hi.closure hu.continuous (continuous_const.mul Real.continuous_sin)
  rw [closure_Ioo (ne_of_lt (by positivity : (0 : ℝ) < Real.pi / 2))] at hclosed
  exact hclosed

lemma apm_m02a05_characterization_forward (x y : ℝ → ℝ)
    (hadm : apm_m02a05_admissible x y)
    (hode : ∀ t ∈ Ioo 0 (Real.pi / 2),
      deriv (deriv x) t = y t ∧ deriv (deriv y) t = x t) :
    Set.EqOn x apm_m02a05_extremal (Icc 0 (Real.pi / 2)) ∧
      Set.EqOn y apm_m02a05_extremal (Icc 0 (Real.pi / 2)) := by
  rcases hadm with ⟨hx, hy, hx0, hy0, hx1, hy1⟩
  obtain ⟨hsumode, hdiffode⟩ := apm_m02a05_diagonal_odes x y hx hy hode
  have hsum0 : (fun t => x t + y t) 0 = 0 := by simp [hx0, hy0]
  have hdiff0 : (fun t => x t - y t) 0 = 0 := by simp [hx0, hy0]
  obtain ⟨C, hC⟩ := apm_m02a05_hyperbolic_solution_form
    (fun t => x t + y t) (hx.add hy) hsum0 hsumode
  obtain ⟨D, hD⟩ := apm_m02a05_trig_solution_form
    (fun t => x t - y t) (hx.sub hy) hdiff0 hdiffode
  have hright : Real.pi / 2 ∈ Icc 0 (Real.pi / 2) :=
    right_mem_Icc.2 (by positivity)
  have hCend := hC hright
  have hDend := hD hright
  simp only at hCend hDend
  rw [hx1, hy1] at hCend hDend
  norm_num at hCend
  norm_num [Real.sin_pi_div_two] at hDend
  have hsinh : Real.sinh (Real.pi / 2) ≠ 0 := by positivity
  have hDzero : D = 0 := by linarith
  constructor
  · intro t ht
    have hsum := hC ht
    have hdiff := hD ht
    simp only at hsum hdiff
    rw [hDzero, zero_mul] at hdiff
    have hsumext : x t + y t = 2 * apm_m02a05_extremal t := by
      rw [apm_m02a05_extremal]
      rw [hsum]
      field_simp [hsinh]
      calc
        _ = Real.sinh t * (C * Real.sinh (Real.pi / 2)) := by ring
        _ = Real.sinh t * 2 := by rw [← hCend]
    linarith
  · intro t ht
    have hsum := hC ht
    have hdiff := hD ht
    simp only at hsum hdiff
    rw [hDzero, zero_mul] at hdiff
    have hsumext : x t + y t = 2 * apm_m02a05_extremal t := by
      rw [apm_m02a05_extremal]
      rw [hsum]
      field_simp [hsinh]
      calc
        _ = Real.sinh t * (C * Real.sinh (Real.pi / 2)) := by ring
        _ = Real.sinh t * 2 := by rw [← hCend]
    linarith

lemma apm_m02a05_characterization (x y : ℝ → ℝ)
    (hadm : apm_m02a05_admissible x y) :
    ((∀ t ∈ Ioo 0 (Real.pi / 2),
        deriv (deriv x) t = y t ∧ deriv (deriv y) t = x t) ↔
      (Set.EqOn x apm_m02a05_extremal (Icc 0 (Real.pi / 2)) ∧
       Set.EqOn y apm_m02a05_extremal (Icc 0 (Real.pi / 2)))) := by
  constructor
  · exact apm_m02a05_characterization_forward x y hadm
  · exact apm_m02a05_characterization_reverse x y

/-! The minimality calculation is cleanest after translating by the extremal.
The following identity isolates both genuinely analytic inputs: cancellation of
the linear Euler--Lagrange term and positivity of the zero-boundary quadratic
form. -/

lemma apm_m02a05_density_translate (x y t : ℝ) (dx dy de : ℝ) :
    dx ^ 2 + dy ^ 2 + 2 * x * y =
      (de ^ 2 + de ^ 2 + 2 * t * t) +
      ((dx - de) ^ 2 + (dy - de) ^ 2 +
        2 * (x - t) * (y - t)) +
      2 * (de * ((dx - de) + (dy - de)) +
        t * ((x - t) + (y - t))) := by
  ring

lemma apm_m02a05_cross_term_zero (p : ℝ → ℝ)
    (hp : ContDiff ℝ 2 p) (hp0 : p 0 = 0)
    (hp1 : p (Real.pi / 2) = 0) :
    (∫ t in Icc 0 (Real.pi / 2),
      deriv apm_m02a05_extremal t * deriv p t +
        apm_m02a05_extremal t * p t) = 0 := by
  have he : ContDiff ℝ 2 apm_m02a05_extremal :=
    apm_m02a05_extremal_admissible.1
  have he' : Continuous (deriv apm_m02a05_extremal) :=
    he.continuous_deriv (by norm_num)
  have hp' : Continuous (deriv p) := hp.continuous_deriv (by norm_num)
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub
    (a := (0 : ℝ)) (b := Real.pi / 2)
    (u := deriv apm_m02a05_extremal) (v := p)
    (u' := apm_m02a05_extremal) (v' := deriv p)
    (fun t _ => by
      rw [funext apm_m02a05_deriv_extremal]
      simpa [apm_m02a05_extremal] using
        (Real.hasDerivAt_cosh t).div_const (Real.sinh (Real.pi / 2)))
    (fun t _ => (hp.differentiable (by norm_num)).differentiableAt.hasDerivAt)
    (apm_m02a05_extremal_admissible.1.continuous.intervalIntegrable 0 (Real.pi / 2))
    (hp'.intervalIntegrable 0 (Real.pi / 2))
  rw [hp0, hp1] at hparts
  simp only [mul_zero, sub_self] at hparts
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
  calc
    _ = (∫ t in (0 : ℝ)..Real.pi / 2,
        apm_m02a05_extremal t * p t +
          deriv apm_m02a05_extremal t * deriv p t) := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    _ = 0 := hparts

lemma apm_m02a05_cross_term_zero_of_admissible_left (x y : ℝ → ℝ)
    (hadm : apm_m02a05_admissible x y) :
    (∫ t in Icc 0 (Real.pi / 2),
      deriv apm_m02a05_extremal t *
          (deriv x t - deriv apm_m02a05_extremal t) +
        apm_m02a05_extremal t *
          (x t - apm_m02a05_extremal t)) = 0 := by
  rcases hadm with ⟨hx, _hy, hx0, _hy0, hx1, _hy1⟩
  let p := fun t => x t - apm_m02a05_extremal t
  have he := apm_m02a05_extremal_admissible.1
  have hp : ContDiff ℝ 2 p := hx.sub he
  have hp0 : p 0 = 0 := by simp [p, hx0, apm_m02a05_extremal]
  have hp1 : p (Real.pi / 2) = 0 := by
    simp [p, hx1, apm_m02a05_extremal]
  calc
    _ = (∫ t in Icc 0 (Real.pi / 2),
        deriv apm_m02a05_extremal t * deriv p t +
          apm_m02a05_extremal t * p t) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro t _
      change deriv apm_m02a05_extremal t *
            (deriv x t - deriv apm_m02a05_extremal t) +
          apm_m02a05_extremal t * (x t - apm_m02a05_extremal t) =
        deriv apm_m02a05_extremal t * deriv p t +
          apm_m02a05_extremal t * p t
      rw [show deriv p t = deriv x t - deriv apm_m02a05_extremal t by
        exact deriv_sub (hx.differentiable (by norm_num)).differentiableAt
          (he.differentiable (by norm_num)).differentiableAt]
    _ = 0 := apm_m02a05_cross_term_zero p hp hp0 hp1

lemma apm_m02a05_cross_term_zero_of_admissible_right (x y : ℝ → ℝ)
    (hadm : apm_m02a05_admissible x y) :
    (∫ t in Icc 0 (Real.pi / 2),
      deriv apm_m02a05_extremal t *
          (deriv y t - deriv apm_m02a05_extremal t) +
        apm_m02a05_extremal t *
          (y t - apm_m02a05_extremal t)) = 0 := by
  simpa [add_comm] using
    apm_m02a05_cross_term_zero_of_admissible_left y x
      ⟨hadm.2.1, hadm.1, hadm.2.2.2.1, hadm.2.2.1,
        hadm.2.2.2.2.2, hadm.2.2.2.2.1⟩

lemma apm_m02a05_energy_expansion (x y : ℝ → ℝ)
    (hadm : apm_m02a05_admissible x y) :
    apm_m02a05_J x y =
      apm_m02a05_J apm_m02a05_extremal apm_m02a05_extremal +
      (∫ t in Icc 0 (Real.pi / 2),
        (deriv x t - deriv apm_m02a05_extremal t) ^ 2 +
        (deriv y t - deriv apm_m02a05_extremal t) ^ 2 +
        2 * (x t - apm_m02a05_extremal t) *
          (y t - apm_m02a05_extremal t)) := by
  let base := fun t =>
    deriv apm_m02a05_extremal t ^ 2 +
    deriv apm_m02a05_extremal t ^ 2 +
    2 * apm_m02a05_extremal t * apm_m02a05_extremal t
  let quad := fun t =>
    (deriv x t - deriv apm_m02a05_extremal t) ^ 2 +
    (deriv y t - deriv apm_m02a05_extremal t) ^ 2 +
    2 * (x t - apm_m02a05_extremal t) *
      (y t - apm_m02a05_extremal t)
  let crossx := fun t =>
    deriv apm_m02a05_extremal t *
        (deriv x t - deriv apm_m02a05_extremal t) +
      apm_m02a05_extremal t * (x t - apm_m02a05_extremal t)
  let crossy := fun t =>
    deriv apm_m02a05_extremal t *
        (deriv y t - deriv apm_m02a05_extremal t) +
      apm_m02a05_extremal t * (y t - apm_m02a05_extremal t)
  have hx := hadm.1
  have hy := hadm.2.1
  have he := apm_m02a05_extremal_admissible.1
  have hdx : Continuous (deriv x) := hx.continuous_deriv (by norm_num)
  have hdy : Continuous (deriv y) := hy.continuous_deriv (by norm_num)
  have hde : Continuous (deriv apm_m02a05_extremal) :=
    he.continuous_deriv (by norm_num)
  have hbase : Continuous base := by dsimp [base]; fun_prop
  have hquad : Continuous quad := by dsimp [quad]; fun_prop
  have hcrossx : Continuous crossx := by dsimp [crossx]; fun_prop
  have hcrossy : Continuous crossy := by dsimp [crossy]; fun_prop
  have ibase : MeasureTheory.IntegrableOn base (Icc 0 (Real.pi / 2)) :=
    hbase.integrableOn_Icc
  have iquad : MeasureTheory.IntegrableOn quad (Icc 0 (Real.pi / 2)) :=
    hquad.integrableOn_Icc
  have icrossx : MeasureTheory.IntegrableOn crossx (Icc 0 (Real.pi / 2)) :=
    hcrossx.integrableOn_Icc
  have icrossy : MeasureTheory.IntegrableOn crossy (Icc 0 (Real.pi / 2)) :=
    hcrossy.integrableOn_Icc
  unfold apm_m02a05_J
  calc
    _ = (∫ t in Icc 0 (Real.pi / 2),
        base t + quad t + 2 * (crossx t + crossy t)) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro t _
      dsimp [base, quad, crossx, crossy]
      ring
    _ = (∫ t in Icc 0 (Real.pi / 2), base t) +
        (∫ t in Icc 0 (Real.pi / 2), quad t) +
        2 * ((∫ t in Icc 0 (Real.pi / 2), crossx t) +
          (∫ t in Icc 0 (Real.pi / 2), crossy t)) := by
      calc
        _ = (∫ t in Icc 0 (Real.pi / 2), base t + quad t) +
            (∫ t in Icc 0 (Real.pi / 2), 2 * (crossx t + crossy t)) :=
          MeasureTheory.integral_add (ibase.add iquad)
            ((icrossx.add icrossy).const_mul 2)
        _ = _ := by
          rw [MeasureTheory.integral_add ibase iquad,
            MeasureTheory.integral_const_mul,
            MeasureTheory.integral_add icrossx icrossy]
    _ = (∫ t in Icc 0 (Real.pi / 2), base t) +
        (∫ t in Icc 0 (Real.pi / 2), quad t) := by
      rw [show (∫ t in Icc 0 (Real.pi / 2), crossx t) = 0 by
        simpa [crossx] using apm_m02a05_cross_term_zero_of_admissible_left x y hadm]
      rw [show (∫ t in Icc 0 (Real.pi / 2), crossy t) = 0 by
        simpa [crossy] using apm_m02a05_cross_term_zero_of_admissible_right x y hadm]
      ring
    _ = _ := by rfl

lemma apm_m02a05_quadratic_diagonal (p q dp dq : ℝ) :
    dp ^ 2 + dq ^ 2 + 2 * p * q =
      ((dp + dq) ^ 2 + (p + q) ^ 2) / 2 +
      ((dp - dq) ^ 2 - (p - q) ^ 2) / 2 := by
  ring

lemma apm_m02a05_sum_mode_integral_nonneg
    (p q dp dq : ℝ → ℝ) :
    0 ≤ (∫ t in Icc 0 (Real.pi / 2),
      (dp t + dq t) ^ 2 + (p t + q t) ^ 2) := by
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards with t
  positivity

lemma apm_m02a05_quadratic_integral_diagonal
    (p q dp dq : ℝ → ℝ)
    (hp : Continuous p) (hq : Continuous q)
    (hdp : Continuous dp) (hdq : Continuous dq) :
    (∫ t in Icc 0 (Real.pi / 2),
      dp t ^ 2 + dq t ^ 2 + 2 * p t * q t) =
      ((∫ t in Icc 0 (Real.pi / 2),
        (dp t + dq t) ^ 2 + (p t + q t) ^ 2) / 2) +
      (((∫ t in Icc 0 (Real.pi / 2), (dp t - dq t) ^ 2) -
        (∫ t in Icc 0 (Real.pi / 2), (p t - q t) ^ 2)) / 2) := by
  let plus := fun t => (dp t + dq t) ^ 2 + (p t + q t) ^ 2
  let minus := fun t => (dp t - dq t) ^ 2 - (p t - q t) ^ 2
  have hplus : Continuous plus := by dsimp [plus]; fun_prop
  have hminus : Continuous minus := by dsimp [minus]; fun_prop
  calc
    _ = (∫ t in Icc 0 (Real.pi / 2), plus t / 2 + minus t / 2) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro t _
      exact apm_m02a05_quadratic_diagonal (p t) (q t) (dp t) (dq t)
    _ = (∫ t in Icc 0 (Real.pi / 2), plus t / 2) +
        (∫ t in Icc 0 (Real.pi / 2), minus t / 2) := by
      rw [MeasureTheory.integral_add]
      · exact (hplus.div_const 2).integrableOn_Icc
      · exact (hminus.div_const 2).integrableOn_Icc
    _ = _ := by
      simp only [MeasureTheory.integral_div]
      dsimp [plus, minus]
      have hdifd : MeasureTheory.IntegrableOn
          (fun t => (dp t - dq t) ^ 2) (Icc 0 (Real.pi / 2)) :=
        ((hdp.sub hdq).pow 2).integrableOn_Icc
      have hdif : MeasureTheory.IntegrableOn
          (fun t => (p t - q t) ^ 2) (Icc 0 (Real.pi / 2)) :=
        ((hp.sub hq).pow 2).integrableOn_Icc
      rw [MeasureTheory.integral_sub hdifd hdif]

lemma apm_m02a05_quadratic_nonneg_of_diagonal
    (p q dp dq : ℝ → ℝ)
    (hdiag :
      (∫ t in Icc 0 (Real.pi / 2),
        dp t ^ 2 + dq t ^ 2 + 2 * p t * q t) =
      ((∫ t in Icc 0 (Real.pi / 2),
        (dp t + dq t) ^ 2 + (p t + q t) ^ 2) / 2) +
      (((∫ t in Icc 0 (Real.pi / 2), (dp t - dq t) ^ 2) -
        (∫ t in Icc 0 (Real.pi / 2), (p t - q t) ^ 2)) / 2))
    (hwirtinger :
      (∫ t in Icc 0 (Real.pi / 2), (p t - q t) ^ 2) ≤
        (∫ t in Icc 0 (Real.pi / 2), (dp t - dq t) ^ 2)) :
    0 ≤ (∫ t in Icc 0 (Real.pi / 2),
      dp t ^ 2 + dq t ^ 2 + 2 * p t * q t) := by
  rw [hdiag]
  have hsum := apm_m02a05_sum_mode_integral_nonneg p q dp dq
  linarith

lemma apm_m02a05_quadratic_nonneg_of_wirtinger
    (p q dp dq : ℝ → ℝ)
    (hp : Continuous p) (hq : Continuous q)
    (hdp : Continuous dp) (hdq : Continuous dq)
    (hwirtinger :
      (∫ t in Icc 0 (Real.pi / 2), (p t - q t) ^ 2) ≤
        (∫ t in Icc 0 (Real.pi / 2), (dp t - dq t) ^ 2)) :
    0 ≤ (∫ t in Icc 0 (Real.pi / 2),
      dp t ^ 2 + dq t ^ 2 + 2 * p t * q t) :=
  apm_m02a05_quadratic_nonneg_of_diagonal p q dp dq
    (apm_m02a05_quadratic_integral_diagonal p q dp dq hp hq hdp hdq)
    hwirtinger

lemma apm_m02a05_minimality_of_variation
    (x y : ℝ → ℝ)
    (hadm : apm_m02a05_admissible x y)
    (hexpand : apm_m02a05_J x y =
      apm_m02a05_J apm_m02a05_extremal apm_m02a05_extremal +
      (∫ t in Icc 0 (Real.pi / 2),
        (deriv x t - deriv apm_m02a05_extremal t) ^ 2 +
        (deriv y t - deriv apm_m02a05_extremal t) ^ 2 +
        2 * (x t - apm_m02a05_extremal t) *
          (y t - apm_m02a05_extremal t)))
    (hquad : 0 ≤ (∫ t in Icc 0 (Real.pi / 2),
        (deriv x t - deriv apm_m02a05_extremal t) ^ 2 +
        (deriv y t - deriv apm_m02a05_extremal t) ^ 2 +
        2 * (x t - apm_m02a05_extremal t) *
          (y t - apm_m02a05_extremal t))) :
    apm_m02a05_J apm_m02a05_extremal apm_m02a05_extremal ≤
      apm_m02a05_J x y := by
  rw [hexpand]
  exact le_add_of_nonneg_right hquad

lemma apm_m02a05_minimality_of_wirtinger
    (hW : ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → v 0 = 0 →
      v (Real.pi / 2) = 0 →
      (∫ t in Icc 0 (Real.pi / 2), v t ^ 2) ≤
        (∫ t in Icc 0 (Real.pi / 2), deriv v t ^ 2)) :
    ∀ x y : ℝ → ℝ, apm_m02a05_admissible x y →
      apm_m02a05_J apm_m02a05_extremal apm_m02a05_extremal ≤
        apm_m02a05_J x y := by
  intro x y hadm
  let p := fun t => x t - apm_m02a05_extremal t
  let q := fun t => y t - apm_m02a05_extremal t
  let dp := fun t => deriv x t - deriv apm_m02a05_extremal t
  let dq := fun t => deriv y t - deriv apm_m02a05_extremal t
  have hx := hadm.1
  have hy := hadm.2.1
  have he := apm_m02a05_extremal_admissible.1
  have hp : ContDiff ℝ 2 p := hx.sub he
  have hq : ContDiff ℝ 2 q := hy.sub he
  have hp0 : p 0 = 0 := by simp [p, hadm.2.2.1, apm_m02a05_extremal]
  have hq0 : q 0 = 0 := by simp [q, hadm.2.2.2.1, apm_m02a05_extremal]
  have hp1 : p (Real.pi / 2) = 0 := by
    simp [p, hadm.2.2.2.2.1, apm_m02a05_extremal]
  have hq1 : q (Real.pi / 2) = 0 := by
    simp [q, hadm.2.2.2.2.2, apm_m02a05_extremal]
  have hpq : ContDiff ℝ 2 (fun t => p t - q t) := hp.sub hq
  have hwirtinger0 := hW (fun t => p t - q t) hpq (by simp [hp0, hq0])
    (by simp [hp1, hq1])
  have hwirtinger :
      (∫ t in Icc 0 (Real.pi / 2), (p t - q t) ^ 2) ≤
        (∫ t in Icc 0 (Real.pi / 2), (dp t - dq t) ^ 2) := by
    refine hwirtinger0.trans_eq ?_
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro t _
    change deriv (fun s => p s - q s) t ^ 2 = (dp t - dq t) ^ 2
    have hvderiv : deriv (fun s => p s - q s) t = deriv p t - deriv q t := by
      simpa only [Pi.sub_apply] using
        deriv_sub (hp.differentiable (by norm_num)).differentiableAt
          (hq.differentiable (by norm_num)).differentiableAt
    rw [hvderiv]
    have hpderiv : deriv p t = deriv x t - deriv apm_m02a05_extremal t := by
      simpa only [p, Pi.sub_apply] using
        deriv_sub (hx.differentiable (by norm_num)).differentiableAt
          (he.differentiable (by norm_num)).differentiableAt
    have hqderiv : deriv q t = deriv y t - deriv apm_m02a05_extremal t := by
      simpa only [q, Pi.sub_apply] using
        deriv_sub (hy.differentiable (by norm_num)).differentiableAt
          (he.differentiable (by norm_num)).differentiableAt
    rw [hpderiv, hqderiv]
  apply apm_m02a05_minimality_of_variation x y hadm
    (apm_m02a05_energy_expansion x y hadm)
  exact apm_m02a05_quadratic_nonneg_of_wirtinger p q dp dq
    hp.continuous hq.continuous
    ((hx.continuous_deriv (by norm_num)).sub (he.continuous_deriv (by norm_num)))
    ((hy.continuous_deriv (by norm_num)).sub (he.continuous_deriv (by norm_num)))
    hwirtinger

lemma apm_m02a05_zero_left_ftc (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hv0 : v 0 = 0) (t : ℝ) :
    v t = ∫ s in (0 : ℝ)..t, deriv v s := by
  have h := intervalIntegral.integral_deriv_eq_sub
    (a := (0 : ℝ)) (b := t) (f := v)
    (fun s _ => (hv.differentiable (by norm_num)).differentiableAt)
    ((hv.continuous_deriv (by norm_num)).intervalIntegrable 0 t)
  rw [h, hv0, sub_zero]

lemma apm_m02a05_zero_right_ftc (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hv1 : v (Real.pi / 2) = 0) (t : ℝ) :
    v t = -(∫ s in t..Real.pi / 2, deriv v s) := by
  have h := intervalIntegral.integral_deriv_eq_sub
    (a := t) (b := Real.pi / 2) (f := v)
    (fun s _ => (hv.differentiable (by norm_num)).differentiableAt)
    ((hv.continuous_deriv (by norm_num)).intervalIntegrable t (Real.pi / 2))
  rw [h, hv1, zero_sub, neg_neg]

lemma apm_m02a05_wirtinger_of_sharp_bound (V E : ℝ)
    (hE : 0 ≤ E) (hsharp : V ≤ (Real.pi ^ 2 / 16) * E) : V ≤ E := by
  have hpi : Real.pi ^ 2 < 16 := by
    nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hc : Real.pi ^ 2 / 16 ≤ 1 := by nlinarith
  exact hsharp.trans (by nlinarith)

lemma apm_m02a05_integral_cauchy_sq_Icc (f : ℝ → ℝ) (hf : Continuous f)
    {a b : ℝ} (hab : a < b) :
    (∫ t in Icc a b, f t) ^ 2 ≤
      (b - a) * (∫ t in Icc a b, f t ^ 2) := by
  let F := ∫ t in Icc a b, f t
  let L : ℝ := b - a
  let c := F / L
  have hfi : MeasureTheory.IntegrableOn f (Icc a b) :=
    hf.integrableOn_Icc
  have hf2i : MeasureTheory.IntegrableOn (fun t => f t ^ 2)
      (Icc a b) := (hf.pow 2).integrableOn_Icc
  have hci : MeasureTheory.IntegrableOn (fun _t : ℝ => c)
      (Icc a b) := continuous_const.integrableOn_Icc
  have hnonneg : 0 ≤ (∫ t in Icc a b, (f t - c) ^ 2) := by
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards with t
    positivity
  have hexpand : (∫ t in Icc a b, (f t - c) ^ 2) =
      (∫ t in Icc a b, f t ^ 2) - 2 * c * F + c ^ 2 * L := by
    calc
      _ = (∫ t in Icc a b,
          f t ^ 2 - (2 * c) * f t + c ^ 2) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        intro t _
        ring
      _ = _ := by
        rw [MeasureTheory.integral_add,
          MeasureTheory.integral_sub hf2i (hfi.const_mul (2 * c)),
          MeasureTheory.integral_const_mul,
          MeasureTheory.setIntegral_const]
        · simp [F, L, MeasureTheory.Measure.real, hab.le]
          ring
        · exact hf2i.sub (hfi.const_mul (2 * c))
        · exact (continuous_const : Continuous (fun _t : ℝ => c ^ 2)).integrableOn_Icc
  rw [hexpand] at hnonneg
  dsimp [c, L, F] at hnonneg ⊢
  have hlen : 0 < b - a := sub_pos.2 hab
  field_simp [ne_of_gt hlen] at hnonneg ⊢
  nlinarith

lemma apm_m02a05_integral_cauchy_sq (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ t in Icc 0 (Real.pi / 2), f t) ^ 2 ≤
      (Real.pi / 2) * (∫ t in Icc 0 (Real.pi / 2), f t ^ 2) := by
  simpa using apm_m02a05_integral_cauchy_sq_Icc f hf
    (by positivity : (0 : ℝ) < Real.pi / 2)

lemma apm_m02a05_integral_sq_mono_Icc (f : ℝ → ℝ) (hf : Continuous f)
    {a b c d : ℝ} (hsub : Icc a b ⊆ Icc c d) :
    (∫ t in Icc a b, f t ^ 2) ≤ (∫ t in Icc c d, f t ^ 2) := by
  apply MeasureTheory.integral_mono_measure
    (MeasureTheory.Measure.restrict_mono hsub le_rfl)
  · filter_upwards with t
    positivity
  · exact (hf.pow 2).integrableOn_Icc

lemma apm_m02a05_zero_left_energy_bound (v : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) (hv0 : v 0 = 0) {t : ℝ}
    (ht : t ∈ Icc 0 (Real.pi / 2)) :
    v t ^ 2 ≤ t * (∫ s in Icc 0 (Real.pi / 2), deriv v s ^ 2) := by
  rcases eq_or_lt_of_le ht.1 with rfl | ht0
  · simp [hv0]
  have hderiv : Continuous (deriv v) := hv.continuous_deriv (by norm_num)
  have hc := apm_m02a05_integral_cauchy_sq_Icc (deriv v) hderiv ht0
  have hmono := apm_m02a05_integral_sq_mono_Icc (deriv v) hderiv
    (show Icc 0 t ⊆ Icc 0 (Real.pi / 2) by
      intro s hs
      exact ⟨hs.1, hs.2.trans ht.2⟩)
  rw [apm_m02a05_zero_left_ftc v hv hv0 t,
    intervalIntegral.integral_of_le ht.1,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have ht_nonneg : 0 ≤ t := ht.1
  nlinarith

lemma apm_m02a05_zero_right_energy_bound (v : ℝ → ℝ)
    (hv : ContDiff ℝ 2 v) (hv1 : v (Real.pi / 2) = 0) {t : ℝ}
    (ht : t ∈ Icc 0 (Real.pi / 2)) :
    v t ^ 2 ≤ (Real.pi / 2 - t) *
      (∫ s in Icc 0 (Real.pi / 2), deriv v s ^ 2) := by
  rcases eq_or_lt_of_le ht.2 with rfl | ht1
  · simp [hv1]
  have hderiv : Continuous (deriv v) := hv.continuous_deriv (by norm_num)
  have hc := apm_m02a05_integral_cauchy_sq_Icc (deriv v) hderiv ht1
  have hmono := apm_m02a05_integral_sq_mono_Icc (deriv v) hderiv
    (show Icc t (Real.pi / 2) ⊆ Icc 0 (Real.pi / 2) by
      intro s hs
      exact ⟨ht.1.trans hs.1, hs.2⟩)
  rw [apm_m02a05_zero_right_ftc v hv hv1 t,
    neg_sq,
    intervalIntegral.integral_of_le ht.2,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hlen : 0 ≤ Real.pi / 2 - t := sub_nonneg.2 ht.2
  nlinarith

lemma apm_m02a05_wirtinger_sharp (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hv0 : v 0 = 0) (hv1 : v (Real.pi / 2) = 0) :
    (∫ t in Icc 0 (Real.pi / 2), v t ^ 2) ≤
      (Real.pi ^ 2 / 16) *
        (∫ t in Icc 0 (Real.pi / 2), deriv v t ^ 2) := by
  let L : ℝ := Real.pi / 2
  let m : ℝ := L / 2
  let E : ℝ := ∫ t in Icc 0 L, deriv v t ^ 2
  have hL : 0 < L := by dsimp [L]; positivity
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have hmL : m ≤ L := by dsimp [m]; linarith
  have hv2 : Continuous (fun t => v t ^ 2) := hv.continuous.pow 2
  have hleft : (∫ t in (0 : ℝ)..m, v t ^ 2) ≤
      ∫ t in (0 : ℝ)..m, t * E := by
    apply intervalIntegral.integral_mono_on hm0
      (hv2.intervalIntegrable 0 m) ((continuous_id.mul continuous_const).intervalIntegrable 0 m)
    intro t ht
    exact apm_m02a05_zero_left_energy_bound v hv hv0
      ⟨ht.1, ht.2.trans hmL⟩
  have hright : (∫ t in m..L, v t ^ 2) ≤
      ∫ t in m..L, (L - t) * E := by
    apply intervalIntegral.integral_mono_on hmL
      (hv2.intervalIntegrable m L)
      (((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable m L)
    intro t ht
    exact apm_m02a05_zero_right_energy_bound v hv hv1
      ⟨hm0.trans ht.1, ht.2⟩
  have hsplit : (∫ t in (0 : ℝ)..m, v t ^ 2) +
      (∫ t in m..L, v t ^ 2) = ∫ t in (0 : ℝ)..L, v t ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals
      (hv2.intervalIntegrable 0 m) (hv2.intervalIntegrable m L)
  have hleft_eval : (∫ t in (0 : ℝ)..m, t * E) = (L ^ 2 / 8) * E := by
    rw [intervalIntegral.integral_mul_const, integral_id]
    dsimp [m]
    ring
  have hright_eval : (∫ t in m..L, (L - t) * E) = (L ^ 2 / 8) * E := by
    rw [intervalIntegral.integral_mul_const]
    change (∫ t in m..L, (fun _ : ℝ => L) t - id t) * E = _
    rw [intervalIntegral.integral_sub intervalIntegrable_const
        (continuous_id.intervalIntegrable m L),
      intervalIntegral.integral_const]
    have hid : (∫ t in m..L, id t) = (L ^ 2 - m ^ 2) / 2 := by
      simpa only [id_eq] using (integral_id (a := m) (b := L))
    rw [hid]
    dsimp [m]
    ring
  rw [hleft_eval] at hleft
  rw [hright_eval] at hright
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hL.le]
  rw [← hsplit]
  dsimp [L, E] at hleft hright ⊢
  nlinarith

lemma apm_m02a05_wirtinger (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hv0 : v 0 = 0) (hv1 : v (Real.pi / 2) = 0) :
    (∫ t in Icc 0 (Real.pi / 2), v t ^ 2) ≤
      (∫ t in Icc 0 (Real.pi / 2), deriv v t ^ 2) := by
  apply apm_m02a05_wirtinger_of_sharp_bound
  · apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards with t
    positivity
  · exact apm_m02a05_wirtinger_sharp v hv hv0 hv1

theorem apm_m02a05 :
    (∀ x y : ℝ → ℝ, apm_m02a05_admissible x y →
      ((∀ t ∈ Ioo 0 (Real.pi / 2),
          deriv (deriv x) t = y t ∧ deriv (deriv y) t = x t) ↔
        (Set.EqOn x apm_m02a05_extremal (Icc 0 (Real.pi / 2)) ∧
         Set.EqOn y apm_m02a05_extremal (Icc 0 (Real.pi / 2))))) ∧
    (∀ x y : ℝ → ℝ, apm_m02a05_admissible x y →
      apm_m02a05_J apm_m02a05_extremal apm_m02a05_extremal ≤
        apm_m02a05_J x y) ∧
    (∀ B : ℝ, ∃ x y : ℝ → ℝ,
      apm_m02a05_admissible x y ∧ B < apm_m02a05_J x y) := by
  refine ⟨?_, apm_m02a05_minimality_of_wirtinger apm_m02a05_wirtinger,
    apm_m02a05_unbounded_above⟩
  intro x y hadm
  exact apm_m02a05_characterization x y hadm
