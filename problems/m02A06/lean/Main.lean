import Mathlib

/-!
# APM m02A06

## Statement repairs

The source claims uniqueness for every `ε > 0`, but the contraction argument only
gives uniqueness in a bounded ball when `ε` is sufficiently small.  This is
load-bearing: already for `f = 0`, the first integral of the ODE rules out a
decaying solution with `u(0) = 1` when `ε > 3/2`.  The statement below makes
the contraction regime and its uniqueness ball explicit, using a supplied
uniform bound `C` for `f`.

## Encoding notes

The solution is a genuine twice continuously differentiable function on the
closed half-line, and `u(∞) = 0` is encoded as convergence along `atTop`.

Repair 2 (statement-refuted-by-solver, attempt 1): the previous conclusion used
`∃! u : ℝ → ℝ`, but no hypothesis constrains `u` on `(-∞, 0)` — regularity,
the ODE, the boundary value, the decay, and the ball bound all live on
`Ici 0` / `Ioi 0` / `atTop`.  Two total functions agreeing on the half-line but
differing on the negative side are distinct witnesses, so the bare `∃!` was
refutable.  The conclusion now asserts existence in the frozen ball and
uniqueness *as agreement on `Ici 0`*, which carries the full mathematical
content of the contraction argument.  The problem id and theorem name are
unchanged.
-/

open Filter Set
open scoped ContDiff Topology ZeroAtInfty

/-- The Banach space used for the contraction: continuous real functions on
the closed half-line which vanish at infinity. -/
abbrev apm_m02a06_FunctionSpace := C₀(Ici (0 : ℝ), ℝ)

instance apm_m02a06_compactIccSpace_halfLine : CompactIccSpace (Ici (0 : ℝ)) where
  isCompact_Icc := by
    intro a b
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    have himage :
        ((fun z : Ici (0 : ℝ) => (z : ℝ)) '' Icc a b) = Icc (a : ℝ) (b : ℝ) := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hx
        exact ⟨⟨x, a.property.trans hx.1⟩, hx, rfl⟩
    rw [himage]
    exact isCompact_Icc

/-- The closed sup-norm ball on which the nonlinear transform contracts. -/
abbrev apm_m02a06_Ball (C : ℝ) :=
  Metric.closedBall (0 : apm_m02a06_FunctionSpace) (2 * (1 + C))

lemma apm_m02a06_ball_nonempty (C : ℝ) (hC : 0 ≤ C) :
    Nonempty (apm_m02a06_Ball C) := by
  exact ⟨⟨0, by simpa [Metric.mem_closedBall] using
    (show (0 : ℝ) ≤ 2 * (1 + C) by positivity)⟩⟩

lemma apm_m02a06_ball_isComplete (C : ℝ) :
    IsComplete (Metric.closedBall (0 : apm_m02a06_FunctionSpace) (2 * (1 + C))) :=
  Metric.isClosed_closedBall.isComplete

lemma apm_m02a06_ball_pointwise_bound
    (C : ℝ) (u : apm_m02a06_Ball C) (x : Ici (0 : ℝ)) :
    |u.1 x| ≤ 2 * (1 + C) := by
  have hnorm : ‖u.1‖ ≤ 2 * (1 + C) := by
    have hp := u.property
    change dist u.1 (0 : apm_m02a06_FunctionSpace) ≤ 2 * (1 + C) at hp
    simpa only [dist_zero_right] using hp
  exact (by simpa [Real.norm_eq_abs] using
    (BoundedContinuousFunction.norm_coe_le_norm u.1.toBCF x).trans hnorm)

lemma apm_m02a06_ball_pointwise_sub_le_dist
    (C : ℝ) (u v : apm_m02a06_Ball C) (x : Ici (0 : ℝ)) :
    |u.1 x - v.1 x| ≤ dist u v := by
  simpa only [Real.dist_eq, ZeroAtInftyContinuousMap.dist_toBCF_eq_dist,
    Subtype.dist_eq] using
      (BoundedContinuousFunction.dist_coe_le_dist (f := u.1.toBCF) (g := v.1.toBCF) x)

lemma apm_m02a06_functionSpace_continuous (u : apm_m02a06_FunctionSpace) :
    Continuous u := map_continuous u

lemma apm_m02a06_functionSpace_tendsto_atTop (u : apm_m02a06_FunctionSpace) :
    Tendsto u atTop (nhds 0) := by
  rw [← cocompact_eq_atTop]
  exact zero_at_infty u

/-- Extend a function on the closed half-line continuously to all reals by
freezing it at its boundary value on the negative half-line. -/
noncomputable def apm_m02a06_extend (u : apm_m02a06_FunctionSpace) (x : ℝ) : ℝ :=
  u ⟨max 0 x, le_max_left 0 x⟩

lemma apm_m02a06_extend_continuous (u : apm_m02a06_FunctionSpace) :
    Continuous (apm_m02a06_extend u) := by
  exact (apm_m02a06_functionSpace_continuous u).comp
    ((continuous_const.max continuous_id).subtype_mk _)

@[simp] lemma apm_m02a06_extend_of_nonneg (u : apm_m02a06_FunctionSpace)
    {x : ℝ} (hx : 0 ≤ x) : apm_m02a06_extend u x = u ⟨x, hx⟩ := by
  simp [apm_m02a06_extend, max_eq_right hx]

lemma apm_m02a06_extend_ball_bound (C : ℝ) (u : apm_m02a06_Ball C) (x : ℝ) :
    |apm_m02a06_extend u.1 x| ≤ 2 * (1 + C) := by
  exact apm_m02a06_ball_pointwise_bound C u ⟨max 0 x, le_max_left 0 x⟩

lemma apm_m02a06_extend_sub_le_dist (C : ℝ) (u v : apm_m02a06_Ball C) (x : ℝ) :
    |apm_m02a06_extend u.1 x - apm_m02a06_extend v.1 x| ≤ dist u v := by
  exact apm_m02a06_ball_pointwise_sub_le_dist C u v
    ⟨max 0 x, le_max_left 0 x⟩

lemma apm_m02a06_maxToHalfLine_tendsto_atTop :
    Tendsto (fun x : ℝ => (⟨max 0 x, le_max_left 0 x⟩ : Ici (0 : ℝ))) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop (b : ℝ)] with x hx
  exact hx.trans (le_max_right 0 x)

lemma apm_m02a06_extend_tendsto_atTop (u : apm_m02a06_FunctionSpace) :
    Tendsto (apm_m02a06_extend u) atTop (nhds 0) := by
  exact (apm_m02a06_functionSpace_tendsto_atTop u).comp
    apm_m02a06_maxToHalfLine_tendsto_atTop

lemma apm_m02a06_extend_sq_tendsto_atTop (u : apm_m02a06_FunctionSpace) :
    Tendsto (fun x => (apm_m02a06_extend u x) ^ 2) atTop (nhds 0) := by
  simpa only [pow_two, zero_mul] using
    (apm_m02a06_extend_tendsto_atTop u).mul
      (apm_m02a06_extend_tendsto_atTop u)

lemma apm_m02a06_source_continuous (ε : ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) (u : apm_m02a06_FunctionSpace) :
    Continuous (fun x => f x + ε * (apm_m02a06_extend u x) ^ 2) := by
  exact hf.add (continuous_const.mul ((apm_m02a06_extend_continuous u).pow 2))

lemma apm_m02a06_source_tendsto_atTop (ε : ℝ) (f : ℝ → ℝ)
    (hf : Tendsto f atTop (nhds 0)) (u : apm_m02a06_FunctionSpace) :
    Tendsto (fun x => f x + ε * (apm_m02a06_extend u x) ^ 2) atTop (nhds 0) := by
  simpa only [zero_add, mul_zero] using hf.add
    (tendsto_const_nhds.mul (apm_m02a06_extend_sq_tendsto_atTop u))

lemma apm_m02a06_tendsto_zero_of_compactSupport (f : ℝ → ℝ)
    (hf : HasCompactSupport f) : Tendsto f atTop (nhds 0) := by
  have he : f =ᶠ[coclosedCompact ℝ] 0 := hasCompactSupport_iff_eventuallyEq.mp hf
  rw [Filter.coclosedCompact_eq_cocompact] at he
  have he' : f =ᶠ[atTop] 0 := he.filter_mono atTop_le_cocompact
  exact (tendsto_congr' he').2 tendsto_const_nhds

lemma apm_m02a06_nonlinear_source_tendsto_atTop
    (ε : ℝ) (f : ℝ → ℝ) (hf : HasCompactSupport f)
    (u : apm_m02a06_FunctionSpace) :
    Tendsto (fun x => f x + ε * (apm_m02a06_extend u x) ^ 2) atTop (nhds 0) :=
  apm_m02a06_source_tendsto_atTop ε f
    (apm_m02a06_tendsto_zero_of_compactSupport f hf) u

lemma apm_m02a06_source_bound (C ε : ℝ) (f : ℝ → ℝ)
    (u : apm_m02a06_Ball C) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hf : ∀ x ∈ Ici (0 : ℝ), |f x| ≤ C) (x : ℝ) (hx : 0 ≤ x) :
    |f x + ε * (apm_m02a06_extend u.1 x) ^ 2| ≤
      C + ε * (2 * (1 + C)) ^ 2 := by
  calc
    |f x + ε * (apm_m02a06_extend u.1 x) ^ 2| ≤
        |f x| + |ε * (apm_m02a06_extend u.1 x) ^ 2| := abs_add_le _ _
    _ = |f x| + ε * (apm_m02a06_extend u.1 x) ^ 2 := by
      rw [abs_mul, abs_of_nonneg hε, abs_sq]
    _ ≤ C + ε * (2 * (1 + C)) ^ 2 := add_le_add (hf x hx)
      (mul_le_mul_of_nonneg_left
        ((sq_le_sq).2 (by simpa [abs_of_nonneg (by positivity : 0 ≤ 2 * (1 + C))]
          using apm_m02a06_extend_ball_bound C u x)) hε)

lemma apm_m02a06_subtypeVal_tendsto_atTop :
    Tendsto ((↑) : Ici (0 : ℝ) → ℝ) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop
    ⟨max 0 b, show 0 ≤ max 0 b from le_max_left _ _⟩] with a ha
  exact (le_max_right 0 b).trans ha

/-- Restrict a continuous half-line function tending to zero to the complete
`C₀` carrier. -/
noncomputable def apm_m02a06_toFunctionSpace
    (u : ℝ → ℝ) (hu_cont : ContinuousOn u (Ici 0))
    (hu_zero : Tendsto u atTop (nhds 0)) : apm_m02a06_FunctionSpace where
  toFun x := u x
  continuous_toFun := hu_cont.restrict
  zero_at_infty' := by
    rw [cocompact_eq_atTop]
    exact hu_zero.comp apm_m02a06_subtypeVal_tendsto_atTop

@[simp] lemma apm_m02a06_toFunctionSpace_apply
    (u : ℝ → ℝ) (hu_cont : ContinuousOn u (Ici 0))
    (hu_zero : Tendsto u atTop (nhds 0)) (x : Ici (0 : ℝ)) :
    apm_m02a06_toFunctionSpace u hu_cont hu_zero x = u x := rfl

def apm_m02a06_IsSolution (ε : ℝ) (f u : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 u (Ici 0) ∧
  (∀ x ∈ Ioi (0 : ℝ), -deriv (deriv u) x + u x - ε * (u x) ^ 2 = f x) ∧
  u 0 = 1 ∧ Tendsto u atTop (nhds 0)

lemma apm_m02a06_radius_pos (C : ℝ) (hC : 0 ≤ C) :
    0 < 2 * (1 + C) := by positivity

lemma apm_m02a06_contraction_constant_lt_one
    (C ε : ℝ) (hC : 0 ≤ C) (hε_small : ε < 1 / (4 * (1 + C))) :
    4 * ε * (1 + C) < 1 := by
  have hpos : 0 < 1 + C := by positivity
  calc
    4 * ε * (1 + C) < 4 * (1 / (4 * (1 + C))) * (1 + C) := by
      gcongr
    _ = 1 := by field_simp

lemma apm_m02a06_quadratic_lipschitz
    (C ε u v : ℝ) (hε : 0 ≤ ε)
    (hu : |u| ≤ 2 * (1 + C)) (hv : |v| ≤ 2 * (1 + C)) :
    |ε * u ^ 2 - ε * v ^ 2| ≤
      (4 * ε * (1 + C)) * |u - v| := by
  rw [← mul_sub, sq_sub_sq, abs_mul, abs_mul, abs_of_nonneg hε]
  have hadd : |u + v| ≤ 4 * (1 + C) := by
    calc
      |u + v| ≤ |u| + |v| := abs_add_le u v
      _ ≤ 4 * (1 + C) := by linarith
  calc
    ε * (|u + v| * |u - v|) = (ε * |u + v|) * |u - v| := by ring
    _ ≤ (ε * (4 * (1 + C))) * |u - v| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hadd hε) (abs_nonneg _)
    _ = 4 * ε * (1 + C) * |u - v| := by ring

/-- The Dirichlet Green kernel for `-u'' + u` on the nonnegative half-line. -/
noncomputable def apm_m02a06_greenKernel (x y : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (Real.exp (-|x - y|) - Real.exp (-(x + y)))

lemma apm_m02a06_greenKernel_comm (x y : ℝ) :
    apm_m02a06_greenKernel x y = apm_m02a06_greenKernel y x := by
  simp only [apm_m02a06_greenKernel, add_comm]
  rw [abs_sub_comm]

lemma apm_m02a06_greenKernel_zero_left {y : ℝ} (hy : 0 ≤ y) :
    apm_m02a06_greenKernel 0 y = 0 := by
  simp [apm_m02a06_greenKernel, abs_of_nonneg hy]

lemma apm_m02a06_greenKernel_zero_right {x : ℝ} (hx : 0 ≤ x) :
    apm_m02a06_greenKernel x 0 = 0 := by
  simp [apm_m02a06_greenKernel, abs_of_nonneg hx]

lemma apm_m02a06_greenKernel_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ apm_m02a06_greenKernel x y := by
  have habs : |x - y| ≤ x + y := by
    calc
      |x - y| ≤ |x| + |y| := abs_sub x y
      _ = x + y := by rw [abs_of_nonneg hx, abs_of_nonneg hy]
  have hexp : Real.exp (-(x + y)) ≤ Real.exp (-|x - y|) := by
    exact Real.exp_le_exp.mpr (neg_le_neg habs)
  unfold apm_m02a06_greenKernel
  exact mul_nonneg (by norm_num) (sub_nonneg.mpr hexp)

lemma apm_m02a06_greenKernel_le_half {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    apm_m02a06_greenKernel x y ≤ 1 / 2 := by
  have hsum : 0 ≤ x + y := add_nonneg hx hy
  have hfirst : Real.exp (-|x - y|) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))
  have hsecond : 0 ≤ Real.exp (-(x + y)) := Real.exp_pos _ |>.le
  unfold apm_m02a06_greenKernel
  nlinarith

/-- On the lower triangle the absolute value in the Green kernel disappears. -/
lemma apm_m02a06_greenKernel_of_le {x y : ℝ} (hyx : y ≤ x) :
    apm_m02a06_greenKernel x y =
      (1 / 2 : ℝ) * (Real.exp (-(x - y)) - Real.exp (-(x + y))) := by
  simp [apm_m02a06_greenKernel, abs_of_nonneg (sub_nonneg.mpr hyx)]

/-- On the upper triangle the absolute value in the Green kernel disappears
with the opposite affine branch. -/
lemma apm_m02a06_greenKernel_of_ge {x y : ℝ} (hxy : x ≤ y) :
    apm_m02a06_greenKernel x y =
      (1 / 2 : ℝ) * (Real.exp (-(y - x)) - Real.exp (-(x + y))) := by
  rw [apm_m02a06_greenKernel_comm]
  simpa [add_comm] using apm_m02a06_greenKernel_of_le hxy

/-- The exponentially decaying part of the kernel is already a pointwise
majorant; this is the domination needed for the improper Green integral. -/
lemma apm_m02a06_greenKernel_le_exp {x y : ℝ} :
    apm_m02a06_greenKernel x y ≤ (1 / 2 : ℝ) * Real.exp (-|x - y|) := by
  have hnonneg : 0 ≤ Real.exp (-(x + y)) := (Real.exp_pos _).le
  unfold apm_m02a06_greenKernel
  nlinarith

/-- The reflected exponential in the Dirichlet kernel has exactly the mass
`exp (-x)` on the half-line.  This is one of the two scalar identities needed
to compute the full Green-kernel mass and hence its sup-norm operator bound. -/
lemma apm_m02a06_integral_reflected_exp (x : ℝ) :
    (∫ y in Ici (0 : ℝ), Real.exp (-(x + y))) = Real.exp (-x) := by
  have hIoi :
      (∫ y in Ioi (0 : ℝ), Real.exp (-x) * Real.exp (-y)) = Real.exp (-x) := by
    rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi, ← hIoi]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  rw [← Real.exp_add]
  ring_nf

lemma apm_m02a06_integral_exp_abs_lower (x : ℝ) (hx : 0 ≤ x) :
    (∫ y in Ioc (0 : ℝ) x, Real.exp (-|x - y|)) = 1 - Real.exp (-x) := by
  rw [← intervalIntegral.integral_of_le hx]
  calc
    (∫ y in (0 : ℝ)..x, Real.exp (-|x - y|)) =
        Real.exp (-x) * ∫ y in (0 : ℝ)..x, Real.exp y := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro y hy
      rw [uIcc_of_le hx] at hy
      change Real.exp (-|x - y|) = Real.exp (-x) * Real.exp y
      rw [abs_of_nonneg (sub_nonneg.mpr hy.2), ← Real.exp_add]
      ring_nf
    _ = 1 - Real.exp (-x) := by
      rw [integral_exp, Real.exp_zero]
      rw [mul_sub]
      have hxexp : Real.exp (-x) * Real.exp x = 1 := by
        rw [← Real.exp_add]
        simp
      rw [hxexp, mul_one]

lemma apm_m02a06_integral_exp_abs_upper (x : ℝ) :
    (∫ y in Ici x, Real.exp (-|x - y|)) = 1 := by
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  calc
    (∫ y in Ioi x, Real.exp (-|x - y|)) =
        Real.exp x * ∫ y in Ioi x, Real.exp (-y) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      change Real.exp (-|x - y|) = Real.exp x * Real.exp (-y)
      rw [abs_of_nonpos (sub_nonpos.mpr hy.le), ← Real.exp_add]
      ring_nf
    _ = 1 := by
      rw [integral_exp_neg_Ioi]
      rw [← Real.exp_add]
      simp

lemma apm_m02a06_integrableOn_exp_abs_upper (x : ℝ) :
    MeasureTheory.IntegrableOn (fun y : ℝ => Real.exp (-|x - y|)) (Ioi x) := by
  refine MeasureTheory.IntegrableOn.congr_fun
    ((integrableOn_exp_neg_Ioi x).const_mul (Real.exp x)) ?_ measurableSet_Ioi
  intro y hy
  change Real.exp x * Real.exp (-y) = Real.exp (-|x - y|)
  symm
  rw [abs_of_nonpos (sub_nonpos.mpr hy.le), ← Real.exp_add]
  ring_nf

lemma apm_m02a06_integral_exp_abs (x : ℝ) (hx : 0 ≤ x) :
    (∫ y in Ici (0 : ℝ), Real.exp (-|x - y|)) = 2 - Real.exp (-x) := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [apm_m02a06_integral_exp_abs_upper]
    norm_num
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi, ← Ioc_union_Ioi_eq_Ioi hx.le]
  rw [MeasureTheory.setIntegral_union]
  · rw [apm_m02a06_integral_exp_abs_lower x hx.le,
      ← MeasureTheory.integral_Ici_eq_integral_Ioi,
      apm_m02a06_integral_exp_abs_upper x]
    ring
  · exact Ioc_disjoint_Ioi_same
  · exact measurableSet_Ioi
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).1
      ((by fun_prop : Continuous (fun y : ℝ => Real.exp (-|x - y|))).intervalIntegrable _ _)
  · exact apm_m02a06_integrableOn_exp_abs_upper x

lemma apm_m02a06_integrableOn_exp_abs (x : ℝ) (hx : 0 ≤ x) :
    MeasureTheory.IntegrableOn (fun y : ℝ => Real.exp (-|x - y|)) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  rcases hx.eq_or_lt with rfl | hx
  · exact apm_m02a06_integrableOn_exp_abs_upper 0
  rw [← Ioc_union_Ioi_eq_Ioi hx.le]
  exact MeasureTheory.IntegrableOn.union
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).1
      ((by fun_prop : Continuous (fun y : ℝ => Real.exp (-|x - y|))).intervalIntegrable _ _))
    (apm_m02a06_integrableOn_exp_abs_upper x)

lemma apm_m02a06_integrableOn_reflected_exp (x : ℝ) :
    MeasureTheory.IntegrableOn (fun y : ℝ => Real.exp (-(x + y))) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  refine MeasureTheory.IntegrableOn.congr_fun
    ((integrableOn_exp_neg_Ioi 0).const_mul (Real.exp (-x))) ?_ measurableSet_Ioi
  intro y _
  change Real.exp (-x) * Real.exp (-y) = Real.exp (-(x + y))
  rw [← Real.exp_add]
  ring_nf

/-- Exact half-line mass of the Dirichlet Green kernel. -/
lemma apm_m02a06_integral_greenKernel (x : ℝ) (hx : 0 ≤ x) :
    (∫ y in Ici (0 : ℝ), apm_m02a06_greenKernel x y) = 1 - Real.exp (-x) := by
  unfold apm_m02a06_greenKernel
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub (apm_m02a06_integrableOn_exp_abs x hx)
      (apm_m02a06_integrableOn_reflected_exp x),
    apm_m02a06_integral_exp_abs x hx,
    apm_m02a06_integral_reflected_exp]
  ring

lemma apm_m02a06_integral_greenKernel_le_one (x : ℝ) (hx : 0 ≤ x) :
    (∫ y in Ici (0 : ℝ), apm_m02a06_greenKernel x y) ≤ 1 := by
  rw [apm_m02a06_integral_greenKernel x hx]
  exact sub_le_self _ (Real.exp_pos _).le

lemma apm_m02a06_integrableOn_greenKernel (x : ℝ) (hx : 0 ≤ x) :
    MeasureTheory.IntegrableOn (apm_m02a06_greenKernel x) (Ici 0) := by
  simpa only [apm_m02a06_greenKernel] using
    ((apm_m02a06_integrableOn_exp_abs x hx).sub
      (apm_m02a06_integrableOn_reflected_exp x)).const_mul (1 / 2 : ℝ)

/-- The Green operator has sup-norm at most one.  No measurability assumption
on `h` is needed for the inequality itself: if the integrand is not strongly
measurable, the Bochner integral is definitionally zero. -/
lemma apm_m02a06_greenKernel_integral_mul_le
    (x B : ℝ) (h : ℝ → ℝ) (hx : 0 ≤ x) (hB : 0 ≤ B)
    (hh : ∀ y ∈ Ici (0 : ℝ), |h y| ≤ B) :
    |∫ y in Ici (0 : ℝ), apm_m02a06_greenKernel x y * h y| ≤ B := by
  have hdom : MeasureTheory.IntegrableOn
      (fun y => B * apm_m02a06_greenKernel x y) (Ici 0) :=
    (apm_m02a06_integrableOn_greenKernel x hx).const_mul B
  calc
    |∫ y in Ici (0 : ℝ), apm_m02a06_greenKernel x y * h y| =
        ‖∫ y in Ici (0 : ℝ), apm_m02a06_greenKernel x y * h y‖ :=
      (Real.norm_eq_abs _).symm
    _ ≤ ∫ y in Ici (0 : ℝ), B * apm_m02a06_greenKernel x y := by
      apply MeasureTheory.norm_integral_le_of_norm_le hdom
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with y hy
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (apm_m02a06_greenKernel_nonneg hx hy),
        mul_comm B]
      exact mul_le_mul_of_nonneg_left (hh y hy) (apm_m02a06_greenKernel_nonneg hx hy)
    _ = B * (∫ y in Ici (0 : ℝ), apm_m02a06_greenKernel x y) := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ B * 1 := mul_le_mul_of_nonneg_left
      (apm_m02a06_integral_greenKernel_le_one x hx) hB
    _ = B := mul_one B

/-- The concrete nonlinear half-line Green transform whose fixed point is the
desired solution.  Exposing it makes the remaining parameter-integral and
Banach-contraction bridge precise. -/
noncomputable def apm_m02a06_greenTransform
    (ε : ℝ) (f u : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-x) +
    ∫ y in Ici (0 : ℝ),
      apm_m02a06_greenKernel x y * (f y + ε * (u y) ^ 2)

/-- Algebraically split presentation of the linear Green operator.  The two
moving-endpoint integrals are over finite intervals; the only improper term
is a fixed scalar. -/
noncomputable def apm_m02a06_greenSplit (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (Real.exp (-x) * (∫ y in (0 : ℝ)..x, Real.exp y * h y) +
      Real.exp x * ((∫ y in Ioi (0 : ℝ), Real.exp (-y) * h y) -
        ∫ y in (0 : ℝ)..x, Real.exp (-y) * h y) -
      Real.exp (-x) * ∫ y in Ioi (0 : ℝ), Real.exp (-y) * h y)

lemma apm_m02a06_greenSplit_continuous (h : ℝ → ℝ) (hh : Continuous h) :
    Continuous (apm_m02a06_greenSplit h) := by
  have hpos : ∀ a b : ℝ,
      IntervalIntegrable (fun y : ℝ => Real.exp y * h y) MeasureTheory.volume a b :=
    fun a b => by
      simpa only [Pi.mul_apply] using
        ((Real.continuous_exp.comp continuous_id).mul hh).intervalIntegrable a b
  have hneg : ∀ a b : ℝ,
      IntervalIntegrable (fun y : ℝ => Real.exp (-y) * h y) MeasureTheory.volume a b :=
    fun a b => by
      simpa only [Pi.mul_apply] using
        ((Real.continuous_exp.comp continuous_neg).mul hh).intervalIntegrable a b
  unfold apm_m02a06_greenSplit
  fun_prop

lemma apm_m02a06_hasDerivAt_integral_exp_mul
    (h : ℝ → ℝ) (hh : Continuous h) (x : ℝ) :
    HasDerivAt (fun z => ∫ y in (0 : ℝ)..z, Real.exp y * h y)
      (Real.exp x * h x) x := by
  let g : ℝ → ℝ := fun y => Real.exp y * h y
  have hg : Continuous g := (Real.continuous_exp.comp continuous_id).mul hh
  exact intervalIntegral.integral_hasDerivAt_right
    (hg.intervalIntegrable 0 x) (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt

lemma apm_m02a06_hasDerivAt_integral_exp_neg_mul
    (h : ℝ → ℝ) (hh : Continuous h) (x : ℝ) :
    HasDerivAt (fun z => ∫ y in (0 : ℝ)..z, Real.exp (-y) * h y)
      (Real.exp (-x) * h x) x := by
  let g : ℝ → ℝ := fun y => Real.exp (-y) * h y
  have hg : Continuous g := (Real.continuous_exp.comp continuous_neg).mul hh
  exact intervalIntegral.integral_hasDerivAt_right
    (hg.intervalIntegrable 0 x) (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt

noncomputable def apm_m02a06_greenSplitDeriv (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (-Real.exp (-x) * (∫ y in (0 : ℝ)..x, Real.exp y * h y) +
      Real.exp x * ((∫ y in Ioi (0 : ℝ), Real.exp (-y) * h y) -
        ∫ y in (0 : ℝ)..x, Real.exp (-y) * h y) +
      Real.exp (-x) * ∫ y in Ioi (0 : ℝ), Real.exp (-y) * h y)

lemma apm_m02a06_greenSplit_hasDerivAt
    (h : ℝ → ℝ) (hh : Continuous h) (x : ℝ) :
    HasDerivAt (apm_m02a06_greenSplit h) (apm_m02a06_greenSplitDeriv h x) x := by
  have hp := apm_m02a06_hasDerivAt_integral_exp_mul h hh x
  have hn := apm_m02a06_hasDerivAt_integral_exp_neg_mul h hh x
  have hep : HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp x
  have hen : HasDerivAt (fun z : ℝ => Real.exp (-z)) (-Real.exp (-x)) x := by
    convert (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg using 1 <;> ring
  have hc : HasDerivAt
      (fun _ : ℝ => ∫ y in Ioi (0 : ℝ), Real.exp (-y) * h y) 0 x := hasDerivAt_const _ _
  unfold apm_m02a06_greenSplit apm_m02a06_greenSplitDeriv
  convert (hasDerivAt_const x (1 / 2 : ℝ)).mul
    (((hen.mul hp).add (hep.mul (hc.sub hn))).sub (hen.mul hc)) using 1 <;>
      simp only [Pi.sub_apply] <;> ring

lemma apm_m02a06_greenSplitDeriv_hasDerivAt
    (h : ℝ → ℝ) (hh : Continuous h) (x : ℝ) :
    HasDerivAt (apm_m02a06_greenSplitDeriv h)
      (apm_m02a06_greenSplit h x - h x) x := by
  have hp := apm_m02a06_hasDerivAt_integral_exp_mul h hh x
  have hn := apm_m02a06_hasDerivAt_integral_exp_neg_mul h hh x
  have hep : HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp x
  have hen : HasDerivAt (fun z : ℝ => Real.exp (-z)) (-Real.exp (-x)) x := by
    convert (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg using 1 <;> ring
  have hc : HasDerivAt
      (fun _ : ℝ => ∫ y in Ioi (0 : ℝ), Real.exp (-y) * h y) 0 x := hasDerivAt_const _ _
  have hexp : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]
    simp
  have hexp' : Real.exp x * Real.exp (-x) = 1 := by simpa [mul_comm] using hexp
  have hexph : Real.exp (-x) * Real.exp x * h x = h x := by rw [hexp, one_mul]
  have hexph' : Real.exp x * Real.exp (-x) * h x = h x := by rw [hexp', one_mul]
  have hexphNested : Real.exp (-x) * (Real.exp x * h x) = h x := by
    rw [← mul_assoc, hexp, one_mul]
  have hexphNested' : Real.exp x * (Real.exp (-x) * h x) = h x := by
    rw [← mul_assoc, hexp', one_mul]
  have hneg1 : -Real.exp (-x) * (Real.exp x * h x) = -h x := by
    rw [neg_mul, hexphNested]
  have hneg2 : Real.exp x * -(Real.exp (-x) * h x) = -h x := by
    rw [mul_neg, hexphNested']
  unfold apm_m02a06_greenSplitDeriv apm_m02a06_greenSplit
  convert (hasDerivAt_const x (1 / 2 : ℝ)).mul
    ((((hen.neg.mul hp).add (hep.mul (hc.sub hn))).add (hen.mul hc))) using 1 <;>
      simp only [Pi.sub_apply, Pi.neg_apply, Pi.mul_apply, Pi.add_apply, zero_mul,
        zero_add, mul_zero, add_zero, sub_zero, zero_sub, neg_neg, hneg1, hneg2] <;>
      ring

lemma apm_m02a06_greenSplit_ode (h : ℝ → ℝ) (hh : Continuous h) (x : ℝ) :
    -deriv (deriv (apm_m02a06_greenSplit h)) x + apm_m02a06_greenSplit h x = h x := by
  have hd : deriv (apm_m02a06_greenSplit h) = apm_m02a06_greenSplitDeriv h := by
    funext z
    exact (apm_m02a06_greenSplit_hasDerivAt h hh z).deriv
  rw [hd, (apm_m02a06_greenSplitDeriv_hasDerivAt h hh x).deriv]
  ring

lemma apm_m02a06_deriv_exp_neg (x : ℝ) :
    deriv (fun z : ℝ => Real.exp (-z)) x = -Real.exp (-x) := by
  convert ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg).deriv using 1 <;> ring

lemma apm_m02a06_deriv_deriv_exp_neg (x : ℝ) :
    deriv (deriv (fun z : ℝ => Real.exp (-z))) x = Real.exp (-x) := by
  have hd : deriv (fun z : ℝ => Real.exp (-z)) = fun z => -Real.exp (-z) := by
    funext z
    exact apm_m02a06_deriv_exp_neg z
  rw [hd]
  convert (((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg).neg).deriv using 1 <;> ring

lemma apm_m02a06_exp_add_greenSplit_ode
    (h : ℝ → ℝ) (hh : Continuous h) (x : ℝ) :
    -deriv (deriv (fun z => Real.exp (-z) + apm_m02a06_greenSplit h z)) x +
        (Real.exp (-x) + apm_m02a06_greenSplit h x) = h x := by
  have he : Differentiable ℝ (fun z : ℝ => Real.exp (-z)) := by fun_prop
  have hg : Differentiable ℝ (apm_m02a06_greenSplit h) := fun z =>
    (apm_m02a06_greenSplit_hasDerivAt h hh z).differentiableAt
  have hd : deriv (fun z => Real.exp (-z) + apm_m02a06_greenSplit h z) =
      fun z => deriv (fun w : ℝ => Real.exp (-w)) z +
        deriv (apm_m02a06_greenSplit h) z := by
    funext z
    exact deriv_add (he z) (hg z)
  rw [hd]
  have hde : Differentiable ℝ (deriv fun z : ℝ => Real.exp (-z)) := by
    rw [show deriv (fun z : ℝ => Real.exp (-z)) = fun z => -Real.exp (-z) by
      funext z
      exact apm_m02a06_deriv_exp_neg z]
    fun_prop
  have hdg : Differentiable ℝ (deriv (apm_m02a06_greenSplit h)) := by
    rw [show deriv (apm_m02a06_greenSplit h) = apm_m02a06_greenSplitDeriv h by
      funext z
      exact (apm_m02a06_greenSplit_hasDerivAt h hh z).deriv]
    exact fun z => (apm_m02a06_greenSplitDeriv_hasDerivAt h hh z).differentiableAt
  have hdd : deriv (fun z => deriv (fun w : ℝ => Real.exp (-w)) z +
      deriv (apm_m02a06_greenSplit h) z) x =
      deriv (deriv (fun w : ℝ => Real.exp (-w))) x +
        deriv (deriv (apm_m02a06_greenSplit h)) x := deriv_add (hde x) (hdg x)
  rw [hdd, apm_m02a06_deriv_deriv_exp_neg]
  linarith [apm_m02a06_greenSplit_ode h hh x]

/-- A continuous source is sent by the split Green operator to a globally
twice continuously differentiable function. -/
lemma apm_m02a06_greenSplit_contDiff_two (h : ℝ → ℝ) (hh : Continuous h) :
    ContDiff ℝ 2 (apm_m02a06_greenSplit h) := by
  have hdif : Differentiable ℝ (apm_m02a06_greenSplit h) := fun x =>
    (apm_m02a06_greenSplit_hasDerivAt h hh x).differentiableAt
  have hd : deriv (apm_m02a06_greenSplit h) = apm_m02a06_greenSplitDeriv h := by
    funext x
    exact (apm_m02a06_greenSplit_hasDerivAt h hh x).deriv
  have hdd : deriv (apm_m02a06_greenSplitDeriv h) =
      fun x => apm_m02a06_greenSplit h x - h x := by
    funext x
    exact (apm_m02a06_greenSplitDeriv_hasDerivAt h hh x).deriv
  have hderiv : ContDiff ℝ 1 (apm_m02a06_greenSplitDeriv h) := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun x =>
      (apm_m02a06_greenSplitDeriv_hasDerivAt h hh x).differentiableAt, ?_⟩
    rw [hdd]
    exact (apm_m02a06_greenSplit_continuous h hh).sub hh
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  exact ⟨hdif, by simp, by simpa only [hd] using hderiv⟩

lemma apm_m02a06_greenSplit_zero (h : ℝ → ℝ) :
    apm_m02a06_greenSplit h 0 = 0 := by
  simp [apm_m02a06_greenSplit]

lemma apm_m02a06_integrableOn_exp_neg_mul
    (h : ℝ → ℝ) (B : ℝ) (hh : Continuous h)
    (hB : ∀ y ∈ Ioi (0 : ℝ), |h y| ≤ B) :
    MeasureTheory.IntegrableOn (fun y : ℝ => Real.exp (-y) * h y) (Ioi 0) := by
  have hi : MeasureTheory.IntegrableOn
      (fun y : ℝ => h y * Real.exp (-y)) (Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).bdd_mul hh.aestronglyMeasurable (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with y hy
      simpa only [Real.norm_eq_abs] using hB y hy)
  simpa only [mul_comm] using hi

lemma apm_m02a06_integral_exp_neg_mul_Ioi_eq
    (h : ℝ → ℝ) (B x : ℝ) (hh : Continuous h)
    (hB : ∀ y ∈ Ioi (0 : ℝ), |h y| ≤ B) (hx : 0 ≤ x) :
    (∫ y in Ioi x, Real.exp (-y) * h y) =
      (∫ y in Ioi (0 : ℝ), Real.exp (-y) * h y) -
        ∫ y in (0 : ℝ)..x, Real.exp (-y) * h y := by
  have hi := apm_m02a06_integrableOn_exp_neg_mul h B hh hB
  linarith [intervalIntegral.integral_Ioi_sub_Ioi hi hx]

lemma apm_m02a06_exp_mul_integral_tail_le
    (h : ℝ → ℝ) (δ x : ℝ)
    (hh : ∀ y ∈ Ioi x, |h y| ≤ δ) :
    |Real.exp x * ∫ y in Ioi x, Real.exp (-y) * h y| ≤ δ := by
  have hg : MeasureTheory.IntegrableOn (fun y : ℝ => δ * Real.exp (-y)) (Ioi x) :=
    (integrableOn_exp_neg_Ioi x).const_mul δ
  have hint : |∫ y in Ioi x, Real.exp (-y) * h y| ≤
      ∫ y in Ioi x, δ * Real.exp (-y) := by
    simpa only [Real.norm_eq_abs] using MeasureTheory.norm_integral_le_of_norm_le
      (f := fun y : ℝ => Real.exp (-y) * h y) hg (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with y hy
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      nlinarith [Real.exp_pos (-y), hh y hy])
  calc
    |Real.exp x * ∫ y in Ioi x, Real.exp (-y) * h y| =
        Real.exp x * |∫ y in Ioi x, Real.exp (-y) * h y| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos x)]
    _ ≤ Real.exp x * (∫ y in Ioi x, δ * Real.exp (-y)) :=
      mul_le_mul_of_nonneg_left hint (Real.exp_pos x).le
    _ = δ := by
      rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi]
      calc
        Real.exp x * (δ * Real.exp (-x)) = δ * (Real.exp x * Real.exp (-x)) := by ring
        _ = δ := by rw [← Real.exp_add]; simp

lemma apm_m02a06_exp_mul_integral_tail_tendsto
    (h : ℝ → ℝ) (hzero : Filter.Tendsto h Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun x : ℝ => Real.exp x * ∫ y in Ioi x, Real.exp (-y) * h y)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop] at hzero ⊢
  intro ε hε
  obtain ⟨A, hA⟩ := hzero (ε / 2) (half_pos hε)
  refine ⟨A, fun x hx => ?_⟩
  rw [Real.dist_eq, sub_zero]
  have htail : ∀ y ∈ Ioi x, |h y| ≤ ε / 2 := by
    intro y hy
    have hyA : A ≤ y := hx.trans hy.le
    have := hA y hyA
    simpa only [Real.dist_eq, sub_zero] using this.le
  exact lt_of_le_of_lt
    (apm_m02a06_exp_mul_integral_tail_le h (ε / 2) x htail)
    (half_lt_self hε)

lemma apm_m02a06_exp_neg_mul_integral_tail_le
    (h : ℝ → ℝ) (δ A x : ℝ) (hδ : 0 ≤ δ) (hAx : A ≤ x)
    (hh : ∀ y ∈ Ioc A x, |h y| ≤ δ) :
    |Real.exp (-x) * ∫ y in A..x, Real.exp y * h y| ≤ δ := by
  have hg : IntervalIntegrable (fun y : ℝ => δ * Real.exp y)
      MeasureTheory.volume A x :=
    (continuous_const.mul Real.continuous_exp).intervalIntegrable A x
  have hint : |∫ y in A..x, Real.exp y * h y| ≤
      ∫ y in A..x, δ * Real.exp y := by
    simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_of_norm_le
      hAx (by
        filter_upwards with y hy
        rw [Real.norm_eq_abs]
        calc
          |Real.exp y * h y| = Real.exp y * |h y| := by
            rw [abs_mul, abs_of_pos (Real.exp_pos y)]
          _ ≤ Real.exp y * δ := mul_le_mul_of_nonneg_left (hh y hy) (Real.exp_pos y).le
          _ = δ * Real.exp y := mul_comm _ _) hg
  calc
    |Real.exp (-x) * ∫ y in A..x, Real.exp y * h y| =
        Real.exp (-x) * |∫ y in A..x, Real.exp y * h y| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos (-x))]
    _ ≤ Real.exp (-x) * (∫ y in A..x, δ * Real.exp y) :=
      mul_le_mul_of_nonneg_left hint (Real.exp_pos (-x)).le
    _ = δ * (1 - Real.exp (A - x)) := by
      rw [intervalIntegral.integral_const_mul, integral_exp]
      rw [show Real.exp (-x) * (δ * (Real.exp x - Real.exp A)) =
        δ * (Real.exp (-x) * Real.exp x - Real.exp (-x) * Real.exp A) by ring,
        ← Real.exp_add, ← Real.exp_add]
      simp only [neg_add_cancel, Real.exp_zero, sub_eq_add_neg]
      ring_nf
    _ ≤ δ := by
      have hexp : 0 ≤ Real.exp (A - x) := (Real.exp_pos _).le
      nlinarith

lemma apm_m02a06_exp_neg_mul_integral_lower_tendsto
    (h : ℝ → ℝ) (hh : Continuous h)
    (hzero : Filter.Tendsto h Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun x : ℝ => Real.exp (-x) * ∫ y in (0 : ℝ)..x, Real.exp y * h y)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop] at hzero ⊢
  intro ε hε
  obtain ⟨A, hA⟩ := hzero (ε / 2) (half_pos hε)
  have hfix : Filter.Tendsto
      (fun x : ℝ => Real.exp (-x) * ∫ y in (0 : ℝ)..A, Real.exp y * h y)
      Filter.atTop (nhds 0) :=
    by simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.mul_const
      (∫ y in (0 : ℝ)..A, Real.exp y * h y))
  rw [Metric.tendsto_atTop] at hfix
  obtain ⟨X, hX⟩ := hfix (ε / 2) (half_pos hε)
  refine ⟨max A X, fun x hx => ?_⟩
  have hAx : A ≤ x := (le_max_left A X).trans hx
  have hXx : X ≤ x := (le_max_right A X).trans hx
  have htail : ∀ y ∈ Ioc A x, |h y| ≤ ε / 2 := by
    intro y hy
    have := hA y hy.1.le
    simpa only [Real.dist_eq, sub_zero] using this.le
  have hi0 : IntervalIntegrable (fun y : ℝ => Real.exp y * h y)
      MeasureTheory.volume 0 A :=
    (Real.continuous_exp.mul hh).intervalIntegrable 0 A
  have hi1 : IntervalIntegrable (fun y : ℝ => Real.exp y * h y)
      MeasureTheory.volume A x :=
    (Real.continuous_exp.mul hh).intervalIntegrable A x
  have hsplit : (∫ y in (0 : ℝ)..x, Real.exp y * h y) =
      (∫ y in (0 : ℝ)..A, Real.exp y * h y) +
        ∫ y in A..x, Real.exp y * h y :=
    (intervalIntegral.integral_add_adjacent_intervals hi0 hi1).symm
  rw [hsplit, mul_add]
  calc
    dist (Real.exp (-x) * (∫ y in (0 : ℝ)..A, Real.exp y * h y) +
        Real.exp (-x) * (∫ y in A..x, Real.exp y * h y)) 0 =
        |Real.exp (-x) * (∫ y in (0 : ℝ)..A, Real.exp y * h y) +
          Real.exp (-x) * (∫ y in A..x, Real.exp y * h y)| := by
      rw [Real.dist_eq, sub_zero]
    _ ≤ |Real.exp (-x) * (∫ y in (0 : ℝ)..A, Real.exp y * h y)| +
        |Real.exp (-x) * (∫ y in A..x, Real.exp y * h y)| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le (by
        simpa only [Real.dist_eq, sub_zero] using hX x hXx)
      (apm_m02a06_exp_neg_mul_integral_tail_le h (ε / 2) A x
        (half_pos hε).le hAx htail)
    _ = ε := by ring

lemma apm_m02a06_greenSplit_tendsto_atTop
    (h : ℝ → ℝ) (B : ℝ) (hh : Continuous h)
    (hB : ∀ y ∈ Ioi (0 : ℝ), |h y| ≤ B)
    (hzero : Filter.Tendsto h Filter.atTop (nhds 0)) :
    Filter.Tendsto (apm_m02a06_greenSplit h) Filter.atTop (nhds 0) := by
  let total := ∫ y in Ioi (0 : ℝ), Real.exp (-y) * h y
  have hp := apm_m02a06_exp_neg_mul_integral_lower_tendsto h hh hzero
  have hu := apm_m02a06_exp_mul_integral_tail_tendsto h hzero
  have hu' : Filter.Tendsto
      (fun x : ℝ => Real.exp x *
        (total - ∫ y in (0 : ℝ)..x, Real.exp (-y) * h y))
      Filter.atTop (nhds 0) := by
    apply hu.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [apm_m02a06_integral_exp_neg_mul_Ioi_eq h B x hh hB hx]
  have hen := Real.tendsto_exp_neg_atTop_nhds_zero
  have hconst : Filter.Tendsto (fun x : ℝ => Real.exp (-x) * total)
      Filter.atTop (nhds 0) := by
    simpa using hen.mul_const total
  have hall := ((hp.add hu').sub hconst).const_mul (1 / 2 : ℝ)
  unfold apm_m02a06_greenSplit
  simpa [total] using hall

lemma apm_m02a06_integral_greenKernel_mul_lower
    (h : ℝ → ℝ) (x : ℝ) (hx : 0 ≤ x) (hh : Continuous h) :
    (∫ y in Ioc (0 : ℝ) x, apm_m02a06_greenKernel x y * h y) =
      (1 / 2 : ℝ) * (Real.exp (-x) * (∫ y in (0 : ℝ)..x, Real.exp y * h y) -
        Real.exp (-x) * ∫ y in (0 : ℝ)..x, Real.exp (-y) * h y) := by
  rw [← intervalIntegral.integral_of_le hx]
  have hpos : IntervalIntegrable (fun y : ℝ => Real.exp y * h y)
      MeasureTheory.volume 0 x := by
    simpa only [Pi.mul_apply] using
      ((Real.continuous_exp.comp continuous_id).mul hh).intervalIntegrable 0 x
  have hneg : IntervalIntegrable (fun y : ℝ => Real.exp (-y) * h y)
      MeasureTheory.volume 0 x := by
    simpa only [Pi.mul_apply] using
      ((Real.continuous_exp.comp continuous_neg).mul hh).intervalIntegrable 0 x
  have hA : IntervalIntegrable
      (fun y : ℝ => Real.exp (-x) * (Real.exp y * h y)) MeasureTheory.volume 0 x :=
    hpos.const_mul _
  have hB : IntervalIntegrable
      (fun y : ℝ => Real.exp (-x) * (Real.exp (-y) * h y)) MeasureTheory.volume 0 x :=
    hneg.const_mul _
  calc
    (∫ y in (0 : ℝ)..x, apm_m02a06_greenKernel x y * h y) =
        ∫ y in (0 : ℝ)..x, (1 / 2 : ℝ) *
          (Real.exp (-x) * (Real.exp y * h y) -
            Real.exp (-x) * (Real.exp (-y) * h y)) := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [uIcc_of_le hx] at hy
      change apm_m02a06_greenKernel x y * h y = (1 / 2 : ℝ) *
        (Real.exp (-x) * (Real.exp y * h y) - Real.exp (-x) * (Real.exp (-y) * h y))
      rw [apm_m02a06_greenKernel_of_le hy.2]
      rw [show -(x - y) = -x + y by ring, show -(x + y) = -x + -y by ring,
        Real.exp_add, Real.exp_add]
      ring_nf
    _ = (1 / 2 : ℝ) * (Real.exp (-x) * (∫ y in (0 : ℝ)..x, Real.exp y * h y) -
        Real.exp (-x) * ∫ y in (0 : ℝ)..x, Real.exp (-y) * h y) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub hA hB,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]

lemma apm_m02a06_integral_greenKernel_mul_upper
    (h : ℝ → ℝ) (B x : ℝ) (hx : 0 ≤ x) (hh : Continuous h)
    (hB : ∀ y ∈ Ioi (0 : ℝ), |h y| ≤ B) :
    (∫ y in Ioi x, apm_m02a06_greenKernel x y * h y) =
      (1 / 2 : ℝ) * (Real.exp x * (∫ y in Ioi x, Real.exp (-y) * h y) -
        Real.exp (-x) * ∫ y in Ioi x, Real.exp (-y) * h y) := by
  have hi0 := apm_m02a06_integrableOn_exp_neg_mul h B hh hB
  have hix := hi0.mono_set (Ioi_subset_Ioi hx)
  have hA : MeasureTheory.IntegrableOn
      (fun y : ℝ => Real.exp x * (Real.exp (-y) * h y)) (Ioi x) := hix.const_mul _
  have hB' : MeasureTheory.IntegrableOn
      (fun y : ℝ => Real.exp (-x) * (Real.exp (-y) * h y)) (Ioi x) := hix.const_mul _
  calc
    (∫ y in Ioi x, apm_m02a06_greenKernel x y * h y) =
        ∫ y in Ioi x, (1 / 2 : ℝ) *
          (Real.exp x * (Real.exp (-y) * h y) -
            Real.exp (-x) * (Real.exp (-y) * h y)) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      change apm_m02a06_greenKernel x y * h y = (1 / 2 : ℝ) *
        (Real.exp x * (Real.exp (-y) * h y) - Real.exp (-x) * (Real.exp (-y) * h y))
      rw [apm_m02a06_greenKernel_of_ge hy.le]
      rw [show -(y - x) = x + -y by ring, show -(x + y) = -x + -y by ring,
        Real.exp_add, Real.exp_add]
      ring_nf
    _ = (1 / 2 : ℝ) * (Real.exp x * (∫ y in Ioi x, Real.exp (-y) * h y) -
        Real.exp (-x) * ∫ y in Ioi x, Real.exp (-y) * h y) := by
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_sub hA hB',
        MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]

lemma apm_m02a06_integrableOn_greenKernel_mul
    (h : ℝ → ℝ) (B x : ℝ) (hx : 0 ≤ x) (hh : Continuous h)
    (hB : ∀ y ∈ Ici (0 : ℝ), |h y| ≤ B) :
    MeasureTheory.IntegrableOn
      (fun y => apm_m02a06_greenKernel x y * h y) (Ici 0) := by
  have hi : MeasureTheory.IntegrableOn
      (fun y => h y * apm_m02a06_greenKernel x y) (Ici 0) :=
    (apm_m02a06_integrableOn_greenKernel x hx).bdd_mul hh.aestronglyMeasurable (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with y hy
      simpa only [Real.norm_eq_abs] using hB y hy)
  simpa only [mul_comm] using hi

/-- The kernel-integral and moving-endpoint presentations of the Green
operator agree on the half-line. -/
lemma apm_m02a06_integral_greenKernel_mul_eq_greenSplit
    (h : ℝ → ℝ) (B x : ℝ) (hx : 0 ≤ x) (hh : Continuous h)
    (hB : ∀ y ∈ Ici (0 : ℝ), |h y| ≤ B) :
    (∫ y in Ici (0 : ℝ), apm_m02a06_greenKernel x y * h y) =
      apm_m02a06_greenSplit h x := by
  have hi := apm_m02a06_integrableOn_greenKernel_mul h B x hx hh hB
  have htail : ∀ y ∈ Ioi (0 : ℝ), |h y| ≤ B :=
    fun y hy => hB y (show 0 ≤ y from le_of_lt hy)
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi, ← Ioc_union_Ioi_eq_Ioi hx,
    MeasureTheory.setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hi.mono_set (Ioc_subset_Ioi_self.trans Ioi_subset_Ici_self))
      (hi.mono_set (Ioi_subset_Ioi hx |>.trans Ioi_subset_Ici_self)),
    apm_m02a06_integral_greenKernel_mul_lower h x hx hh,
    apm_m02a06_integral_greenKernel_mul_upper h B x hx hh htail,
    apm_m02a06_integral_exp_neg_mul_Ioi_eq h B x hh htail hx]
  unfold apm_m02a06_greenSplit
  ring

lemma apm_m02a06_continuousOn_integral_greenKernel_mul
    (h : ℝ → ℝ) (B : ℝ) (hh : Continuous h)
    (hB : ∀ y ∈ Ici (0 : ℝ), |h y| ≤ B) :
    ContinuousOn (fun x => ∫ y in Ici (0 : ℝ),
      apm_m02a06_greenKernel x y * h y) (Ici 0) := by
  refine (apm_m02a06_greenSplit_continuous h hh).continuousOn.congr ?_
  intro x hx
  exact apm_m02a06_integral_greenKernel_mul_eq_greenSplit h B x hx hh hB

lemma apm_m02a06_greenTransform_continuousOn_of_source
    (ε : ℝ) (f u : ℝ → ℝ) (B : ℝ)
    (hsource_cont : Continuous fun y => f y + ε * (u y) ^ 2)
    (hsource_bound : ∀ y ∈ Ici (0 : ℝ), |f y + ε * (u y) ^ 2| ≤ B) :
    ContinuousOn (apm_m02a06_greenTransform ε f u) (Ici 0) := by
  apply (by fun_prop : Continuous fun x : ℝ => Real.exp (-x)).continuousOn.add
  exact apm_m02a06_continuousOn_integral_greenKernel_mul
    (fun y => f y + ε * (u y) ^ 2) B hsource_cont hsource_bound

lemma apm_m02a06_greenTransform_abs_le
    (ε C R : ℝ) (f u : ℝ → ℝ) (x : ℝ)
    (hx : 0 ≤ x) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hf : ∀ y ∈ Ici (0 : ℝ), |f y| ≤ C)
    (hu : ∀ y ∈ Ici (0 : ℝ), |u y| ≤ R) :
    |apm_m02a06_greenTransform ε f u x| ≤
      Real.exp (-x) + (C + ε * R ^ 2) := by
  unfold apm_m02a06_greenTransform
  calc
    |Real.exp (-x) + ∫ y in Ici (0 : ℝ),
        apm_m02a06_greenKernel x y * (f y + ε * (u y) ^ 2)| ≤
        |Real.exp (-x)| + |∫ y in Ici (0 : ℝ),
          apm_m02a06_greenKernel x y * (f y + ε * (u y) ^ 2)| := abs_add_le _ _
    _ = Real.exp (-x) + |∫ y in Ici (0 : ℝ),
          apm_m02a06_greenKernel x y * (f y + ε * (u y) ^ 2)| := by
      rw [abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-x) + (C + ε * R ^ 2) := add_le_add_right
      (apm_m02a06_greenKernel_integral_mul_le x (C + ε * R ^ 2)
        (fun y => f y + ε * (u y) ^ 2) hx (by positivity) (by
          intro y hy
          calc
            |f y + ε * (u y) ^ 2| ≤ |f y| + |ε * (u y) ^ 2| := abs_add_le _ _
            _ = |f y| + ε * (u y) ^ 2 := by rw [abs_mul, abs_of_nonneg hε, abs_sq]
            _ ≤ C + ε * R ^ 2 := add_le_add (hf y hy)
              (mul_le_mul_of_nonneg_left
                ((sq_le_sq).2 (by simpa [abs_of_nonneg hR] using hu y hy)) hε))) _

lemma apm_m02a06_greenTransform_maps_ball
    (f u : ℝ → ℝ) (C ε x : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hε_small : ε < 1 / (4 * (1 + C))) (hx : 0 ≤ x)
    (hf : ∀ y ∈ Ici (0 : ℝ), |f y| ≤ C)
    (hu : ∀ y ∈ Ici (0 : ℝ), |u y| ≤ 2 * (1 + C)) :
    |apm_m02a06_greenTransform ε f u x| < 2 * (1 + C) := by
  have hbase : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)
  have hq := apm_m02a06_contraction_constant_lt_one C ε hC hε_small
  have hbound := apm_m02a06_greenTransform_abs_le ε C (2 * (1 + C)) f u x
    hx hε.le hC (by positivity) hf hu
  nlinarith [mul_pos (show 0 < 4 * (1 + C) by positivity) hε]

lemma apm_m02a06_greenTransform_sub_le
    (f u v : ℝ → ℝ) (C ε D x : ℝ) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hD : 0 ≤ D) (hx : 0 ≤ x)
    (hu : ∀ y ∈ Ici (0 : ℝ), |u y| ≤ 2 * (1 + C))
    (hv : ∀ y ∈ Ici (0 : ℝ), |v y| ≤ 2 * (1 + C))
    (huv : ∀ y ∈ Ici (0 : ℝ), |u y - v y| ≤ D)
    (huint : MeasureTheory.IntegrableOn
      (fun y => apm_m02a06_greenKernel x y * (f y + ε * (u y) ^ 2)) (Ici 0))
    (hvint : MeasureTheory.IntegrableOn
      (fun y => apm_m02a06_greenKernel x y * (f y + ε * (v y) ^ 2)) (Ici 0)) :
    |apm_m02a06_greenTransform ε f u x - apm_m02a06_greenTransform ε f v x| ≤
      (4 * ε * (1 + C)) * D := by
  unfold apm_m02a06_greenTransform
  rw [add_sub_add_left_eq_sub, ← MeasureTheory.integral_sub huint hvint]
  have heq :
      (∫ y in Ici (0 : ℝ),
        apm_m02a06_greenKernel x y * (f y + ε * (u y) ^ 2) -
          apm_m02a06_greenKernel x y * (f y + ε * (v y) ^ 2)) =
      ∫ y in Ici (0 : ℝ), apm_m02a06_greenKernel x y *
        ((f y + ε * (u y) ^ 2) - (f y + ε * (v y) ^ 2)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ici
    intro y _
    ring
  rw [heq]
  refine apm_m02a06_greenKernel_integral_mul_le x (4 * ε * (1 + C) * D)
    (fun y => (f y + ε * (u y) ^ 2) - (f y + ε * (v y) ^ 2)) hx
    (mul_nonneg (by positivity) hD) ?_
  intro y hy
  change |(f y + ε * (u y) ^ 2) - (f y + ε * (v y) ^ 2)| ≤ _
  rw [add_sub_add_left_eq_sub]
  calc
    |ε * (u y) ^ 2 - ε * (v y) ^ 2| ≤
        (4 * ε * (1 + C)) * |u y - v y| :=
      apm_m02a06_quadratic_lipschitz C ε (u y) (v y) hε (hu y hy) (hv y hy)
    _ ≤ (4 * ε * (1 + C)) * D :=
      mul_le_mul_of_nonneg_left (huv y hy) (by positivity)

lemma apm_m02a06_integrableOn_greenTransform_source
    (f : ℝ → ℝ) (C ε x : ℝ) (u : apm_m02a06_Ball C)
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hx : 0 ≤ x) (hf_cont : Continuous f)
    (hf_bound : ∀ y ∈ Ici (0 : ℝ), |f y| ≤ C) :
    MeasureTheory.IntegrableOn
      (fun y => apm_m02a06_greenKernel x y *
        (f y + ε * (apm_m02a06_extend u.1 y) ^ 2)) (Ici 0) := by
  apply apm_m02a06_integrableOn_greenKernel_mul
    (fun y => f y + ε * (apm_m02a06_extend u.1 y) ^ 2)
    (C + ε * (2 * (1 + C)) ^ 2) x hx
    (apm_m02a06_source_continuous ε f hf_cont u.1)
  intro y hy
  exact apm_m02a06_source_bound C ε f u hC hε hf_bound y hy

lemma apm_m02a06_greenTransform_extend_sub_le
    (f : ℝ → ℝ) (C ε x : ℝ) (u v : apm_m02a06_Ball C)
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hx : 0 ≤ x) (hf_cont : Continuous f)
    (hf_bound : ∀ y ∈ Ici (0 : ℝ), |f y| ≤ C) :
    |apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1) x -
        apm_m02a06_greenTransform ε f (apm_m02a06_extend v.1) x| ≤
      (4 * ε * (1 + C)) * dist u v := by
  apply apm_m02a06_greenTransform_sub_le f (apm_m02a06_extend u.1)
    (apm_m02a06_extend v.1) C ε (dist u v) x hC hε dist_nonneg hx
    (fun y _ => apm_m02a06_extend_ball_bound C u y)
    (fun y _ => apm_m02a06_extend_ball_bound C v y)
    (fun y _ => apm_m02a06_extend_sub_le_dist C u v y)
    (apm_m02a06_integrableOn_greenTransform_source f C ε x u hC hε hx hf_cont hf_bound)
    (apm_m02a06_integrableOn_greenTransform_source f C ε x v hC hε hx hf_cont hf_bound)

lemma apm_m02a06_greenTransform_extend_maps_ball
    (f : ℝ → ℝ) (C ε x : ℝ) (u : apm_m02a06_Ball C)
    (hC : 0 ≤ C) (hε : 0 < ε) (hε_small : ε < 1 / (4 * (1 + C)))
    (hx : 0 ≤ x) (hf_bound : ∀ y ∈ Ici (0 : ℝ), |f y| ≤ C) :
    |apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1) x| < 2 * (1 + C) := by
  apply apm_m02a06_greenTransform_maps_ball f (apm_m02a06_extend u.1)
    C ε x hC hε hε_small hx hf_bound
  intro y _
  exact apm_m02a06_extend_ball_bound C u y

lemma apm_m02a06_greenTransform_extend_continuousOn
    (f : ℝ → ℝ) (C ε : ℝ) (u : apm_m02a06_Ball C)
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hf_cont : Continuous f)
    (hf_bound : ∀ y ∈ Ici (0 : ℝ), |f y| ≤ C) :
    ContinuousOn
      (apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1)) (Ici 0) := by
  apply apm_m02a06_greenTransform_continuousOn_of_source ε f
    (apm_m02a06_extend u.1) (C + ε * (2 * (1 + C)) ^ 2)
    (apm_m02a06_source_continuous ε f hf_cont u.1)
  intro y hy
  exact apm_m02a06_source_bound C ε f u hC hε hf_bound y hy

lemma apm_m02a06_greenTransform_extend_tendsto_atTop
    (f : ℝ → ℝ) (C ε : ℝ) (u : apm_m02a06_Ball C)
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hf_cont : Continuous f)
    (hf_zero : Tendsto f atTop (nhds 0))
    (hf_bound : ∀ y ∈ Ici (0 : ℝ), |f y| ≤ C) :
    Tendsto (apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1))
      atTop (nhds 0) := by
  let source := fun y => f y + ε * (apm_m02a06_extend u.1 y) ^ 2
  have hscont : Continuous source :=
    apm_m02a06_source_continuous ε f hf_cont u.1
  have hsbound : ∀ y ∈ Ioi (0 : ℝ), |source y| ≤
      C + ε * (2 * (1 + C)) ^ 2 := by
    intro y hy
    exact apm_m02a06_source_bound C ε f u hC hε hf_bound y hy.le
  have hszero : Tendsto source atTop (nhds 0) :=
    apm_m02a06_source_tendsto_atTop ε f hf_zero u.1
  have hsplit := apm_m02a06_greenSplit_tendsto_atTop source
    (C + ε * (2 * (1 + C)) ^ 2) hscont hsbound hszero
  have hsum : Tendsto (fun x => Real.exp (-x) + apm_m02a06_greenSplit source x)
      atTop (nhds 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.add hsplit
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  unfold apm_m02a06_greenTransform
  rw [apm_m02a06_integral_greenKernel_mul_eq_greenSplit source
    (C + ε * (2 * (1 + C)) ^ 2) x hx hscont (by
      intro y hy
      exact apm_m02a06_source_bound C ε f u hC hε hf_bound y hy)]

noncomputable def apm_m02a06_greenTransformFunctionSpace
    (f : ℝ → ℝ) (C ε : ℝ) (u : apm_m02a06_Ball C)
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hf_cont : Continuous f)
    (hf_bound : ∀ y ∈ Ici (0 : ℝ), |f y| ≤ C)
    (hzero : Tendsto
      (apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1)) atTop (nhds 0)) :
    apm_m02a06_FunctionSpace :=
  apm_m02a06_toFunctionSpace
    (apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1))
    (apm_m02a06_greenTransform_extend_continuousOn f C ε u hC hε hf_cont hf_bound)
    hzero

@[simp] lemma apm_m02a06_greenTransformFunctionSpace_apply
    (f : ℝ → ℝ) (C ε : ℝ) (u : apm_m02a06_Ball C)
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hf_cont : Continuous f)
    (hf_bound : ∀ y ∈ Ici (0 : ℝ), |f y| ≤ C)
    (hzero : Tendsto
      (apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1)) atTop (nhds 0))
    (x : Ici (0 : ℝ)) :
    apm_m02a06_greenTransformFunctionSpace f C ε u hC hε hf_cont hf_bound hzero x =
      apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1) x := rfl

noncomputable def apm_m02a06_greenBallMap
    (f : ℝ → ℝ) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hε_small : ε < 1 / (4 * (1 + C))) (hf_cont : Continuous f)
    (hf_bound : ∀ y ∈ Ici (0 : ℝ), |f y| ≤ C)
    (hzero : ∀ u : apm_m02a06_Ball C, Tendsto
      (apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1)) atTop (nhds 0)) :
    apm_m02a06_Ball C → apm_m02a06_Ball C := fun u => by
  let Tu := apm_m02a06_greenTransformFunctionSpace f C ε u hC hε.le hf_cont hf_bound
    (hzero u)
  refine ⟨Tu, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right,
    ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
    BoundedContinuousFunction.norm_le (by positivity)]
  intro x
  simpa only [Real.norm_eq_abs, Tu] using
    (apm_m02a06_greenTransform_extend_maps_ball f C ε x u hC hε hε_small
      x.property hf_bound).le

@[simp] lemma apm_m02a06_greenBallMap_apply
    (f : ℝ → ℝ) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hε_small : ε < 1 / (4 * (1 + C))) (hf_cont : Continuous f)
    (hf_bound : ∀ y ∈ Ici (0 : ℝ), |f y| ≤ C)
    (hzero : ∀ u : apm_m02a06_Ball C, Tendsto
      (apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1)) atTop (nhds 0))
    (u : apm_m02a06_Ball C) (x : Ici (0 : ℝ)) :
    (apm_m02a06_greenBallMap f C ε hC hε hε_small hf_cont hf_bound hzero u).1 x =
      apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1) x := rfl

lemma apm_m02a06_greenBallMap_dist_le
    (f : ℝ → ℝ) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hε_small : ε < 1 / (4 * (1 + C))) (hf_cont : Continuous f)
    (hf_bound : ∀ y ∈ Ici (0 : ℝ), |f y| ≤ C)
    (hzero : ∀ u : apm_m02a06_Ball C, Tendsto
      (apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1)) atTop (nhds 0))
    (u v : apm_m02a06_Ball C) :
    dist (apm_m02a06_greenBallMap f C ε hC hε hε_small hf_cont hf_bound hzero u)
        (apm_m02a06_greenBallMap f C ε hC hε hε_small hf_cont hf_bound hzero v) ≤
      (4 * ε * (1 + C)) * dist u v := by
  rw [Subtype.dist_eq, ← ZeroAtInftyContinuousMap.dist_toBCF_eq_dist]
  apply (BoundedContinuousFunction.dist_le (by positivity)).2
  intro x
  simpa only [Real.dist_eq, apm_m02a06_greenBallMap_apply] using
    apm_m02a06_greenTransform_extend_sub_le f C ε x u v hC hε.le x.property
      hf_cont hf_bound

def apm_m02a06_contractionK (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 ≤ ε) : NNReal :=
  ⟨4 * ε * (1 + C), by positivity⟩

lemma apm_m02a06_greenBallMap_contracting
    (f : ℝ → ℝ) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hε_small : ε < 1 / (4 * (1 + C))) (hf_cont : Continuous f)
    (hf_bound : ∀ y ∈ Ici (0 : ℝ), |f y| ≤ C)
    (hzero : ∀ u : apm_m02a06_Ball C, Tendsto
      (apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1)) atTop (nhds 0)) :
    ContractingWith (apm_m02a06_contractionK C ε hC hε.le)
      (apm_m02a06_greenBallMap f C ε hC hε hε_small hf_cont hf_bound hzero) := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
  · exact_mod_cast apm_m02a06_contraction_constant_lt_one C ε hC hε_small
  · simpa [apm_m02a06_contractionK] using
      apm_m02a06_greenBallMap_dist_le f C ε hC hε hε_small hf_cont hf_bound
        hzero u v

noncomputable def apm_m02a06_greenFixedPoint
    (f : ℝ → ℝ) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hε_small : ε < 1 / (4 * (1 + C))) (hf_cont : Continuous f)
    (hf_bound : ∀ y ∈ Ici (0 : ℝ), |f y| ≤ C)
    (hzero : ∀ u : apm_m02a06_Ball C, Tendsto
      (apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1)) atTop (nhds 0)) :
    apm_m02a06_Ball C := by
  letI : CompleteSpace (apm_m02a06_Ball C) :=
    (apm_m02a06_ball_isComplete C).completeSpace_coe
  letI : Nonempty (apm_m02a06_Ball C) := apm_m02a06_ball_nonempty C hC
  exact ContractingWith.fixedPoint
    (apm_m02a06_greenBallMap f C ε hC hε hε_small hf_cont hf_bound hzero)
    (apm_m02a06_greenBallMap_contracting f C ε hC hε hε_small hf_cont hf_bound hzero)

lemma apm_m02a06_greenFixedPoint_eq
    (f : ℝ → ℝ) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hε_small : ε < 1 / (4 * (1 + C))) (hf_cont : Continuous f)
    (hf_bound : ∀ y ∈ Ici (0 : ℝ), |f y| ≤ C)
    (hzero : ∀ u : apm_m02a06_Ball C, Tendsto
      (apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1)) atTop (nhds 0)) :
    apm_m02a06_greenBallMap f C ε hC hε hε_small hf_cont hf_bound hzero
        (apm_m02a06_greenFixedPoint f C ε hC hε hε_small hf_cont hf_bound hzero) =
      apm_m02a06_greenFixedPoint f C ε hC hε hε_small hf_cont hf_bound hzero := by
  letI : CompleteSpace (apm_m02a06_Ball C) :=
    (apm_m02a06_ball_isComplete C).completeSpace_coe
  letI : Nonempty (apm_m02a06_Ball C) := apm_m02a06_ball_nonempty C hC
  exact (apm_m02a06_greenBallMap_contracting f C ε hC hε hε_small hf_cont hf_bound
    hzero).fixedPoint_isFixedPt

lemma apm_m02a06_greenFixedPoint_apply
    (f : ℝ → ℝ) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hε_small : ε < 1 / (4 * (1 + C))) (hf_cont : Continuous f)
    (hf_bound : ∀ y ∈ Ici (0 : ℝ), |f y| ≤ C)
    (hzero : ∀ u : apm_m02a06_Ball C, Tendsto
      (apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1)) atTop (nhds 0))
    (x : Ici (0 : ℝ)) :
    (apm_m02a06_greenFixedPoint f C ε hC hε hε_small hf_cont hf_bound hzero).1 x =
      apm_m02a06_greenTransform ε f
        (apm_m02a06_extend
          (apm_m02a06_greenFixedPoint f C ε hC hε hε_small hf_cont hf_bound hzero).1) x := by
  have hfix := apm_m02a06_greenFixedPoint_eq f C ε hC hε hε_small hf_cont hf_bound hzero
  exact DFunLike.congr_fun (congrArg Subtype.val hfix).symm x

lemma apm_m02a06_eq_greenFixedPoint_of_eq
    (f : ℝ → ℝ) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hε_small : ε < 1 / (4 * (1 + C))) (hf_cont : Continuous f)
    (hf_bound : ∀ y ∈ Ici (0 : ℝ), |f y| ≤ C)
    (hzero : ∀ u : apm_m02a06_Ball C, Tendsto
      (apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1)) atTop (nhds 0))
    (u : apm_m02a06_Ball C)
    (hu : apm_m02a06_greenBallMap f C ε hC hε hε_small hf_cont hf_bound hzero u = u) :
    u = apm_m02a06_greenFixedPoint f C ε hC hε hε_small hf_cont hf_bound hzero := by
  letI : CompleteSpace (apm_m02a06_Ball C) :=
    (apm_m02a06_ball_isComplete C).completeSpace_coe
  letI : Nonempty (apm_m02a06_Ball C) := apm_m02a06_ball_nonempty C hC
  exact (apm_m02a06_greenBallMap_contracting f C ε hC hε hε_small hf_cont hf_bound
    hzero).fixedPoint_unique hu

lemma apm_m02a06_greenFixedPoint_extend_tendsto
    (f : ℝ → ℝ) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hε_small : ε < 1 / (4 * (1 + C))) (hf_cont : Continuous f)
    (hf_bound : ∀ y ∈ Ici (0 : ℝ), |f y| ≤ C)
    (hzero : ∀ u : apm_m02a06_Ball C, Tendsto
      (apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1)) atTop (nhds 0)) :
    Tendsto (apm_m02a06_extend
      (apm_m02a06_greenFixedPoint f C ε hC hε hε_small hf_cont hf_bound hzero).1)
      atTop (nhds 0) :=
  apm_m02a06_extend_tendsto_atTop _

lemma apm_m02a06_greenFixedPoint_extend_bound
    (f : ℝ → ℝ) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hε_small : ε < 1 / (4 * (1 + C))) (hf_cont : Continuous f)
    (hf_bound : ∀ y ∈ Ici (0 : ℝ), |f y| ≤ C)
    (hzero : ∀ u : apm_m02a06_Ball C, Tendsto
      (apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1)) atTop (nhds 0))
    (x : ℝ) :
    |apm_m02a06_extend
      (apm_m02a06_greenFixedPoint f C ε hC hε hε_small hf_cont hf_bound hzero).1 x| ≤
      2 * (1 + C) :=
  apm_m02a06_extend_ball_bound C _ x

lemma apm_m02a06_greenFixedPoint_extend_zero
    (f : ℝ → ℝ) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hε_small : ε < 1 / (4 * (1 + C))) (hf_cont : Continuous f)
    (hf_bound : ∀ y ∈ Ici (0 : ℝ), |f y| ≤ C)
    (hzero : ∀ u : apm_m02a06_Ball C, Tendsto
      (apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1)) atTop (nhds 0)) :
    apm_m02a06_extend
      (apm_m02a06_greenFixedPoint f C ε hC hε hε_small hf_cont hf_bound hzero).1 0 = 1 := by
  have hfix := apm_m02a06_greenFixedPoint_apply f C ε hC hε hε_small hf_cont
    hf_bound hzero (⟨0, show (0 : ℝ) ≤ 0 from le_rfl⟩ : Ici (0 : ℝ))
  have hkernel : (∫ y in Ici (0 : ℝ), apm_m02a06_greenKernel 0 y *
      (f y + ε * (apm_m02a06_extend
        (apm_m02a06_greenFixedPoint f C ε hC hε hε_small hf_cont hf_bound hzero).1 y) ^ 2)) =
      0 := by
    apply MeasureTheory.integral_eq_zero_of_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with y hy
    simp only [Pi.zero_apply, apm_m02a06_greenKernel_zero_left hy, zero_mul]
  rw [apm_m02a06_extend_of_nonneg
    (apm_m02a06_greenFixedPoint f C ε hC hε hε_small hf_cont hf_bound hzero).1 le_rfl,
    hfix]
  simp [apm_m02a06_greenTransform, hkernel]

lemma apm_m02a06_greenFixedPoint_extend_eq_split
    (f : ℝ → ℝ) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hε_small : ε < 1 / (4 * (1 + C))) (hf_cont : Continuous f)
    (hf_bound : ∀ y ∈ Ici (0 : ℝ), |f y| ≤ C)
    (hzero : ∀ u : apm_m02a06_Ball C, Tendsto
      (apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1)) atTop (nhds 0))
    (x : ℝ) (hx : 0 ≤ x) :
    apm_m02a06_extend
        (apm_m02a06_greenFixedPoint f C ε hC hε hε_small hf_cont hf_bound hzero).1 x =
      Real.exp (-x) + apm_m02a06_greenSplit
        (fun y => f y + ε * (apm_m02a06_extend
          (apm_m02a06_greenFixedPoint f C ε hC hε hε_small hf_cont hf_bound hzero).1 y) ^ 2) x := by
  let u := apm_m02a06_greenFixedPoint f C ε hC hε hε_small hf_cont hf_bound hzero
  have hsource_cont := apm_m02a06_source_continuous ε f hf_cont u.1
  have hsource_bound : ∀ y ∈ Ici (0 : ℝ),
      |f y + ε * (apm_m02a06_extend u.1 y) ^ 2| ≤
        C + ε * (2 * (1 + C)) ^ 2 := fun y hy =>
    apm_m02a06_source_bound C ε f u hC hε.le hf_bound y hy
  rw [apm_m02a06_extend_of_nonneg u.1 hx,
    apm_m02a06_greenFixedPoint_apply f C ε hC hε hε_small hf_cont hf_bound hzero
      ⟨x, hx⟩]
  unfold apm_m02a06_greenTransform
  rw [apm_m02a06_integral_greenKernel_mul_eq_greenSplit
    (fun y => f y + ε * (apm_m02a06_extend u.1 y) ^ 2)
    (C + ε * (2 * (1 + C)) ^ 2) x hx hsource_cont hsource_bound]

lemma apm_m02a06_greenFixedPoint_extend_contDiffOn
    (f : ℝ → ℝ) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hε_small : ε < 1 / (4 * (1 + C))) (hf_smooth : ContDiff ℝ ∞ f)
    (hf_bound : ∀ y ∈ Ici (0 : ℝ), |f y| ≤ C)
    (hzero : ∀ u : apm_m02a06_Ball C, Tendsto
      (apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1)) atTop (nhds 0)) :
    ContDiffOn ℝ 2 (apm_m02a06_extend
      (apm_m02a06_greenFixedPoint f C ε hC hε hε_small hf_smooth.continuous
        hf_bound hzero).1) (Ici 0) := by
  let u := apm_m02a06_greenFixedPoint f C ε hC hε hε_small hf_smooth.continuous
    hf_bound hzero
  let source := fun y => f y + ε * (apm_m02a06_extend u.1 y) ^ 2
  have hscont : Continuous source := apm_m02a06_source_continuous ε f hf_smooth.continuous u.1
  have hexp : ContDiff ℝ 2 (fun x : ℝ => Real.exp (-x)) := by fun_prop
  have hrhs : ContDiff ℝ 2 (fun x => Real.exp (-x) + apm_m02a06_greenSplit source x) :=
    hexp.add (apm_m02a06_greenSplit_contDiff_two source hscont)
  apply hrhs.contDiffOn.congr
  intro x hx
  simpa only [source, u] using
    apm_m02a06_greenFixedPoint_extend_eq_split f C ε hC hε hε_small
      hf_smooth.continuous hf_bound hzero x hx

lemma apm_m02a06_greenFixedPoint_extend_ode
    (f : ℝ → ℝ) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hε_small : ε < 1 / (4 * (1 + C))) (hf_cont : Continuous f)
    (hf_bound : ∀ y ∈ Ici (0 : ℝ), |f y| ≤ C)
    (hzero : ∀ u : apm_m02a06_Ball C, Tendsto
      (apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1)) atTop (nhds 0))
    (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
    -deriv (deriv (apm_m02a06_extend
        (apm_m02a06_greenFixedPoint f C ε hC hε hε_small hf_cont hf_bound hzero).1)) x +
      apm_m02a06_extend
        (apm_m02a06_greenFixedPoint f C ε hC hε hε_small hf_cont hf_bound hzero).1 x -
      ε * (apm_m02a06_extend
        (apm_m02a06_greenFixedPoint f C ε hC hε hε_small hf_cont hf_bound hzero).1 x) ^ 2 =
      f x := by
  let u := apm_m02a06_greenFixedPoint f C ε hC hε hε_small hf_cont hf_bound hzero
  let source := fun y => f y + ε * (apm_m02a06_extend u.1 y) ^ 2
  let rhs := fun y => Real.exp (-y) + apm_m02a06_greenSplit source y
  have hscont : Continuous source := apm_m02a06_source_continuous ε f hf_cont u.1
  have hlocal : apm_m02a06_extend u.1 =ᶠ[nhds x] rhs := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact apm_m02a06_greenFixedPoint_extend_eq_split f C ε hC hε hε_small
      hf_cont hf_bound hzero y hy.le
  have hval : apm_m02a06_extend u.1 x = rhs x := hlocal.self_of_nhds
  have hrhs := apm_m02a06_exp_add_greenSplit_ode source hscont x
  rw [hlocal.deriv.deriv_eq, hval]
  dsimp only [rhs, source] at hval hrhs ⊢
  rw [hval] at hrhs
  linarith

lemma apm_m02a06_exists_solution_of_transform_tendsto
    (f : ℝ → ℝ) (hf_smooth : ContDiff ℝ ∞ f)
    (C : ℝ) (hC : 0 ≤ C) (hf_bound : ∀ x ∈ Ici (0 : ℝ), |f x| ≤ C)
    (ε : ℝ) (hε : 0 < ε) (hε_small : ε < 1 / (4 * (1 + C)))
    (hzero : ∀ u : apm_m02a06_Ball C, Tendsto
      (apm_m02a06_greenTransform ε f (apm_m02a06_extend u.1)) atTop (nhds 0)) :
    ∃ u : ℝ → ℝ,
      apm_m02a06_IsSolution ε f u ∧
      ∀ x ∈ Ici (0 : ℝ), |u x| ≤ 2 * (1 + C) := by
  let p := apm_m02a06_greenFixedPoint f C ε hC hε hε_small hf_smooth.continuous
    hf_bound hzero
  let u := apm_m02a06_extend p.1
  refine ⟨u, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [u, p] using
        apm_m02a06_greenFixedPoint_extend_contDiffOn f C ε hC hε hε_small
          hf_smooth hf_bound hzero
    · intro x hx
      simpa only [u, p] using
        apm_m02a06_greenFixedPoint_extend_ode f C ε hC hε hε_small
          hf_smooth.continuous hf_bound hzero x hx
    · simpa only [u, p] using
        apm_m02a06_greenFixedPoint_extend_zero f C ε hC hε hε_small
          hf_smooth.continuous hf_bound hzero
    · simpa only [u, p] using
        apm_m02a06_greenFixedPoint_extend_tendsto f C ε hC hε hε_small
          hf_smooth.continuous hf_bound hzero
  · intro x _
    simpa only [u, p] using
      apm_m02a06_greenFixedPoint_extend_bound f C ε hC hε hε_small
        hf_smooth.continuous hf_bound hzero x

lemma apm_m02a06_exists_solution
    (f : ℝ → ℝ) (hf_smooth : ContDiff ℝ ∞ f) (hf_compact : HasCompactSupport f)
    (C : ℝ) (hC : 0 ≤ C) (hf_bound : ∀ x ∈ Ici (0 : ℝ), |f x| ≤ C)
    (ε : ℝ) (hε : 0 < ε) (hε_small : ε < 1 / (4 * (1 + C))) :
    ∃ u : ℝ → ℝ,
      apm_m02a06_IsSolution ε f u ∧
      ∀ x ∈ Ici (0 : ℝ), |u x| ≤ 2 * (1 + C) := by
  apply apm_m02a06_exists_solution_of_transform_tendsto f hf_smooth C hC hf_bound
    ε hε hε_small
  intro u
  exact apm_m02a06_greenTransform_extend_tendsto_atTop f C ε u hC hε.le
    hf_smooth.continuous (apm_m02a06_tendsto_zero_of_compactSupport f hf_compact) hf_bound

/-- A classical decaying solution, restricted to the half-line, as an element
of the complete `C₀` carrier. -/
noncomputable def apm_m02a06_solutionFunctionSpace
    (ε : ℝ) (f v : ℝ → ℝ) (hv : apm_m02a06_IsSolution ε f v) :
    apm_m02a06_FunctionSpace :=
  apm_m02a06_toFunctionSpace v hv.1.continuousOn hv.2.2.2

@[simp] lemma apm_m02a06_solutionFunctionSpace_apply
    (ε : ℝ) (f v : ℝ → ℝ) (hv : apm_m02a06_IsSolution ε f v)
    (x : Ici (0 : ℝ)) :
    apm_m02a06_solutionFunctionSpace ε f v hv x = v x := rfl

/-- A bounded classical solution belongs to the same closed ball used by the
contraction construction. -/
noncomputable def apm_m02a06_solutionBall
    (ε C : ℝ) (f v : ℝ → ℝ) (hC : 0 ≤ C) (hv : apm_m02a06_IsSolution ε f v)
    (hv_bound : ∀ x ∈ Ici (0 : ℝ), |v x| ≤ 2 * (1 + C)) :
    apm_m02a06_Ball C := by
  let w := apm_m02a06_solutionFunctionSpace ε f v hv
  refine ⟨w, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right,
    ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
    BoundedContinuousFunction.norm_le (by positivity)]
  intro x
  simpa only [Real.norm_eq_abs, w] using hv_bound x x.property

lemma apm_m02a06_extend_solutionBall_of_nonneg
    (ε C : ℝ) (f v : ℝ → ℝ) (hC : 0 ≤ C) (hv : apm_m02a06_IsSolution ε f v)
    (hv_bound : ∀ x ∈ Ici (0 : ℝ), |v x| ≤ 2 * (1 + C))
    {x : ℝ} (hx : 0 ≤ x) :
    apm_m02a06_extend (apm_m02a06_solutionBall ε C f v hC hv hv_bound).1 x = v x := by
  rw [apm_m02a06_extend_of_nonneg _ hx]
  rfl

lemma apm_m02a06_solution_source_ode
    (ε : ℝ) (f v : ℝ → ℝ) (hv : apm_m02a06_IsSolution ε f v)
    (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
    -deriv (deriv v) x + v x = f x + ε * (v x) ^ 2 := by
  linarith [hv.2.1 x hx]

lemma apm_m02a06_solutionBall_source_ode
    (ε C : ℝ) (f v : ℝ → ℝ) (hC : 0 ≤ C)
    (hv : apm_m02a06_IsSolution ε f v)
    (hv_bound : ∀ x ∈ Ici (0 : ℝ), |v x| ≤ 2 * (1 + C))
    (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
    -deriv (deriv v) x + v x = f x + ε *
      (apm_m02a06_extend (apm_m02a06_solutionBall ε C f v hC hv hv_bound).1 x) ^ 2 := by
  rw [apm_m02a06_extend_solutionBall_of_nonneg ε C f v hC hv hv_bound hx.le]
  exact apm_m02a06_solution_source_ode ε f v hv x hx

lemma apm_m02a06_solutionBall_extend_zero
    (ε C : ℝ) (f v : ℝ → ℝ) (hC : 0 ≤ C)
    (hv : apm_m02a06_IsSolution ε f v)
    (hv_bound : ∀ x ∈ Ici (0 : ℝ), |v x| ≤ 2 * (1 + C)) :
    apm_m02a06_extend (apm_m02a06_solutionBall ε C f v hC hv hv_bound).1 0 = 1 := by
  rw [apm_m02a06_extend_solutionBall_of_nonneg ε C f v hC hv hv_bound le_rfl]
  exact hv.2.2.1

lemma apm_m02a06_solutionBall_extend_tendsto
    (ε C : ℝ) (f v : ℝ → ℝ) (hC : 0 ≤ C)
    (hv : apm_m02a06_IsSolution ε f v)
    (hv_bound : ∀ x ∈ Ici (0 : ℝ), |v x| ≤ 2 * (1 + C)) :
    Tendsto (apm_m02a06_extend
      (apm_m02a06_solutionBall ε C f v hC hv hv_bound).1) atTop (nhds 0) :=
  apm_m02a06_extend_tendsto_atTop _

lemma apm_m02a06_weighted_plus_hasDerivAt
    (v h : ℝ → ℝ) (x : ℝ) (hv : DifferentiableAt ℝ v x)
    (hv' : DifferentiableAt ℝ (deriv v) x)
    (hode : -deriv (deriv v) x + v x = h x) :
    HasDerivAt (fun y => Real.exp (-y) * (deriv v y + v y))
      (-Real.exp (-x) * h x) x := by
  have he : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    convert (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg using 1 <;> ring
  have hsecond : deriv (deriv v) x = v x - h x := by linarith
  convert he.mul (hv'.hasDerivAt.add hv.hasDerivAt) using 1
  simp only [Pi.add_apply]
  rw [hsecond]
  ring

lemma apm_m02a06_weighted_minus_hasDerivAt
    (v h : ℝ → ℝ) (x : ℝ) (hv : DifferentiableAt ℝ v x)
    (hv' : DifferentiableAt ℝ (deriv v) x)
    (hode : -deriv (deriv v) x + v x = h x) :
    HasDerivAt (fun y => Real.exp y * (deriv v y - v y))
      (-Real.exp x * h x) x := by
  have hsecond : deriv (deriv v) x = v x - h x := by linarith
  convert (Real.hasDerivAt_exp x).mul (hv'.hasDerivAt.sub hv.hasDerivAt) using 1
  simp only [Pi.sub_apply]
  rw [hsecond]
  ring

lemma apm_m02a06_solution_differentiableAt
    (ε : ℝ) (f v : ℝ → ℝ) (hv : apm_m02a06_IsSolution ε f v)
    (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
    DifferentiableAt ℝ v x ∧ DifferentiableAt ℝ (deriv v) x := by
  have hc : ContDiffOn ℝ 2 v (Ioi (0 : ℝ)) := hv.1.mono Ioi_subset_Ici_self
  have hvd : DifferentiableOn ℝ v (Ioi (0 : ℝ)) := hc.differentiableOn (by norm_num)
  have hderiv : ContDiffOn ℝ 1 (deriv v) (Ioi (0 : ℝ)) :=
    hc.deriv_of_isOpen isOpen_Ioi (by norm_num)
  exact ⟨(hvd x hx).differentiableAt (Ioi_mem_nhds hx),
    (hderiv.differentiableOn (by norm_num) x hx).differentiableAt (Ioi_mem_nhds hx)⟩

lemma apm_m02a06_solution_weighted_plus_hasDerivAt
    (ε : ℝ) (f v : ℝ → ℝ) (hv : apm_m02a06_IsSolution ε f v)
    (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
    HasDerivAt (fun y => Real.exp (-y) * (deriv v y + v y))
      (-Real.exp (-x) * (f x + ε * (v x) ^ 2)) x := by
  exact apm_m02a06_weighted_plus_hasDerivAt v
    (fun y => f y + ε * (v y) ^ 2) x
    (apm_m02a06_solution_differentiableAt ε f v hv x hx).1
    (apm_m02a06_solution_differentiableAt ε f v hv x hx).2
    (apm_m02a06_solution_source_ode ε f v hv x hx)

lemma apm_m02a06_solution_weighted_minus_hasDerivAt
    (ε : ℝ) (f v : ℝ → ℝ) (hv : apm_m02a06_IsSolution ε f v)
    (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
    HasDerivAt (fun y => Real.exp y * (deriv v y - v y))
      (-Real.exp x * (f x + ε * (v x) ^ 2)) x := by
  exact apm_m02a06_weighted_minus_hasDerivAt v
    (fun y => f y + ε * (v y) ^ 2) x
    (apm_m02a06_solution_differentiableAt ε f v hv x hx).1
    (apm_m02a06_solution_differentiableAt ε f v hv x hx).2
    (apm_m02a06_solution_source_ode ε f v hv x hx)

lemma apm_m02a06_solution_weighted_plus_integral
    (ε : ℝ) (f v : ℝ → ℝ) (hf : Continuous f)
    (hv : apm_m02a06_IsSolution ε f v)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ y in a..b, -Real.exp (-y) * (f y + ε * (v y) ^ 2)) =
      Real.exp (-b) * (deriv v b + v b) -
        Real.exp (-a) * (deriv v a + v a) := by
  have hsource : ContinuousOn (fun y => f y + ε * (v y) ^ 2) (uIcc a b) :=
    hf.continuousOn.add (continuousOn_const.mul (hv.1.continuousOn.mono (by
      rw [uIcc_of_le hab]
      intro x hx
      exact ha.le.trans hx.1) |>.pow 2))
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact apm_m02a06_solution_weighted_plus_hasDerivAt ε f v hv x
      (ha.trans_le hx.1)
  · exact ((Real.continuous_exp.comp continuous_neg).continuousOn.neg.mul
      hsource).intervalIntegrable

lemma apm_m02a06_solution_weighted_minus_integral
    (ε : ℝ) (f v : ℝ → ℝ) (hf : Continuous f)
    (hv : apm_m02a06_IsSolution ε f v)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ y in a..b, -Real.exp y * (f y + ε * (v y) ^ 2)) =
      Real.exp b * (deriv v b - v b) -
        Real.exp a * (deriv v a - v a) := by
  have hsource : ContinuousOn (fun y => f y + ε * (v y) ^ 2) (uIcc a b) :=
    hf.continuousOn.add (continuousOn_const.mul (hv.1.continuousOn.mono (by
      rw [uIcc_of_le hab]
      intro x hx
      exact ha.le.trans hx.1) |>.pow 2))
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact apm_m02a06_solution_weighted_minus_hasDerivAt ε f v hv x
      (ha.trans_le hx.1)
  · exact (Real.continuous_exp.continuousOn.neg.mul hsource).intervalIntegrable

lemma apm_m02a06_solution_finite_green_formula
    (ε : ℝ) (f v : ℝ → ℝ) (hf : Continuous f)
    (hv : apm_m02a06_IsSolution ε f v)
    (a x b : ℝ) (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    v x = (1 / 2 : ℝ) *
      (Real.exp x *
          (Real.exp (-a) * (deriv v a + v a) +
            ∫ y in a..x, -Real.exp (-y) * (f y + ε * (v y) ^ 2)) -
        Real.exp (-x) *
          (Real.exp b * (deriv v b - v b) -
            ∫ y in x..b, -Real.exp y * (f y + ε * (v y) ^ 2))) := by
  have hp := apm_m02a06_solution_weighted_plus_integral ε f v hf hv
    a x ha hax
  have hm := apm_m02a06_solution_weighted_minus_integral ε f v hf hv
    x b (ha.trans_le hax) hxb
  have hexp1 : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hexp2 : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hp, hm]
  ring_nf at hexp1 hexp2 ⊢
  rw [hexp1, one_mul]

lemma apm_m02a06_solution_second_deriv_tendsto_atTop
    (ε : ℝ) (f v : ℝ → ℝ) (hf_compact : HasCompactSupport f)
    (hv : apm_m02a06_IsSolution ε f v) :
    Tendsto (deriv (deriv v)) atTop (nhds 0) := by
  have hfzero := apm_m02a06_tendsto_zero_of_compactSupport f hf_compact
  have hvzero := hv.2.2.2
  have hvsq : Tendsto (fun x => (v x) ^ 2) atTop (nhds 0) := by
    simpa only [pow_two, zero_mul] using hvzero.mul hvzero
  have hrhs : Tendsto (fun x => v x - f x - ε * (v x) ^ 2) atTop (nhds 0) := by
    simpa only [zero_sub, sub_zero, mul_zero] using
      (hvzero.sub hfzero).sub (tendsto_const_nhds.mul hvsq)
  apply hrhs.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hode := hv.2.1 x hx
  linarith

lemma apm_m02a06_solution_deriv_tendsto_atTop
    (ε : ℝ) (f v : ℝ → ℝ) (hf_compact : HasCompactSupport f)
    (hv : apm_m02a06_IsSolution ε f v) :
    Tendsto (deriv v) atTop (nhds 0) := by
  have hvzero := hv.2.2.2
  have hvvzero := apm_m02a06_solution_second_deriv_tendsto_atTop ε f v hf_compact hv
  rw [Metric.tendsto_atTop] at hvzero hvvzero ⊢
  intro δ hδ
  obtain ⟨Nv, hNv⟩ := hvzero (δ / 4) (by positivity)
  obtain ⟨Nd, hNd⟩ := hvvzero (δ / 4) (by positivity)
  refine ⟨max (max Nv Nd) 1, fun x hx => ?_⟩
  have hxNv : Nv ≤ x := (le_max_left Nv Nd).trans (le_max_left _ 1) |>.trans hx
  have hxNd : Nd ≤ x := (le_max_right Nv Nd).trans (le_max_left _ 1) |>.trans hx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one ((le_max_right (max Nv Nd) 1).trans hx)
  have hvcont : ContinuousOn v (Icc x (x + 1)) :=
    hv.1.continuousOn.mono (by intro y hy; exact hxpos.le.trans hy.1)
  have hvdiff : DifferentiableOn ℝ v (Ioo x (x + 1)) := by
    intro y hy
    exact (apm_m02a06_solution_differentiableAt ε f v hv y
      (hxpos.trans hy.1)).1.differentiableWithinAt
  obtain ⟨c, hc, hcderiv⟩ := exists_deriv_eq_slope v (by linarith)
    hvcont hvdiff
  have hdccont : ContinuousOn (deriv v) (Icc x c) := by
    have hcsub : Icc x c ⊆ Ioi (0 : ℝ) := by
      intro y hy
      exact hxpos.trans_le hy.1
    have hcv : ContDiffOn ℝ 2 v (Ioi (0 : ℝ)) := hv.1.mono Ioi_subset_Ici_self
    exact (hcv.deriv_of_isOpen (m := 1) isOpen_Ioi (by norm_num)).continuousOn.mono hcsub
  have hdcdiff : DifferentiableOn ℝ (deriv v) (Ioo x c) := by
    intro y hy
    exact (apm_m02a06_solution_differentiableAt ε f v hv y
      (hxpos.trans hy.1)).2.differentiableWithinAt
  obtain ⟨d, hd, hdderiv⟩ := exists_deriv_eq_slope (deriv v) hc.1
    hdccont hdcdiff
  rw [Real.dist_eq, sub_zero]
  have hvc : |deriv v c| < δ / 2 := by
    rw [hcderiv]
    have hvx := hNv x hxNv
    have hvx1 := hNv (x + 1) (by linarith)
    rw [Real.dist_eq, sub_zero] at hvx hvx1
    rw [show x + 1 - x = (1 : ℝ) by ring, div_one]
    exact lt_of_le_of_lt (abs_sub _ _) (by linarith)
  have hvdc : |deriv v c - deriv v x| < δ / 2 := by
    have hdd := hNd d (by linarith [hd.1, hxNd])
    rw [Real.dist_eq, sub_zero] at hdd
    have hcx : 0 < c - x := sub_pos.mpr hc.1
    have heq : deriv v c - deriv v x = deriv (deriv v) d * (c - x) := by
      rw [hdderiv]
      field_simp
    rw [heq, abs_mul]
    calc
      |deriv (deriv v) d| * |c - x| < (δ / 4) * |c - x| :=
        mul_lt_mul_of_pos_right hdd (abs_pos.mpr (ne_of_gt hcx))
      _ < δ / 2 := by
        rw [abs_of_pos hcx]
        have hc1 : c - x < 1 := by linarith [hc.2]
        nlinarith [abs_nonneg (deriv (deriv v) d)]
  calc
    |deriv v x| ≤ |deriv v c| + |deriv v c - deriv v x| := by
      have := abs_add_le (deriv v c) (deriv v x - deriv v c)
      simpa [add_sub_cancel_left, abs_sub_comm] using this
    _ < δ := by linarith

lemma apm_m02a06_solution_weighted_plus_eq_tail
    (ε C : ℝ) (f v : ℝ → ℝ) (hf_smooth : ContDiff ℝ ∞ f)
    (hf_compact : HasCompactSupport f) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hf_bound : ∀ x ∈ Ici (0 : ℝ), |f x| ≤ C)
    (hv : apm_m02a06_IsSolution ε f v)
    (hv_bound : ∀ x ∈ Ici (0 : ℝ), |v x| ≤ 2 * (1 + C))
    (a : ℝ) (ha : 0 < a) :
    Real.exp (-a) * (deriv v a + v a) =
      ∫ y in Ioi a, Real.exp (-y) *
        (f y + ε * (apm_m02a06_extend
          (apm_m02a06_solutionBall ε C f v hC hv hv_bound).1 y) ^ 2) := by
  let w := apm_m02a06_solutionBall ε C f v hC hv hv_bound
  let source := fun y => f y + ε * (apm_m02a06_extend w.1 y) ^ 2
  have hscont : Continuous source :=
    apm_m02a06_source_continuous ε f hf_smooth.continuous w.1
  have hsbound : ∀ y ∈ Ioi (0 : ℝ), |source y| ≤
      C + ε * (2 * (1 + C)) ^ 2 := by
    intro y hy
    exact apm_m02a06_source_bound C ε f w hC hε hf_bound y hy.le
  have hsint := apm_m02a06_integrableOn_exp_neg_mul source
    (C + ε * (2 * (1 + C)) ^ 2) hscont hsbound
  have hv'zero := apm_m02a06_solution_deriv_tendsto_atTop ε f v hf_compact hv
  have hstatezero : Tendsto
      (fun x => Real.exp (-x) * (deriv v x + v x)) atTop (nhds 0) := by
    simpa only [zero_add, zero_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.mul (hv'zero.add hv.2.2.2)
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := a) (m := (0 : ℝ))
    (f := fun x => Real.exp (-x) * (deriv v x + v x))
    (f' := fun x => -(Real.exp (-x) * source x))
    (fun x hx => by
      have hxpos : x ∈ Ioi (0 : ℝ) := ha.trans_le hx
      simpa only [neg_mul, source, w,
        apm_m02a06_extend_solutionBall_of_nonneg ε C f v hC hv hv_bound hxpos.le]
        using apm_m02a06_solution_weighted_plus_hasDerivAt ε f v hv x hxpos)
    (hsint.mono_set (Ioi_subset_Ioi ha.le) |>.neg) hstatezero
  rw [MeasureTheory.integral_neg] at hFTC
  dsimp only at hFTC
  linarith

lemma apm_m02a06_solution_green_formula_from_positive
    (ε C : ℝ) (f v : ℝ → ℝ) (hf_smooth : ContDiff ℝ ∞ f)
    (hf_compact : HasCompactSupport f) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hf_bound : ∀ x ∈ Ici (0 : ℝ), |f x| ≤ C)
    (hv : apm_m02a06_IsSolution ε f v)
    (hv_bound : ∀ x ∈ Ici (0 : ℝ), |v x| ≤ 2 * (1 + C))
    (a x : ℝ) (ha : 0 < a) (hax : a ≤ x) :
    let source := fun y => f y + ε * (apm_m02a06_extend
      (apm_m02a06_solutionBall ε C f v hC hv hv_bound).1 y) ^ 2
    v x = (1 / 2 : ℝ) *
      (Real.exp x * ((∫ y in Ioi a, Real.exp (-y) * source y) -
          ∫ y in a..x, Real.exp (-y) * source y) -
        Real.exp (-x) * (Real.exp (2 * a) *
            (∫ y in Ioi a, Real.exp (-y) * source y) -
          2 * Real.exp a * v a -
          ∫ y in a..x, Real.exp y * source y)) := by
  dsimp only
  let w := apm_m02a06_solutionBall ε C f v hC hv hv_bound
  let source := fun y => f y + ε * (apm_m02a06_extend w.1 y) ^ 2
  have hp := apm_m02a06_solution_weighted_plus_eq_tail ε C f v hf_smooth
    hf_compact hC hε hf_bound hv hv_bound a ha
  have hpf := apm_m02a06_solution_weighted_plus_integral ε f v
    hf_smooth.continuous hv a x ha hax
  have hm := apm_m02a06_solution_weighted_minus_integral ε f v
    hf_smooth.continuous hv a x ha hax
  have hsource : ∀ y ∈ uIcc a x,
      f y + ε * (v y) ^ 2 = source y := by
    intro y hy
    rw [uIcc_of_le hax] at hy
    simp only [source, w,
      apm_m02a06_extend_solutionBall_of_nonneg ε C f v hC hv hv_bound
        (ha.le.trans hy.1)]
  have hneg : (∫ y in a..x, -Real.exp (-y) * (f y + ε * (v y) ^ 2)) =
      -(∫ y in a..x, Real.exp (-y) * source y) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro y hy
    change -Real.exp (-y) * (f y + ε * v y ^ 2) =
      -(Real.exp (-y) * source y)
    rw [hsource y hy]
    ring
  have hpos : (∫ y in a..x, -Real.exp y * (f y + ε * (v y) ^ 2)) =
      -(∫ y in a..x, Real.exp y * source y) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro y hy
    change -Real.exp y * (f y + ε * v y ^ 2) =
      -(Real.exp y * source y)
    rw [hsource y hy]
    ring
  rw [hneg] at hpf
  rw [hpos] at hm
  have hexpa : Real.exp (2 * a) * (Real.exp (-a) * (deriv v a + v a)) =
      Real.exp a * (deriv v a + v a) := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 1
    ring
  have hrecover : v x = (1 / 2 : ℝ) *
      (Real.exp x * (Real.exp (-x) * (deriv v x + v x)) -
        Real.exp (-x) * (Real.exp x * (deriv v x - v x))) := by
    have hx1 : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add]
      simp
    have hx2 : Real.exp (-x) * Real.exp x = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      v x = (1 / 2 : ℝ) * ((deriv v x + v x) - (deriv v x - v x)) := by ring
      _ = _ := by rw [← mul_assoc, hx1, one_mul, ← mul_assoc, hx2, one_mul]
  dsimp only [source, w] at hp hm ⊢
  dsimp only [source, w] at hpf
  rw [hp] at hexpa
  have hpx : Real.exp (-x) * (deriv v x + v x) =
      (∫ y in Ioi a, Real.exp (-y) *
        (f y + ε * (apm_m02a06_extend
          (apm_m02a06_solutionBall ε C f v hC hv hv_bound).1 y) ^ 2)) -
      ∫ y in a..x, Real.exp (-y) *
        (f y + ε * (apm_m02a06_extend
          (apm_m02a06_solutionBall ε C f v hC hv hv_bound).1 y) ^ 2) := by
    linarith
  have hqa : Real.exp a * (deriv v a - v a) =
      Real.exp (2 * a) *
        (∫ y in Ioi a, Real.exp (-y) *
          (f y + ε * (apm_m02a06_extend
            (apm_m02a06_solutionBall ε C f v hC hv hv_bound).1 y) ^ 2)) -
      2 * Real.exp a * v a := by
    linarith [hexpa]
  have hqx : Real.exp x * (deriv v x - v x) =
      Real.exp (2 * a) *
        (∫ y in Ioi a, Real.exp (-y) *
          (f y + ε * (apm_m02a06_extend
            (apm_m02a06_solutionBall ε C f v hC hv hv_bound).1 y) ^ 2)) -
      2 * Real.exp a * v a -
      ∫ y in a..x, Real.exp y *
        (f y + ε * (apm_m02a06_extend
          (apm_m02a06_solutionBall ε C f v hC hv hv_bound).1 y) ^ 2) := by
    linarith
  rw [hrecover, hpx, hqx]

lemma apm_m02a06_integral_Ioi_tendsto_lower_zero
    (g : ℝ → ℝ) (hgcont : Continuous g)
    (hgint : MeasureTheory.IntegrableOn g (Ioi (0 : ℝ))) :
    Tendsto (fun a => ∫ y in Ioi a, g y) (𝓝[Ioi (0 : ℝ)] 0)
      (nhds (∫ y in Ioi (0 : ℝ), g y)) := by
  have hprim : Tendsto (fun a => ∫ y in (0 : ℝ)..a, g y)
      (𝓝[Ioi (0 : ℝ)] 0) (nhds 0) := by
    have hc : Continuous (fun a => ∫ y in (0 : ℝ)..a, g y) :=
      (intervalIntegral.differentiable_integral_of_continuous
        (a := (0 : ℝ)) hgcont).continuous
    have ht : Tendsto (fun a => ∫ y in (0 : ℝ)..a, g y) (𝓝 (0 : ℝ))
        (nhds (∫ y in (0 : ℝ)..(0 : ℝ), g y)) := hc.continuousAt
    simpa using ht.mono_left inf_le_left
  have hlim : Tendsto
      (fun a => (∫ y in Ioi (0 : ℝ), g y) - ∫ y in (0 : ℝ)..a, g y)
      (𝓝[Ioi (0 : ℝ)] 0) (nhds ((∫ y in Ioi (0 : ℝ), g y) - 0)) :=
    tendsto_const_nhds.sub hprim
  simpa only [sub_zero] using hlim.congr' (by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have hsub := intervalIntegral.integral_Ioi_sub_Ioi hgint ha.le
    linarith)

lemma apm_m02a06_intervalIntegral_tendsto_lower_zero
    (g : ℝ → ℝ) (hgcont : Continuous g) (x : ℝ) :
    Tendsto (fun a => ∫ y in a..x, g y) (𝓝[Ioi (0 : ℝ)] 0)
      (nhds (∫ y in (0 : ℝ)..x, g y)) := by
  have hprim : Tendsto (fun a => ∫ y in (0 : ℝ)..a, g y)
      (𝓝[Ioi (0 : ℝ)] 0) (nhds 0) := by
    have hc : Continuous (fun a => ∫ y in (0 : ℝ)..a, g y) :=
      (intervalIntegral.differentiable_integral_of_continuous
        (a := (0 : ℝ)) hgcont).continuous
    have ht : Tendsto (fun a => ∫ y in (0 : ℝ)..a, g y) (𝓝 (0 : ℝ))
        (nhds (∫ y in (0 : ℝ)..(0 : ℝ), g y)) := hc.continuousAt
    simpa using ht.mono_left inf_le_left
  have hlim : Tendsto
      (fun a => (∫ y in (0 : ℝ)..x, g y) - ∫ y in (0 : ℝ)..a, g y)
      (𝓝[Ioi (0 : ℝ)] 0) (nhds ((∫ y in (0 : ℝ)..x, g y) - 0)) :=
    tendsto_const_nhds.sub hprim
  simpa only [sub_zero] using hlim.congr' (by
    filter_upwards with a
    have h0a : IntervalIntegrable g MeasureTheory.volume (0 : ℝ) a :=
      hgcont.intervalIntegrable _ _
    have hax : IntervalIntegrable g MeasureTheory.volume a x :=
      hgcont.intervalIntegrable _ _
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume) (f := g) h0a hax]
    ring)

lemma apm_m02a06_solution_green_formula_positive
    (ε C : ℝ) (f v : ℝ → ℝ) (hf_smooth : ContDiff ℝ ∞ f)
    (hf_compact : HasCompactSupport f) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hf_bound : ∀ x ∈ Ici (0 : ℝ), |f x| ≤ C)
    (hv : apm_m02a06_IsSolution ε f v)
    (hv_bound : ∀ x ∈ Ici (0 : ℝ), |v x| ≤ 2 * (1 + C))
    (x : ℝ) (hx : 0 < x) :
    let source := fun y => f y + ε * (apm_m02a06_extend
      (apm_m02a06_solutionBall ε C f v hC hv hv_bound).1 y) ^ 2
    v x = (1 / 2 : ℝ) *
      (Real.exp x * ((∫ y in Ioi (0 : ℝ), Real.exp (-y) * source y) -
          ∫ y in (0 : ℝ)..x, Real.exp (-y) * source y) -
        Real.exp (-x) * ((∫ y in Ioi (0 : ℝ), Real.exp (-y) * source y) -
          2 - ∫ y in (0 : ℝ)..x, Real.exp y * source y)) := by
  dsimp only
  let w := apm_m02a06_solutionBall ε C f v hC hv hv_bound
  let source := fun y => f y + ε * (apm_m02a06_extend w.1 y) ^ 2
  have hscont : Continuous source :=
    apm_m02a06_source_continuous ε f hf_smooth.continuous w.1
  have hsbound : ∀ y ∈ Ioi (0 : ℝ), |source y| ≤
      C + ε * (2 * (1 + C)) ^ 2 := by
    intro y hy
    exact apm_m02a06_source_bound C ε f w hC hε hf_bound y hy.le
  have hsint := apm_m02a06_integrableOn_exp_neg_mul source
    (C + ε * (2 * (1 + C)) ^ 2) hscont hsbound
  have htail := apm_m02a06_integral_Ioi_tendsto_lower_zero
    (fun y => Real.exp (-y) * source y)
    ((Real.continuous_exp.comp continuous_neg).mul hscont) hsint
  have hneg := apm_m02a06_intervalIntegral_tendsto_lower_zero
    (fun y => Real.exp (-y) * source y)
    ((Real.continuous_exp.comp continuous_neg).mul hscont) x
  have hpos := apm_m02a06_intervalIntegral_tendsto_lower_zero
    (fun y => Real.exp y * source y) (Real.continuous_exp.mul hscont) x
  have he2 : Tendsto (fun a : ℝ => Real.exp (2 * a)) (𝓝[Ioi (0 : ℝ)] 0)
      (nhds 1) := by
    have hc : ContinuousAt (fun a : ℝ => Real.exp (2 * a)) 0 := by fun_prop
    simpa using hc.tendsto.mono_left inf_le_left
  have he1 : Tendsto (fun a : ℝ => Real.exp a) (𝓝[Ioi (0 : ℝ)] 0)
      (nhds 1) := by
    have ht : Tendsto Real.exp (𝓝 (0 : ℝ)) (nhds (Real.exp 0)) :=
      Real.continuous_exp.continuousAt
    simpa using ht.mono_left inf_le_left
  have hv0 : Tendsto v (𝓝[Ioi (0 : ℝ)] 0) (nhds 1) := by
    have hc := (hv.1.continuousOn 0 (by simp)).mono Ioi_subset_Ici_self
    simpa only [hv.2.2.1] using hc.tendsto
  have hc1 : Tendsto (fun _ : ℝ => Real.exp x) (𝓝[Ioi (0 : ℝ)] 0)
      (nhds (Real.exp x)) := tendsto_const_nhds
  have hc2 : Tendsto (fun _ : ℝ => Real.exp (-x)) (𝓝[Ioi (0 : ℝ)] 0)
      (nhds (Real.exp (-x))) := tendsto_const_nhds
  have hinner1 := htail.sub hneg
  have hinner2 := ((he2.mul htail).sub ((he1.mul hv0).const_mul 2)).sub hpos
  have houter := (hc1.mul hinner1).sub (hc2.mul hinner2)
  have hright := houter.const_mul (1 / 2 : ℝ)
  have hformula : ∀ᶠ a in 𝓝[Ioi (0 : ℝ)] 0,
      v x = (1 / 2 : ℝ) *
        (Real.exp x * ((∫ y in Ioi a, Real.exp (-y) * source y) -
            ∫ y in a..x, Real.exp (-y) * source y) -
          Real.exp (-x) * (Real.exp (2 * a) *
              (∫ y in Ioi a, Real.exp (-y) * source y) -
            2 * (Real.exp a * v a) - ∫ y in a..x, Real.exp y * source y)) := by
    have hIic : ∀ᶠ a in 𝓝[Ioi (0 : ℝ)] 0, a ∈ Iic x :=
      Filter.Eventually.filter_mono inf_le_left (Iic_mem_nhds hx)
    filter_upwards [self_mem_nhdsWithin, hIic] with a ha hax
    have hf := apm_m02a06_solution_green_formula_from_positive ε C f v hf_smooth
      hf_compact hC hε hf_bound hv hv_bound a x ha hax
    dsimp only at hf
    convert hf using 1 <;> ring
  have hconst : Tendsto (fun _ : ℝ => v x) (𝓝[Ioi (0 : ℝ)] 0) (nhds (v x)) :=
    tendsto_const_nhds
  have heq : ∀ᶠ a in 𝓝[Ioi (0 : ℝ)] 0,
      (1 / 2 : ℝ) *
        (Real.exp x * ((∫ y in Ioi a, Real.exp (-y) * source y) -
            ∫ y in a..x, Real.exp (-y) * source y) -
          Real.exp (-x) * (Real.exp (2 * a) *
              (∫ y in Ioi a, Real.exp (-y) * source y) -
            2 * (Real.exp a * v a) - ∫ y in a..x, Real.exp y * source y)) = v x := by
    filter_upwards [hformula] with a ha
    exact ha.symm
  have hu := tendsto_nhds_unique hconst (hright.congr' heq)
  dsimp only [source, w] at hu ⊢
  simpa using hu

lemma apm_m02a06_solution_eq_exp_add_greenSplit
    (ε C : ℝ) (f v : ℝ → ℝ) (hf_smooth : ContDiff ℝ ∞ f)
    (hf_compact : HasCompactSupport f) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hf_bound : ∀ x ∈ Ici (0 : ℝ), |f x| ≤ C)
    (hv : apm_m02a06_IsSolution ε f v)
    (hv_bound : ∀ x ∈ Ici (0 : ℝ), |v x| ≤ 2 * (1 + C))
    (x : ℝ) (hx : 0 ≤ x) :
    let source := fun y => f y + ε * (apm_m02a06_extend
      (apm_m02a06_solutionBall ε C f v hC hv hv_bound).1 y) ^ 2
    v x = Real.exp (-x) + apm_m02a06_greenSplit source x := by
  dsimp only
  by_cases hx0 : x = 0
  · subst x
    rw [hv.2.2.1, apm_m02a06_greenSplit_zero]
    norm_num
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have h := apm_m02a06_solution_green_formula_positive ε C f v hf_smooth
      hf_compact hC hε hf_bound hv hv_bound x hxpos
    dsimp only at h
    rw [h]
    unfold apm_m02a06_greenSplit
    ring

lemma apm_m02a06_solution_eq_greenTransform
    (ε C : ℝ) (f v : ℝ → ℝ) (hf_smooth : ContDiff ℝ ∞ f)
    (hf_compact : HasCompactSupport f) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hf_bound : ∀ x ∈ Ici (0 : ℝ), |f x| ≤ C)
    (hv : apm_m02a06_IsSolution ε f v)
    (hv_bound : ∀ x ∈ Ici (0 : ℝ), |v x| ≤ 2 * (1 + C))
    (x : ℝ) (hx : 0 ≤ x) :
    v x = apm_m02a06_greenTransform ε f
      (apm_m02a06_extend
        (apm_m02a06_solutionBall ε C f v hC hv hv_bound).1) x := by
  let w := apm_m02a06_solutionBall ε C f v hC hv hv_bound
  let source := fun y => f y + ε * (apm_m02a06_extend w.1 y) ^ 2
  have hscont : Continuous source :=
    apm_m02a06_source_continuous ε f hf_smooth.continuous w.1
  have hsbound : ∀ y ∈ Ici (0 : ℝ), |source y| ≤
      C + ε * (2 * (1 + C)) ^ 2 := by
    intro y hy
    exact apm_m02a06_source_bound C ε f w hC hε hf_bound y hy
  have hvrep := apm_m02a06_solution_eq_exp_add_greenSplit ε C f v hf_smooth
    hf_compact hC hε hf_bound hv hv_bound x hx
  dsimp only at hvrep
  rw [hvrep]
  unfold apm_m02a06_greenTransform
  rw [apm_m02a06_integral_greenKernel_mul_eq_greenSplit source
    (C + ε * (2 * (1 + C)) ^ 2) x hx hscont hsbound]

lemma apm_m02a06_solutionBall_fixed
    (ε C : ℝ) (f v : ℝ → ℝ) (hf_smooth : ContDiff ℝ ∞ f)
    (hf_compact : HasCompactSupport f) (hC : 0 ≤ C) (hε : 0 < ε)
    (hε_small : ε < 1 / (4 * (1 + C)))
    (hf_bound : ∀ x ∈ Ici (0 : ℝ), |f x| ≤ C)
    (hv : apm_m02a06_IsSolution ε f v)
    (hv_bound : ∀ x ∈ Ici (0 : ℝ), |v x| ≤ 2 * (1 + C)) :
    let hzero := fun u : apm_m02a06_Ball C =>
      apm_m02a06_greenTransform_extend_tendsto_atTop f C ε u hC hε.le
        hf_smooth.continuous (apm_m02a06_tendsto_zero_of_compactSupport f hf_compact)
        hf_bound
    apm_m02a06_greenBallMap f C ε hC hε hε_small hf_smooth.continuous
      hf_bound hzero (apm_m02a06_solutionBall ε C f v hC hv hv_bound) =
        apm_m02a06_solutionBall ε C f v hC hv hv_bound := by
  dsimp only
  apply Subtype.ext
  apply DFunLike.ext _ _
  intro x
  rw [apm_m02a06_greenBallMap_apply]
  change apm_m02a06_greenTransform ε f
    (apm_m02a06_extend
      (apm_m02a06_solutionBall ε C f v hC hv hv_bound).1) x = v x
  exact (apm_m02a06_solution_eq_greenTransform ε C f v hf_smooth hf_compact
    hC hε.le hf_bound hv hv_bound x x.property).symm

theorem apm_m02a06
    (f : ℝ → ℝ) (hf_smooth : ContDiff ℝ ∞ f)
    (hf_compact : HasCompactSupport f) (hf_support : Function.support f ⊆ Ioi 0)
    (C : ℝ) (hC : 0 ≤ C) (hf_bound : ∀ x ∈ Ici (0 : ℝ), |f x| ≤ C)
    (ε : ℝ) (hε : 0 < ε) (hε_small : ε < 1 / (4 * (1 + C))) :
    ∃ u : ℝ → ℝ,
      apm_m02a06_IsSolution ε f u ∧
      (∀ x ∈ Ici (0 : ℝ), |u x| ≤ 2 * (1 + C)) ∧
      ∀ v : ℝ → ℝ,
        apm_m02a06_IsSolution ε f v →
        (∀ x ∈ Ici (0 : ℝ), |v x| ≤ 2 * (1 + C)) →
        ∀ x ∈ Ici (0 : ℝ), v x = u x := by
  /-
  Boundary (closer hop 1): the informal contraction argument requires
  constructing the Dirichlet Green operator for `-deriv (deriv ·) + id` on
  `Ici 0`, proving that it preserves decay at `atTop`, and establishing its
  sup-norm maximum-principle estimate. Repository searches found only the
  abstract fixed-point layer (`ContractingWith.fixedPoint` and
  `ContractingWith.fixedPoint_unique`, used by `m01J05` and `t91A04`), not a
  compiled half-line Green operator or the required maximum-principle bound.

  This hop compiles the nonlinear and numerical layers independently.
  `apm_m02a06_radius_pos` proves positivity of the frozen ball radius,
  `apm_m02a06_contraction_constant_lt_one` derives the exact strict constant
  `4 * ε * (1 + C) < 1`, and `apm_m02a06_quadratic_lipschitz` proves the
  pointwise quadratic difference estimate on that ball.

  The abstract `ContractingWith` API therefore remains blocked only before
  these estimates: the missing work is the concrete inverse of
  `-deriv (deriv ·) + id` on the half-line, with regularity, boundary value,
  decay, and operator sup-norm bound. Searches of `LEMMA-INDEX.md`, all solved
  artifacts, `ConstructionTargets/`, Mathlib's ODE/integration/maximum-principle
  sources, and git history found no such Green operator. Siblings `m94A05`,
  `m94J05`, and `m96A02` record the same concrete-operator boundary, while
  `t91A04` only supplies the already-known abstract fixed-point wrapper.

  Closer hop 2 begins the missing concrete operator rather than repeating the
  API search. `apm_m02a06_greenKernel` defines the half-line Dirichlet kernel
  `G(x,y) = (exp(-|x-y|) - exp(-(x+y)))/2`.
  `apm_m02a06_greenKernel_comm`, the two boundary lemmas, and the pointwise
  bounds prove that it is symmetric, vanishes when either nonnegative
  argument is zero, and satisfies `0 ≤ G(x,y) ≤ 1/2` on the half-line. The
  remaining bridge is to define the improper integral operator, split at
  `y=x` to differentiate twice, prove decay and the full kernel-mass/sup-norm
  estimate, and then apply the compiled contraction layer. Searches of the
  exponential integral and parameter-integral APIs found primitives for these
  steps but no packaged half-line Green-operator theorem.

  Closer hop 3 carries out the exact algebraic preparation for that split.
  `apm_m02a06_greenKernel_of_le` and `apm_m02a06_greenKernel_of_ge` give the
  two smooth exponential formulas on `y ≤ x` and `x ≤ y`, respectively,
  and `apm_m02a06_greenKernel_le_exp` gives the integrable exponential
  majorant needed for dominated improper integration. Inspection of
  `ImproperIntegrals.lean` found `integrableOn_exp_neg_Ioi` and
  `integral_exp_neg_Ioi`, so the scalar tails are available. What remains is
  still the substantial parameter-integral assembly: combine the two moving
  domains, differentiate both pieces twice including their boundary terms,
  prove the resulting function tends to zero, then bundle a complete
  sup-norm function space and apply Banach contraction. No packaged theorem
  performs that assembly, and it was not completed in this final hop.

  HOP 4 GAP AUDIT (outcomes A and B both failed). The nonlinear operator is
  now explicit as `apm_m02a06_greenTransform`. Searches of the complete
  bounded-continuous-function spaces, improper parameter integrals, moving-
  endpoint differentiation, and fixed-point APIs found the ingredients but no
  theorem establishing the required combined regularity and contraction.

  The precise missing lemma is:

      theorem apm_m02a06_greenTransform_fixedPoint
          (f : ℝ → ℝ) (hf_smooth : ContDiff ℝ ∞ f)
          (hf_compact : HasCompactSupport f)
          (hf_support : Function.support f ⊆ Ioi 0)
          (C : ℝ) (hC : 0 ≤ C)
          (hf_bound : ∀ x ∈ Ici (0 : ℝ), |f x| ≤ C)
          (ε : ℝ) (hε : 0 < ε)
          (hε_small : ε < 1 / (4 * (1 + C))) :
          ∃! u : ℝ → ℝ,
            (∀ x ∈ Ici (0 : ℝ),
              u x = apm_m02a06_greenTransform ε f u x) ∧
            apm_m02a06_IsSolution ε f u ∧
            ∀ x ∈ Ici (0 : ℝ), |u x| ≤ 2 * (1 + C)

  This is stronger than the frozen conclusion only by recording the defining
  fixed-point identity, and is the exact theorem delivered by the intended
  Green-operator contraction proof. Its proof must establish the moving-
  domain twice-differentiation, boundary value, decay, kernel-mass bound,
  completeness of the chosen sup-norm space, and contraction. The statement
  is unchanged and the existing sorry is retained honestly.

  Closer hop 5 starts the exact kernel-mass calculation needed by that
  operator estimate. `apm_m02a06_integral_reflected_exp` proves directly in
  Mathlib's set-integral API that the reflected term has half-line mass
  `exp (-x)`. The remaining scalar identity is the split calculation
  `∫ y in Ici 0, exp (-|x-y|) = 2 - exp (-x)` for `x ≥ 0`; together these give
  `∫ y in Ici 0, G x y = 1 - exp (-x) ≤ 1`. This is upstream of both the
  self-map estimate and contraction estimate, but does not yet discharge the
  parameter-integral regularity and fixed-point obligations above.

  Closer hop 6 completes that scalar calculation. The lower and upper pieces
  of `exp (-|x-y|)` are integrated separately, their integrability is bundled,
  and `apm_m02a06_integral_greenKernel` now gives the exact mass
  `1 - exp (-x)` for `x ≥ 0`. Consequently
  `apm_m02a06_integral_greenKernel_le_one` is the compiled norm-one kernel
  estimate needed for the Green operator. The remaining work is to lift this
  scalar estimate to bounded functions, establish the transform's regularity
  and decay, and perform the complete-space contraction construction and
  fixed-point/ODE equivalence.

  Closer hop 7 lifts the mass bound to its first functional consumer.
  `apm_m02a06_integrableOn_greenKernel` establishes Bochner integrability of
  each kernel slice, and `apm_m02a06_greenKernel_integral_mul_le` proves the
  sharp estimate `|∫ G(x,y) h(y) dy| ≤ B` from the sole pointwise hypothesis
  `|h| ≤ B`. This removes the integral-estimate obligation from both the
  self-map and contraction arguments. Remaining are their complete function-
  space packaging, transform regularity/decay, and fixed-point/ODE equivalence.

  Closer hop 8 applies the operator estimate to the nonlinear transform.
  `apm_m02a06_greenTransform_abs_le` gives the generic pointwise self-map
  bound, and `apm_m02a06_greenTransform_maps_ball` specializes it to a strict
  radius bound under the theorem's smallness assumption. The companion
  `apm_m02a06_greenTransform_sub_le` proves the exact contraction estimate
  with constant `4 * ε * (1 + C)` (assuming the two displayed integrands are
  integrable, as they will be for members of the continuous function space).
  Thus the remaining fixed-point work is principally the complete-space and
  regularity/decay packaging, followed by the Green identity for arbitrary
  bounded classical solutions.

  Closer hop 9 installs the intended Banach-space carrier using Mathlib's
  `C₀(Ici 0, ℝ)`, rather than a bespoke sup-norm completion. The closed ball
  is proved nonempty and complete, membership gives the exact pointwise
  radius bound, and evaluation of a difference is bounded by the ambient
  metric. Continuity of every carrier element is also exposed. The remaining
  representation seam is to show that the Green transform is continuous and
  vanishes at infinity as a function of `x`, so it defines a self-map of this
  carrier; after that the compiled bounds feed the fixed-point API directly.

  Closer hop 10 repairs the missing order-topology instance on `Ici 0` by
  proving its closed intervals compact through the subtype embedding. This
  yields `cocompact = atTop` on the half-line, so carrier elements now have a
  compiled `atTop` decay theorem. Conversely, `apm_m02a06_toFunctionSpace`
  packages any continuous half-line function with `atTop` decay into the
  complete carrier. Thus both directions of the representation seam used in
  the final existence and uniqueness statement are available; only proving
  those properties for the Green transform itself remains before Banach.

  Closer hop 11 introduces `apm_m02a06_greenSplit`, the moving-endpoint
  presentation in which the kernel integral is a sum of two finite interval
  primitives and one fixed improper scalar. Its continuity is now compiled
  for continuous input. The exponentially weighted input is proved integrable
  from continuity and a uniform bound, and the upper-tail integral is proved
  equal to the fixed total minus its finite primitive. What remains at this
  seam is the algebraic integral split proving `greenSplit h x` equals
  `∫ G(x,y)h(y)dy` for `x ≥ 0`; continuity of the actual transform then follows
  immediately, after which decay and differentiation use the same formula.

  Closer hop 12 completes that equality. Named lower-triangle and upper-tail
  integration lemmas rewrite both kernel branches into weighted primitives;
  their integrability hypotheses are compiled and the pieces recombine into
  `apm_m02a06_integral_greenKernel_mul_eq_greenSplit`. Consequently the actual
  Green integral is continuous on `Ici 0`, and
  `apm_m02a06_greenTransform_continuousOn_of_source` lifts this directly to
  the nonlinear transform for a continuous bounded source. Remaining before
  the ball self-map is the transform's decay at `atTop`; differentiation of
  the same split identity then supplies the ODE regularity layer.

  Closer hop 13 supplies that differentiation layer. The two moving finite
  primitives are differentiated by the interval-integral FTC, and the
  resulting first derivative is packaged as `apm_m02a06_greenSplitDeriv`.
  Differentiating once more proves the pointwise identity
  `-deriv (deriv (greenSplit h)) + greenSplit h = h`; the same calculations
  establish global `ContDiff ℝ 2` regularity for every continuous source.
  The split formula also gives the Dirichlet value at zero directly. The
  residual existence seam is therefore atTop decay of the transform and its
  carrier-valued contraction/fixed point. Uniqueness additionally requires
  deriving the Green representation for every bounded classical solution.

  Closer hop 14 installs the total-function bridge required by that carrier
  construction. `apm_m02a06_extend` continuously extends each half-line C₀
  function by precomposition with `max 0`; it agrees exactly on `Ici 0`,
  preserves atTop decay, and exposes both the radius and evaluation-distance
  bounds. The nonlinear source built from this extension is continuous,
  tends to zero whenever `f` does, and has the precise uniform bound needed
  by the compiled Green estimates. The remaining analytic obligation is now
  isolated: prove `greenSplit` preserves atTop decay. That result directly
  permits the carrier self-map and metric contraction construction.

  Closer hop 15 specializes every bounded-integral obligation to that total
  extension. For a ball element the nonlinear Green integrand is now proved
  integrable, the transform is continuous on `Ici 0`, and its values lie
  strictly inside the frozen radius. More importantly, the transform
  difference is bounded pointwise by
  `(4 * ε * (1 + C)) * dist u v`, with no residual integrability premises.
  Thus after the sole remaining C₀-decay lemma packages the self-map, this
  estimate lifts directly to its ambient sup metric and Banach fixed point.

  Closer hop 16 performs that lift while keeping decay as the sole explicit
  input. `apm_m02a06_greenTransformFunctionSpace` packages a transform with
  a supplied atTop limit into C₀, and `apm_m02a06_greenBallMap` proves this is
  a self-map of the frozen closed ball. Its application theorem exposes the
  original integral formula, while `apm_m02a06_greenBallMap_dist_le` upgrades
  the pointwise estimate to the exact sup-metric contraction bound. Once the
  decay argument supplies `hzero`, no further analytic or metric packaging is
  needed before constructing `ContractingWith` and its fixed point.

  Closer hop 17 constructs the nonnegative contraction coefficient as an
  `NNReal` and proves the packaged ball map is `ContractingWith` that
  coefficient. The strict inequality is exactly the theorem's smallness
  hypothesis, and Lipschitz continuity follows from hop 16's sup-metric
  estimate. Consequently the abstract Banach layer is fully discharged once
  the decay hypothesis is instantiated; the remaining mathematical work is
  decay, extraction of solution facts from the fixed point, and converse
  Green representation for uniqueness.

  Closer hop 18 installs completeness and nonemptiness of the closed-ball
  subtype locally and constructs the actual Banach fixed point. Its fixed
  point equation is exposed both as an equality in the ball and pointwise as
  the original nonlinear Green integral. A companion theorem proves every
  other fixed point in the ball equals this one. Therefore, after supplying
  the isolated transform-decay hypothesis, existence and fixed-point
  uniqueness are now immediate; what remains is translating the equation to
  the BVP and proving arbitrary bounded classical solutions are fixed points.

  Closer hop 19 compiles the remaining source-side limit conversion. Compact
  support is unfolded as eventual equality to zero on the coclosed-compact
  filter, restricted along `atTop_le_cocompact`, and converted into
  `Tendsto f atTop (nhds 0)`. Combining this with the C₀ extension-square
  limit proves the exact nonlinear source `f + ε * u²` tends to zero for
  every carrier element. Hence the unresolved Green-decay theorem now
  receives a source already carrying continuity, a uniform bound, and its
  zero limit; no theorem hypotheses remain to translate after it is proved.

  Closer hop 20 extracts three final-solution facts directly from the
  conditional fixed point. Its total extension inherits the carrier's atTop
  decay and the exact closed-ball bound. Evaluating the fixed-point equation
  at zero and using the kernel's Dirichlet vanishing proves the required
  boundary value `u 0 = 1`. After the Green-decay hypothesis is instantiated,
  these discharge the boundary, decay, and size conjuncts of existence; only
  `ContDiffOn 2` and the nonlinear ODE must still be transported from the
  compiled split-operator identities.

  Closer hop 21 completes that transport. The homogeneous term `exp (-x)` is
  differentiated twice, combined with `greenSplit_ode`, and packaged as the
  ODE for `exp (-x) + greenSplit h`. At every interior half-line point the
  fixed-point extension is locally equal to this smooth formula; applying
  `EventuallyEq.deriv_eq` twice identifies its second derivative and proves
  the full nonlinear equation. Conditional on the isolated `hzero` decay
  input, every existence conjunct is now compiled. The remaining work is to
  prove that decay input and the converse representation used for uniqueness.

  Closer hop 22 assembles those conditional facts into the exact existential
  shape consumed by the closing theorem. Given only `hzero`,
  `apm_m02a06_exists_solution_of_transform_tendsto` selects the Banach fixed
  point's total extension and proves `IsSolution`—including `ContDiffOn 2`,
  the nonlinear ODE, boundary value, and atTop decay—together with the frozen
  radius bound. Thus the existence half is now one application after the
  Green-decay lemma; the other remaining half is converse representation and
  uniqueness for arbitrary bounded classical solutions.
  -/
  rcases apm_m02a06_exists_solution f hf_smooth hf_compact C hC hf_bound
    ε hε hε_small with ⟨u, hu, hub⟩
  refine ⟨u, hu, hub, ?_⟩
  intro v hv hvb x hx
  let hzero := fun w : apm_m02a06_Ball C =>
    apm_m02a06_greenTransform_extend_tendsto_atTop f C ε w hC hε.le
      hf_smooth.continuous (apm_m02a06_tendsto_zero_of_compactSupport f hf_compact)
      hf_bound
  have hufix := apm_m02a06_solutionBall_fixed ε C f u hf_smooth hf_compact
    hC hε hε_small hf_bound hu hub
  have hvfix := apm_m02a06_solutionBall_fixed ε C f v hf_smooth hf_compact
    hC hε hε_small hf_bound hv hvb
  have hueq := apm_m02a06_eq_greenFixedPoint_of_eq f C ε hC hε hε_small
    hf_smooth.continuous hf_bound hzero
    (apm_m02a06_solutionBall ε C f u hC hu hub) hufix
  have hveq := apm_m02a06_eq_greenFixedPoint_of_eq f C ε hC hε hε_small
    hf_smooth.continuous hf_bound hzero
    (apm_m02a06_solutionBall ε C f v hC hv hvb) hvfix
  have hballs : apm_m02a06_solutionBall ε C f v hC hv hvb =
      apm_m02a06_solutionBall ε C f u hC hu hub := hveq.trans hueq.symm
  have heval := congrArg
    (fun w : apm_m02a06_Ball C => w.1 (⟨x, hx⟩ : Ici (0 : ℝ))) hballs
  change v x = u x at heval
  exact heval
