import Mathlib

/-!
# APM m97A02: Local surjectivity of a composition operator

## Statement repairs

None.

## Encoding questions

None. The space consists of the actual `C¹` functions on `[0,1]` anchored at
the cosine fixed point. Smallness is measured solely by the derivative norm
printed in the source, and the nonlinear equation is stated pointwise on the
whole interval.
-/

open Set

noncomputable section

def apm_m97A02_inSpace (α : ℝ) (x : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 1 x (Icc 0 1) ∧ x α = 0

def apm_m97A02_derivativeBound (x : ℝ → ℝ) (r : ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, |derivWithin x (Icc 0 1) t| < r

def apm_m97A02_isSolution (x y : ℝ → ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1,
    Real.sin (x t) + x (Real.cos t) = y t

/-- Cosine sends the interval on which the composition operator is defined
back into that interval. -/
lemma apm_m97A02_cos_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Real.cos t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact Real.cos_nonneg_of_mem_Icc ⟨(neg_nonpos.mpr Real.pi_div_two_pos.le).trans ht.1,
      ht.2.trans Real.one_le_pi_div_two⟩
  · exact Real.cos_le_one t

/-- The cosine fixed point makes the nonlinear composition preserve the
anchoring condition. -/
lemma apm_m97A02_anchor_preserved {α : ℝ} (hα : Real.cos α = α)
    {x : ℝ → ℝ} (hx : x α = 0) :
    Real.sin (x α) + x (Real.cos α) = 0 := by
  simp [hα, hx]

/-- The derivative-only norm controls pointwise values on the anchored space. -/
lemma apm_m97A02_anchored_pointwise_bound
    {α r t : ℝ} {x : ℝ → ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hx : ContDiffOn ℝ 1 x (Icc 0 1)) (hxα : x α = 0)
    (hder : ∀ s ∈ Icc (0 : ℝ) 1, |derivWithin x (Icc 0 1) s| < r) :
    |x t| ≤ r := by
  have hr : 0 < r := lt_of_le_of_lt (abs_nonneg _) (hder α hα)
  have hmv := Convex.norm_image_sub_le_of_norm_derivWithin_le
    hx.differentiableOn_one
    (fun s hs ↦ by simpa [Real.norm_eq_abs] using (hder s hs).le)
    (convex_Icc (0 : ℝ) 1) hα ht
  have hdist : |t - α| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hα.1, hα.2, ht.1, ht.2]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hxα, sub_zero] at hmv
  exact hmv.trans (mul_le_of_le_one_right hr.le hdist)

/-- The quantitative constant in the derivative norm of composition by cosine
is strictly contractive on `[0,1]`. -/
lemma apm_m97A02_sin_one_lt_one : Real.sin 1 < 1 := by
  have h : Real.sin 1 < Real.sin (Real.pi / 2) := Real.strictMonoOn_sin
    ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
    ⟨by linarith [Real.pi_pos], le_rfl⟩
    (by linarith [Real.pi_gt_three])
  simpa only [Real.sin_pi_div_two] using h

/-- Scalar estimate behind the local Lipschitz bound for the nonlinear
remainder `x ↦ sin x - x`.  Using the global Lipschitz estimate for cosine
avoids needing a separate second-order Taylor bound. -/
lemma apm_m97A02_cos_remainder_mul_sub
    (x y u v : ℝ) :
    |(Real.cos x - 1) * u - (Real.cos y - 1) * v| ≤
      |x| * |u - v| + |x - y| * |v| := by
  rw [show (Real.cos x - 1) * u - (Real.cos y - 1) * v =
      (Real.cos x - 1) * (u - v) + (Real.cos x - Real.cos y) * v by ring]
  calc
    _ ≤ |Real.cos x - 1| * |u - v| +
        |Real.cos x - Real.cos y| * |v| := by
      simpa only [abs_mul] using abs_add_le
        ((Real.cos x - 1) * (u - v)) ((Real.cos x - Real.cos y) * v)
    _ ≤ |x| * |u - v| + |x - y| * |v| := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right
          (by simpa using Real.abs_cos_sub_cos_le x 0) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right
          (Real.abs_cos_sub_cos_le x y) (abs_nonneg _))

/-- Exact derivative formula for the nonlinear remainder used in the
contraction argument. -/
lemma apm_m97A02_derivWithin_sin_sub_self
    {x : ℝ → ℝ} (hx : ContDiffOn ℝ 1 x (Icc 0 1))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    derivWithin (fun s ↦ Real.sin (x s) - x s) (Icc 0 1) t =
      (Real.cos (x t) - 1) * derivWithin x (Icc 0 1) t := by
  have hxd : DifferentiableWithinAt ℝ x (Icc 0 1) t :=
    hx.differentiableOn_one t ht
  rw [show (fun s ↦ Real.sin (x s) - x s) = (fun s ↦ Real.sin (x s)) - x by rfl,
    derivWithin_sub (hxd.sin) hxd,
    derivWithin_sin hxd ((uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) t ht)]
  ring

/-- Pointwise derivative estimate for the difference of two nonlinear
remainders.  This is the calculus-level estimate used by the eventual
derivative-sup-norm contraction. -/
lemma apm_m97A02_derivWithin_remainder_sub_le
    {x y : ℝ → ℝ}
    (hx : ContDiffOn ℝ 1 x (Icc 0 1))
    (hy : ContDiffOn ℝ 1 y (Icc 0 1))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |derivWithin (fun s ↦ Real.sin (x s) - x s) (Icc 0 1) t -
        derivWithin (fun s ↦ Real.sin (y s) - y s) (Icc 0 1) t| ≤
      |x t| * |derivWithin x (Icc 0 1) t - derivWithin y (Icc 0 1) t| +
        |x t - y t| * |derivWithin y (Icc 0 1) t| := by
  rw [apm_m97A02_derivWithin_sin_sub_self hx ht,
    apm_m97A02_derivWithin_sin_sub_self hy ht]
  exact apm_m97A02_cos_remainder_mul_sub _ _ _ _

/-- Continuous derivative data reconstructs an anchored `C¹` function by
integration.  This is the completeness coordinate chart for the
derivative-only norm. -/
lemma apm_m97A02_reconstruct_from_derivative
    (α : ℝ) (g : ℝ → ℝ) (hg : Continuous g) :
    let x : ℝ → ℝ := fun t => ∫ s in α..t, g s
    apm_m97A02_inSpace α x ∧
      ∀ t ∈ Icc (0 : ℝ) 1, derivWithin x (Icc 0 1) t = g t := by
  let x : ℝ → ℝ := fun t => ∫ s in α..t, g s
  have hder (t : ℝ) : HasDerivAt x (g t) t := by
    exact (hg.integral_hasStrictDerivAt α t).hasDerivAt
  have hdiff : Differentiable ℝ x := fun t => (hder t).differentiableAt
  have hderiv : deriv x = g := by
    funext t
    exact (hder t).deriv
  have hxC : ContDiff ℝ 1 x := by
    rw [contDiff_one_iff_deriv]
    exact ⟨hdiff, hderiv ▸ hg⟩
  constructor
  · refine ⟨hxC.contDiffOn, ?_⟩
    simp [x]
  · intro t ht
    exact (hder t).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) t ht)

abbrev apm_m97A02_K := Set.Icc (0 : ℝ) 1

def apm_m97A02_cosMap : C(apm_m97A02_K, apm_m97A02_K) :=
  ⟨fun t => ⟨Real.cos t, apm_m97A02_cos_mem_Icc t.property⟩,
    Continuous.subtype_mk (Real.continuous_cos.comp continuous_subtype_val) _⟩

/-- The derivative-level composition term in the linearization. -/
noncomputable def apm_m97A02_linearComposition :
    C(apm_m97A02_K, ℝ) →L[ℝ] C(apm_m97A02_K, ℝ) := by
  let L : C(apm_m97A02_K, ℝ) →ₗ[ℝ] C(apm_m97A02_K, ℝ) :=
    { toFun := fun g =>
        ⟨fun t => Real.sin t * g (apm_m97A02_cosMap t),
          (Real.continuous_sin.comp continuous_subtype_val).mul
            (g.continuous.comp apm_m97A02_cosMap.continuous)⟩
      map_add' := by
        intro g h
        ext t
        simp [mul_add]
      map_smul' := by
        intro c g
        ext t
        simp
        ring }
  exact L.mkContinuous (Real.sin 1) (by
    intro g
    change ‖(⟨fun t => Real.sin t * g (apm_m97A02_cosMap t), _⟩ :
      C(apm_m97A02_K, ℝ))‖ ≤ Real.sin 1 * ‖g‖
    rw [ContinuousMap.norm_le _ (mul_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num)
        (by linarith [Real.pi_gt_three])) (norm_nonneg g))]
    intro t
    change ‖Real.sin (t : ℝ) * g (apm_m97A02_cosMap t)‖ ≤
      Real.sin 1 * ‖g‖
    rw [norm_mul, Real.norm_of_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi t.property.1
        (t.property.2.trans (by linarith [Real.pi_gt_three])))]
    exact mul_le_mul
      (Real.strictMonoOn_sin.monotoneOn
        (by constructor <;> linarith [Real.pi_gt_three, t.property.1, t.property.2])
        (by constructor <;> linarith [Real.pi_gt_three]) t.property.2)
      (ContinuousMap.norm_coe_le_norm g _) (norm_nonneg _)
      (Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num)
        (by linarith [Real.pi_gt_three])))

lemma apm_m97A02_linearComposition_apply
    (g : C(apm_m97A02_K, ℝ)) (t : apm_m97A02_K) :
    apm_m97A02_linearComposition g t =
      Real.sin t * g (apm_m97A02_cosMap t) := rfl

/-- Concrete non-vacuity of the derivative-level composition operator. -/
lemma apm_m97A02_linearComposition_one_at_one :
    apm_m97A02_linearComposition (1 : C(apm_m97A02_K, ℝ))
      ⟨1, by constructor <;> norm_num⟩ = Real.sin 1 := by
  simp [apm_m97A02_linearComposition_apply]

lemma apm_m97A02_norm_linearComposition_lt_one :
    ‖apm_m97A02_linearComposition‖ < 1 := by
  refine lt_of_le_of_lt (apm_m97A02_linearComposition.opNorm_le_bound
    (Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num)
      (by linarith [Real.pi_gt_three])) ?_) apm_m97A02_sin_one_lt_one
  intro g
  rw [ContinuousMap.norm_le _ (mul_nonneg
    (Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num)
      (by linarith [Real.pi_gt_three])) (norm_nonneg g))]
  intro t
  rw [apm_m97A02_linearComposition_apply, norm_mul,
    Real.norm_of_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi t.property.1
        (t.property.2.trans (by linarith [Real.pi_gt_three])))]
  exact mul_le_mul
    (Real.strictMonoOn_sin.monotoneOn
      (by constructor <;> linarith [Real.pi_gt_three, t.property.1, t.property.2])
      (by constructor <;> linarith [Real.pi_gt_three]) t.property.2)
    (ContinuousMap.norm_coe_le_norm g _) (norm_nonneg _)
    (Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num)
      (by linarith [Real.pi_gt_three]))

/-- The derivative-level linearization is onto, by its Neumann-series
inverse. -/
lemma apm_m97A02_linearized_surjective
    (h : C(apm_m97A02_K, ℝ)) :
    ∃ g : C(apm_m97A02_K, ℝ),
      g - apm_m97A02_linearComposition g = h := by
  have hunit : IsUnit
      (1 - apm_m97A02_linearComposition) :=
    isUnit_one_sub_of_norm_lt_one
      (x := apm_m97A02_linearComposition)
      apm_m97A02_norm_linearComposition_lt_one
  let u := hunit.unit
  refine ⟨(↑(u⁻¹) : C(apm_m97A02_K, ℝ) →L[ℝ]
      C(apm_m97A02_K, ℝ)) h, ?_⟩
  have hu : (↑u : C(apm_m97A02_K, ℝ) →L[ℝ]
      C(apm_m97A02_K, ℝ)) = 1 - apm_m97A02_linearComposition :=
    hunit.unit_spec
  have hi := congrArg
    (fun L : C(apm_m97A02_K, ℝ) →L[ℝ] C(apm_m97A02_K, ℝ) => L h)
    u.mul_inv
  rw [hu] at hi
  simpa using hi

/-- Integration from the anchor, as a norm-one bounded operator on continuous
derivative data. -/
noncomputable def apm_m97A02_integration (α : ℝ)
    (hα : α ∈ Icc (0 : ℝ) 1) :
    C(apm_m97A02_K, ℝ) →L[ℝ] C(apm_m97A02_K, ℝ) := by
  let L : C(apm_m97A02_K, ℝ) →ₗ[ℝ] C(apm_m97A02_K, ℝ) :=
    { toFun := fun g =>
        ⟨fun t => ∫ s in α..(t : ℝ), ContinuousMap.IccExtendCM g s,
          continuous_iff_continuousAt.2 fun t =>
            ((ContinuousMap.IccExtendCM g).continuous.integral_hasStrictDerivAt
              α t).hasDerivAt.continuousAt.comp continuous_subtype_val.continuousAt⟩
      map_add' := by
        intro g h
        ext t
        change (∫ s in α..(t : ℝ), ContinuousMap.IccExtendCM (g + h) s) =
          (∫ s in α..(t : ℝ), ContinuousMap.IccExtendCM g s) +
            ∫ s in α..(t : ℝ), ContinuousMap.IccExtendCM h s
        rw [← intervalIntegral.integral_add
          ((ContinuousMap.IccExtendCM g).continuous.intervalIntegrable _ _)
          ((ContinuousMap.IccExtendCM h).continuous.intervalIntegrable _ _)]
        rfl
      map_smul' := by
        intro c g
        ext t
        change (∫ s in α..(t : ℝ), ContinuousMap.IccExtendCM (c • g) s) =
          c • ∫ s in α..(t : ℝ), ContinuousMap.IccExtendCM g s
        rw [← intervalIntegral.integral_smul c
          (ContinuousMap.IccExtendCM g : ℝ → ℝ)]
        congr 1 }
  exact L.mkContinuous 1 (by
    intro g
    simp only [one_mul]
    change ‖(⟨fun t => ∫ s in α..(t : ℝ), ContinuousMap.IccExtendCM g s, _⟩ :
      C(apm_m97A02_K, ℝ))‖ ≤ ‖g‖
    rw [ContinuousMap.norm_le _ (norm_nonneg g)]
    intro t
    change ‖∫ s in α..(t : ℝ), ContinuousMap.IccExtendCM g s‖ ≤ ‖g‖
    calc
      _ ≤ ‖g‖ * |(t : ℝ) - α| :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (fun s hs => ContinuousMap.norm_coe_le_norm g _)
      _ ≤ ‖g‖ := by
        have hd : |(t : ℝ) - α| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith [hα.1, hα.2, t.property.1, t.property.2]
        simpa using mul_le_of_le_one_right (norm_nonneg g) hd)

lemma apm_m97A02_integration_apply (α : ℝ) (hα : α ∈ Icc (0 : ℝ) 1)
    (g : C(apm_m97A02_K, ℝ)) (t : apm_m97A02_K) :
    apm_m97A02_integration α hα g t =
      ∫ s in α..(t : ℝ), ContinuousMap.IccExtendCM g s := rfl

/-- Concrete non-vacuity: integrating the constant-one derivative returns
the displacement from the anchor. -/
lemma apm_m97A02_integration_one (α : ℝ) (hα : α ∈ Icc (0 : ℝ) 1)
    (t : apm_m97A02_K) :
    apm_m97A02_integration α hα (1 : C(apm_m97A02_K, ℝ)) t =
      (t : ℝ) - α := by
  rw [apm_m97A02_integration_apply]
  change (∫ _ in α..(t : ℝ), (1 : ℝ)) = (t : ℝ) - α
  simp

lemma apm_m97A02_integration_norm_le (α : ℝ)
    (hα : α ∈ Icc (0 : ℝ) 1) (g : C(apm_m97A02_K, ℝ)) :
    ‖apm_m97A02_integration α hα g‖ ≤ ‖g‖ := by
  rw [ContinuousMap.norm_le _ (norm_nonneg g)]
  intro t
  rw [apm_m97A02_integration_apply]
  calc
    _ ≤ ‖g‖ * |(t : ℝ) - α| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (fun s hs => ContinuousMap.norm_coe_le_norm g _)
    _ ≤ ‖g‖ := by
      have hd : |(t : ℝ) - α| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [hα.1, hα.2, t.property.1, t.property.2]
      simpa using mul_le_of_le_one_right (norm_nonneg g) hd

def apm_m97A02_cosContinuousMap (g : C(apm_m97A02_K, ℝ)) :
    C(apm_m97A02_K, ℝ) :=
  ⟨fun t => Real.cos (g t), Real.continuous_cos.comp g.continuous⟩

noncomputable def apm_m97A02_derivativeNonlinearMap
    (α : ℝ) (hα : α ∈ Icc (0 : ℝ) 1)
    (g : C(apm_m97A02_K, ℝ)) : C(apm_m97A02_K, ℝ) :=
  apm_m97A02_cosContinuousMap (apm_m97A02_integration α hα g) * g -
    apm_m97A02_linearComposition g

lemma apm_m97A02_product_remainder_norm_le
    (α : ℝ) (hα : α ∈ Icc (0 : ℝ) 1)
    (g h : C(apm_m97A02_K, ℝ)) :
    ‖apm_m97A02_cosContinuousMap (apm_m97A02_integration α hα g) * g -
        apm_m97A02_cosContinuousMap (apm_m97A02_integration α hα h) * h -
        (g - h)‖ ≤
      (‖g‖ + ‖h‖) * ‖g - h‖ := by
  rw [ContinuousMap.norm_le _ (mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
    (norm_nonneg _))]
  intro t
  change ‖Real.cos (apm_m97A02_integration α hα g t) * g t -
      Real.cos (apm_m97A02_integration α hα h t) * h t -
      (g t - h t)‖ ≤ (‖g‖ + ‖h‖) * ‖g - h‖
  rw [show Real.cos (apm_m97A02_integration α hα g t) * g t -
      Real.cos (apm_m97A02_integration α hα h t) * h t - (g t - h t) =
      (Real.cos (apm_m97A02_integration α hα g t) - 1) * (g t - h t) +
      (Real.cos (apm_m97A02_integration α hα g t) -
        Real.cos (apm_m97A02_integration α hα h t)) * h t by ring]
  calc
    _ ≤ |Real.cos (apm_m97A02_integration α hα g t) - 1| * ‖g t - h t‖ +
        |Real.cos (apm_m97A02_integration α hα g t) -
          Real.cos (apm_m97A02_integration α hα h t)| * ‖h t‖ := by
      simpa [Real.norm_eq_abs, abs_mul] using norm_add_le
        ((Real.cos (apm_m97A02_integration α hα g t) - 1) * (g t - h t))
        ((Real.cos (apm_m97A02_integration α hα g t) -
          Real.cos (apm_m97A02_integration α hα h t)) * h t)
    _ ≤ ‖g‖ * ‖g - h‖ + ‖g - h‖ * ‖h‖ := by
      apply add_le_add
      · have ha : |Real.cos (apm_m97A02_integration α hα g t) - 1| ≤ ‖g‖ := by
          calc
            _ ≤ |apm_m97A02_integration α hα g t - 0| := by
              have hc := Real.abs_cos_sub_cos_le
                (apm_m97A02_integration α hα g t) 0
              simpa using hc
            _ ≤ ‖apm_m97A02_integration α hα g‖ := by
              simpa using ContinuousMap.norm_coe_le_norm
                (apm_m97A02_integration α hα g) t
            _ ≤ ‖g‖ := apm_m97A02_integration_norm_le α hα g
        calc
          _ ≤ ‖g‖ * ‖g t - h t‖ :=
            mul_le_mul_of_nonneg_right ha (norm_nonneg _)
          _ ≤ ‖g‖ * ‖g - h‖ := mul_le_mul_of_nonneg_left
            (by simpa using ContinuousMap.norm_coe_le_norm (g - h) t) (norm_nonneg g)
      · have ha : |Real.cos (apm_m97A02_integration α hα g t) -
            Real.cos (apm_m97A02_integration α hα h t)| ≤ ‖g - h‖ := by
          calc
            _ ≤ |apm_m97A02_integration α hα g t -
                apm_m97A02_integration α hα h t| := Real.abs_cos_sub_cos_le _ _
            _ = ‖apm_m97A02_integration α hα (g - h) t‖ := by
              rw [map_sub]
              rfl
            _ ≤ ‖apm_m97A02_integration α hα (g - h)‖ :=
              ContinuousMap.norm_coe_le_norm _ _
            _ ≤ ‖g - h‖ := apm_m97A02_integration_norm_le α hα (g - h)
        calc
          _ ≤ ‖g - h‖ * ‖h t‖ :=
            mul_le_mul_of_nonneg_right ha (norm_nonneg _)
          _ ≤ ‖g - h‖ * ‖h‖ := mul_le_mul_of_nonneg_left
            (ContinuousMap.norm_coe_le_norm h t) (norm_nonneg (g - h))
    _ ≤ (‖g‖ + ‖h‖) * ‖g - h‖ := by
      exact le_of_eq (by ring)

lemma apm_m97A02_hasStrictFDerivAt_derivativeNonlinearMap
    (α : ℝ) (hα : α ∈ Icc (0 : ℝ) 1) :
    HasStrictFDerivAt (apm_m97A02_derivativeNonlinearMap α hα)
      (1 - apm_m97A02_linearComposition) 0 := by
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hcont : ContinuousAt
      (fun p : C(apm_m97A02_K, ℝ) × C(apm_m97A02_K, ℝ) =>
        ‖p.1‖ + ‖p.2‖) (0, 0) := by fun_prop
  have hev : ∀ᶠ p : C(apm_m97A02_K, ℝ) × C(apm_m97A02_K, ℝ) in nhds (0, 0),
      ‖p.1‖ + ‖p.2‖ ≤ c := by
    filter_upwards [hcont (Iio_mem_nhds (by simpa using hc))] with p hp
    simpa using hp.le
  filter_upwards [hev] with p hp
  have hre := apm_m97A02_product_remainder_norm_le α hα p.1 p.2
  have heq :
      apm_m97A02_derivativeNonlinearMap α hα p.1 -
          apm_m97A02_derivativeNonlinearMap α hα p.2 -
          (1 - apm_m97A02_linearComposition) (p.1 - p.2) =
        apm_m97A02_cosContinuousMap (apm_m97A02_integration α hα p.1) * p.1 -
          apm_m97A02_cosContinuousMap (apm_m97A02_integration α hα p.2) * p.2 -
          (p.1 - p.2) := by
    simp only [apm_m97A02_derivativeNonlinearMap,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, map_sub]
    abel
  rw [heq]
  exact hre.trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _))

lemma apm_m97A02_derivativeNonlinearMap_map_nhds
    (α : ℝ) (hα : α ∈ Icc (0 : ℝ) 1) :
    Filter.map (apm_m97A02_derivativeNonlinearMap α hα)
        (nhds (0 : C(apm_m97A02_K, ℝ))) =
      nhds (apm_m97A02_derivativeNonlinearMap α hα 0) := by
  let L : C(apm_m97A02_K, ℝ) →L[ℝ] C(apm_m97A02_K, ℝ) :=
    1 - apm_m97A02_linearComposition
  have hunit : IsUnit L := by
    dsimp [L]
    exact isUnit_one_sub_of_norm_lt_one
      (x := apm_m97A02_linearComposition)
      apm_m97A02_norm_linearComposition_lt_one
  have hb : Function.Bijective L :=
    ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  let e : C(apm_m97A02_K, ℝ) ≃L[ℝ] C(apm_m97A02_K, ℝ) :=
    ContinuousLinearEquiv.ofBijective L
      (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  apply HasStrictFDerivAt.map_nhds_eq_of_equiv (f' := e)
  simpa [L, e] using
    apm_m97A02_hasStrictFDerivAt_derivativeNonlinearMap α hα

lemma apm_m97A02_derivativeNonlinearMap_locally_surjective
    (α : ℝ) (hα : α ∈ Icc (0 : ℝ) 1) :
    ∃ δ : ℝ, 0 < δ ∧
      Metric.ball (0 : C(apm_m97A02_K, ℝ)) δ ⊆
        Set.range (apm_m97A02_derivativeNonlinearMap α hα) := by
  have hrange : Set.range (apm_m97A02_derivativeNonlinearMap α hα) ∈
      nhds (0 : C(apm_m97A02_K, ℝ)) := by
    have hm := apm_m97A02_derivativeNonlinearMap_map_nhds α hα
    have hz : apm_m97A02_derivativeNonlinearMap α hα 0 = 0 := by
      ext t
      simp [apm_m97A02_derivativeNonlinearMap,
        apm_m97A02_cosContinuousMap]
    rw [hz] at hm
    rw [← hm]
    change (apm_m97A02_derivativeNonlinearMap α hα) ⁻¹'
      Set.range (apm_m97A02_derivativeNonlinearMap α hα) ∈
        nhds (0 : C(apm_m97A02_K, ℝ))
    exact Filter.Eventually.of_forall (fun g => Set.mem_range_self g)
  rcases Metric.mem_nhds_iff.mp hrange with ⟨δ, hδ, hball⟩
  exact ⟨δ, hδ, hball⟩

def apm_m97A02_derivativeData (y : ℝ → ℝ)
    (hy : ContDiffOn ℝ 1 y (Icc (0 : ℝ) 1)) :
    C(apm_m97A02_K, ℝ) :=
  ⟨fun t => derivWithin y (Icc 0 1) t,
    (hy.continuousOn_derivWithin (uniqueDiffOn_Icc (by norm_num))
      (by norm_num)).restrict⟩

lemma apm_m97A02_derivativeData_mem_ball
    {y : ℝ → ℝ} {δ : ℝ}
    (hy : ContDiffOn ℝ 1 y (Icc (0 : ℝ) 1))
    (hδ : 0 < δ) (hbound : apm_m97A02_derivativeBound y δ) :
    apm_m97A02_derivativeData y hy ∈
      Metric.ball (0 : C(apm_m97A02_K, ℝ)) δ := by
  rw [Metric.mem_ball, dist_zero_right,
    ContinuousMap.norm_lt_iff _ hδ]
  intro t
  change |derivWithin y (Icc 0 1) t| < δ
  exact hbound t t.property

lemma apm_m97A02_solution_of_derivativeNonlinearMap_eq
    {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) (hfix : Real.cos α = α)
    {y : ℝ → ℝ} (hy : apm_m97A02_inSpace α y)
    (g : C(apm_m97A02_K, ℝ))
    (hg : apm_m97A02_derivativeNonlinearMap α hα g =
      apm_m97A02_derivativeData y hy.1) :
    ∃ x : ℝ → ℝ, apm_m97A02_inSpace α x ∧
      apm_m97A02_isSolution x y := by
  let G : C(ℝ, ℝ) := ContinuousMap.IccExtendCM g
  let x : ℝ → ℝ := fun t => ∫ s in α..t, G s
  have hxrec := apm_m97A02_reconstruct_from_derivative α G G.continuous
  have hxspace : apm_m97A02_inSpace α x := hxrec.1
  have hxder (t : ℝ) : HasDerivAt x (G t) t := by
    exact (G.continuous.integral_hasStrictDerivAt α t).hasDerivAt
  let z : ℝ → ℝ := fun t => Real.sin (x t) + x (Real.cos t) - y t
  have hzder : ∀ t ∈ Icc (0 : ℝ) 1,
      derivWithin z (Icc 0 1) t = 0 := by
    intro t ht
    have hu := uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1) t ht
    have hmain : HasDerivAt (fun s => Real.sin (x s) + x (Real.cos s))
        (Real.cos (x t) * G t + G (Real.cos t) * (-Real.sin t)) t := by
      exact (hxder t).sin.add
        ((hxder (Real.cos t)).comp t (Real.hasDerivAt_cos t))
    have hyd := (hy.1.differentiableOn_one t ht).hasDerivWithinAt
    have hzd := hmain.hasDerivWithinAt.sub hyd
    change derivWithin ((fun s => Real.sin (x s) + x (Real.cos s)) - y)
      (Icc 0 1) t = 0
    rw [hzd.derivWithin hu]
    have hp := congrArg (fun q : C(apm_m97A02_K, ℝ) => q ⟨t, ht⟩) hg
    change Real.cos (x t) * G t + G (Real.cos t) * (-Real.sin t) -
      derivWithin y (Icc 0 1) t = 0
    have hxt : x t = apm_m97A02_integration α hα g ⟨t, ht⟩ := rfl
    have hGt : G t = g ⟨t, ht⟩ := by simp [G, ht]
    have hGc : G (Real.cos t) = g (apm_m97A02_cosMap ⟨t, ht⟩) := by
      simp [G, apm_m97A02_cosMap, apm_m97A02_cos_mem_Icc ht]
    rw [hxt, hGt, hGc]
    change Real.cos (apm_m97A02_integration α hα g ⟨t, ht⟩) * g ⟨t, ht⟩ -
      apm_m97A02_linearComposition g ⟨t, ht⟩ =
        derivWithin y (Icc 0 1) t at hp
    rw [apm_m97A02_linearComposition_apply] at hp
    nlinarith
  have hzdiff : DifferentiableOn ℝ z (Icc (0 : ℝ) 1) := by
    intro t ht
    exact ((hxder t).differentiableAt.sin.add
      ((hxder (Real.cos t)).differentiableAt.comp t Real.differentiableAt_cos)).differentiableWithinAt.sub
        (hy.1.differentiableOn_one t ht)
  have hzconst : ∀ t ∈ Icc (0 : ℝ) 1, z t = z α := by
    intro t ht
    have hmv := Convex.norm_image_sub_le_of_norm_derivWithin_le (C := 0) hzdiff
      (fun s hs => by simp [hzder s hs]) (convex_Icc (0 : ℝ) 1) hα ht
    have : ‖z t - z α‖ = 0 := le_antisymm (by simpa using hmv) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  refine ⟨x, hxspace, ?_⟩
  intro t ht
  have hzα : z α = 0 := by
    simp [z, hfix, hxspace.2, hy.2]
  have := hzconst t ht
  simp only [z, hzα] at this
  linarith

theorem apm_m97a02 :
    ∀ α : ℝ, α ∈ Icc (0 : ℝ) 1 → Real.cos α = α →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ y : ℝ → ℝ,
          apm_m97A02_inSpace α y →
          apm_m97A02_derivativeBound y δ →
            ∃ x : ℝ → ℝ,
              apm_m97A02_inSpace α x ∧
              apm_m97A02_isSolution x y := by
  /-
  PARTIAL. `apm_m97A02_cos_mem_Icc` proves that the composition operator is
  well-defined on `[0,1]`, while `apm_m97A02_anchor_preserved` proves that the
  nonlinear map preserves the Dottie-number anchoring condition.  This pass
  also proves `apm_m97A02_anchored_pointwise_bound`: Mathlib's convex-set mean
  value theorem turns the derivative bound into the required anchored
  Poincaré estimate `|x t| ≤ r` throughout the interval.

  The remaining inverse-function/contraction argument must build the Banach
  space of anchored `C¹` functions with derivative sup norm, prove its
  completeness via the integration equivalence, bundle `x ↦ x ∘ cos` as a
  bounded linear map with norm at most `sin 1 < 1`, and establish the local
  Lipschitz estimate for `sin ∘ x - x`. Mathlib supplies Neumann-series and
  `ContractingWith` infrastructure, but searches of `LEMMA-INDEX.md`, 172
  closed artifacts, `ConstructionTargets/`, `YoungL2.lean`, and Mathlib's
  continuous-map/derivative equivalence APIs found no assembly for this custom
  derivative-only normed space.  The remaining boundary is therefore
  functional-analytic packaging rather than the pointwise norm control.

  Closer hop 1 additionally isolates the strict contraction constant as
  `apm_m97A02_sin_one_lt_one`, using `Real.strictMonoOn_sin` on
  `[-π/2, π/2]`.  Searches of Mathlib's `C¹`/continuous-map integration,
  bounded composition, closed-subspace completeness, Neumann-series, and
  contraction APIs, plus the closed corpus and construction libraries, found
  no packaged anchored derivative-norm space.  Thus the analytic constant
  `sin 1 < 1` and the anchored Poincaré bound are both compiled; the remaining
  bridge is still the Banach-space model and the nonlinear local Lipschitz
  estimate inside that model.

  Closer hop 2 proves `apm_m97A02_cos_remainder_mul_sub`, the scalar product
  estimate needed after differentiating the nonlinear remainder.  It routes
  around the informal proof's quadratic Taylor estimate by using Mathlib's
  global `Real.abs_cos_sub_cos_le`; on a derivative ball, the resulting bound
  is linear in the radius and therefore still tends to zero.  Searches of
  `LEMMA-INDEX.md`, the closed corpus, Mathlib's `C¹` function spaces,
  continuous-map integration, and git history again found no complete normed
  model for anchored `ContDiffOn` functions.  The remaining boundary is to
  combine this scalar estimate with `derivWithin` chain/product rules and to
  construct the complete derivative-norm space on which contraction applies.

  Closer hop 3 closes the calculus half of that boundary.  The helper
  `apm_m97A02_derivWithin_sin_sub_self` proves the exact endpoint-valid formula
  for the derivative of `sin ∘ x - x`, using `derivWithin_sin` and the
  `UniqueDiffWithinAt` instance supplied by the nondegenerate interval.
  `apm_m97A02_derivWithin_remainder_sub_le` then combines this formula with
  the hop-2 scalar inequality, yielding the pointwise derivative estimate for
  two nonlinear remainders in precisely the form needed by the sup norm.
  Renewed searches of `LEMMA-INDEX.md`, Mathlib's `ContDiffOn`, continuous-map
  integration, normed-function-space and contraction APIs, the closed corpus,
  `ConstructionTargets/`, and `YoungL2.lean` found no packaged complete space
  whose elements are anchored `C¹` functions and whose norm is only the
  derivative supremum.  Constructing that Banach model, the bounded inverse of
  the linearized composition operator, and the final contraction therefore
  remains open.

  HOP 4 isolates the missing completeness theorem without postulating a new
  normed-space structure. The exact required contract is:

  ```lean
  theorem apm_m97A02_anchored_derivative_cauchy_complete
      (α : ℝ) (hα : α ∈ Icc (0 : ℝ) 1)
      (x : ℕ → ℝ → ℝ)
      (hx : ∀ n, apm_m97A02_inSpace α (x n))
      (hcauchy : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
        ∀ t ∈ Icc (0 : ℝ) 1,
          |derivWithin (x m) (Icc 0 1) t -
            derivWithin (x n) (Icc 0 1) t| < ε) :
      ∃ xlim : ℝ → ℝ,
        apm_m97A02_inSpace α xlim ∧
        ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ t ∈ Icc (0 : ℝ) 1,
          |derivWithin (x n) (Icc 0 1) t -
            derivWithin xlim (Icc 0 1) t| < ε
  ```

  This is true by taking the uniform limit of the continuous derivatives on
  `Icc 0 1` and integrating it from the anchor `α`. It is precisely the
  completeness fact needed to turn the anchored derivative-sup metric into a
  complete space. No existing Mathlib declaration found in this hop packages
  this reconstruction; the subsequent bounded-composition and contraction
  assembly therefore also remains open.
  -/
  intro α hα hfix
  rcases apm_m97A02_derivativeNonlinearMap_locally_surjective α hα with
    ⟨δ, hδ, hsurj⟩
  refine ⟨δ, hδ, ?_⟩
  intro y hy hbound
  have hmem := apm_m97A02_derivativeData_mem_ball hy.1 hδ hbound
  rcases hsurj hmem with ⟨g, hg⟩
  exact apm_m97A02_solution_of_derivativeNonlinearMap_eq hα hfix hy g hg
