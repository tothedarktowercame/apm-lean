import Mathlib

/-!
# APM m98A03

## Statement repairs

None.

## Encoding notes

`C([0,1])` is Mathlib's genuine Banach space of continuous maps on the
subtype `[0,1]`, equipped with its sup norm.  Lebesgue measure on that subtype
is used directly in the Hammerstein integral.
-/

open MeasureTheory Set

abbrev apm_m98a03_C01 := ContinuousMap (Icc (0 : ℝ) 1) ℝ

def apm_m98a03_IsFrechetDerivativeAtOn
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Set X) (F : X → Y) (x : X) (A : X →L[ℝ] Y) : Prop :=
  IsOpen U ∧ x ∈ U ∧ HasFDerivWithinAt F A U x

def apm_m98a03_IsHammersteinOperator
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (f : ℝ → ℝ) (F : apm_m98a03_C01 → apm_m98a03_C01) : Prop :=
  ∀ (u : apm_m98a03_C01) (x : Icc (0 : ℝ) 1),
    F u x = ∫ y : Icc (0 : ℝ) 1, K (x, y) * f (u y)

lemma apm_m98a03_integrable_kernel_section
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (f : ℝ → ℝ) (hf : Continuous f) (u : apm_m98a03_C01)
    (x : Icc (0 : ℝ) 1) :
    Integrable (fun y : Icc (0 : ℝ) 1 => K (x, y) * f (u y)) := by
  let q : ContinuousMap (Icc (0 : ℝ) 1) ℝ :=
    ⟨fun y => K (x, y) * f (u y), by fun_prop⟩
  simpa [q] using (BoundedContinuousFunction.mkOfCompact q).integrable volume

/-- Every section of the proposed derivative kernel is integrable on the
compact parameter interval. -/
lemma apm_m98a03_integrable_derivative_kernel_section
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (u h : apm_m98a03_C01) (x : Icc (0 : ℝ) 1) :
    Integrable (fun y : Icc (0 : ℝ) 1 ↦
      K (x, y) * deriv f (u y) * h y) := by
  let q : ContinuousMap (Icc (0 : ℝ) 1) ℝ :=
    ⟨fun y ↦ K (x, y) * deriv f (u y) * h y, by
      exact ((K.continuous.comp (continuous_const.prodMk continuous_id)).mul
        (hf.continuous_deriv_one.comp u.continuous)).mul h.continuous⟩
  simpa [q] using (BoundedContinuousFunction.mkOfCompact q).integrable volume

/-- A uniform pointwise majorant for the derivative kernel.  This is the
estimate required by the dominated parametric-integral theorem once a bound
for `deriv f` has been chosen on the relevant compact range. -/
lemma apm_m98a03_derivative_kernel_norm_le
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (f : ℝ → ℝ) (u h : apm_m98a03_C01)
    (M : ℝ) (hM : ∀ z : ℝ, |deriv f z| ≤ M)
    (x y : Icc (0 : ℝ) 1) :
    |K (x, y) * deriv f (u y) * h y| ≤ ‖K‖ * M * ‖h‖ := by
  rw [abs_mul, abs_mul]
  exact mul_le_mul
    (mul_le_mul (K.norm_coe_le_norm (x, y)) (hM (u y))
      (abs_nonneg _) (norm_nonneg _))
    (h.norm_coe_le_norm y) (abs_nonneg _) (mul_nonneg (norm_nonneg _) (by
      exact (abs_nonneg _).trans (hM (u y))))

/-- The constant majorant occurring in
`apm_m98a03_derivative_kernel_norm_le` is integrable because the parameter
interval has finite volume. -/
lemma apm_m98a03_integrable_derivative_majorant
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ) (M : ℝ) :
    Integrable (fun _ : Icc (0 : ℝ) 1 ↦ ‖K‖ * M) := by
  exact integrable_const _

/-- Continuity of the scalar derivative supplies a uniform bound on every
compact interval. -/
lemma apm_m98a03_exists_deriv_bound_on_Icc
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (a b : ℝ) :
    ∃ M : ℝ, ∀ z ∈ Icc a b, |deriv f z| ≤ M := by
  have hcont : Continuous (fun z : ℝ ↦ |deriv f z|) :=
    hf.continuous_deriv_one.abs
  obtain ⟨M, hM⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image hcont.continuousOn)
  refine ⟨M, ?_⟩
  intro z hz
  exact hM _ (mem_image_of_mem _ hz)

/-- The compact derivative bound can be chosen uniformly for every function
in the open unit sup-norm neighborhood of a fixed input. -/
lemma apm_m98a03_exists_local_deriv_bound
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (u : apm_m98a03_C01) :
    ∃ M : ℝ, ∀ v : apm_m98a03_C01, dist v u < 1 →
      ∀ y : Icc (0 : ℝ) 1, |deriv f (v y)| ≤ M := by
  obtain ⟨M, hM⟩ := apm_m98a03_exists_deriv_bound_on_Icc f hf
    (-(‖u‖ + 1)) (‖u‖ + 1)
  refine ⟨M, ?_⟩
  intro v hv y
  apply hM
  have hvu : ‖v - u‖ < 1 := by simpa [dist_eq_norm] using hv
  have huv : |v y - u y| < 1 := by
    exact lt_of_le_of_lt (by simpa [Real.norm_eq_abs] using
      (v - u).norm_coe_le_norm y) hvu
  have hu : |u y| ≤ ‖u‖ := by
    simpa [Real.norm_eq_abs] using u.norm_coe_le_norm y
  have hvabs : |v y| < ‖u‖ + 1 := calc
    |v y| = |(v y - u y) + u y| := by ring_nf
    _ ≤ |v y - u y| + |u y| := abs_add_le _ _
    _ < 1 + ‖u‖ := add_lt_add_of_lt_of_le huv hu
    _ = ‖u‖ + 1 := by ring
  exact ⟨by linarith [neg_abs_le (v y)], by linarith [le_abs_self (v y)]⟩

noncomputable def apm_m98a03_hammerstein
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (f : ℝ → ℝ) (hf : Continuous f) :
    apm_m98a03_C01 → apm_m98a03_C01 := fun u =>
  ⟨fun x => ∫ y : Icc (0 : ℝ) 1, K (x, y) * f (u y), by
    simpa using
      (continuous_parametric_integral_of_continuous
        (s := Set.univ)
        (show Continuous (Function.uncurry
          (fun x : Icc (0 : ℝ) 1 => fun y : Icc (0 : ℝ) 1 =>
            K (x, y) * f (u y))) by fun_prop)
        isCompact_univ)⟩

lemma apm_m98a03_hammerstein_apply
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (f : ℝ → ℝ) (hf : Continuous f) (u : apm_m98a03_C01)
    (x : Icc (0 : ℝ) 1) :
    apm_m98a03_hammerstein K f hf u x =
      ∫ y : Icc (0 : ℝ) 1, K (x, y) * f (u y) := rfl

lemma apm_m98a03_hammerstein_spec
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (f : ℝ → ℝ) (hf : Continuous f) :
    apm_m98a03_IsHammersteinOperator K f
      (apm_m98a03_hammerstein K f hf) := by
  intro u x
  rfl

noncomputable def apm_m98a03_weightedIntegralOperator
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (a : apm_m98a03_C01) : apm_m98a03_C01 →L[ℝ] apm_m98a03_C01 := by
  let L : apm_m98a03_C01 →ₗ[ℝ] apm_m98a03_C01 :=
    { toFun := fun h =>
        ⟨fun x => ∫ y : Icc (0 : ℝ) 1, K (x, y) * a y * h y, by
          simpa using
            (continuous_parametric_integral_of_continuous
              (s := Set.univ)
              (show Continuous (Function.uncurry
                (fun x : Icc (0 : ℝ) 1 => fun y : Icc (0 : ℝ) 1 =>
                  K (x, y) * a y * h y)) by fun_prop)
              isCompact_univ)⟩
      map_add' := by
        intro h₁ h₂
        ext x
        simp only [ContinuousMap.coe_mk, ContinuousMap.add_apply]
        rw [← integral_add]
        · congr 1
          funext y
          ring
        · exact (BoundedContinuousFunction.mkOfCompact
            (⟨fun y => K (x, y) * a y * h₁ y, by fun_prop⟩ :
              C(Icc (0 : ℝ) 1, ℝ))).integrable volume
        · exact (BoundedContinuousFunction.mkOfCompact
            (⟨fun y => K (x, y) * a y * h₂ y, by fun_prop⟩ :
              C(Icc (0 : ℝ) 1, ℝ))).integrable volume
      map_smul' := by
        intro c h
        ext x
        simp only [ContinuousMap.coe_mk, ContinuousMap.smul_apply, smul_eq_mul]
        rw [← integral_const_mul]
        congr 1
        funext y
        simp only [RingHom.id_apply]
        ring }
  exact L.mkContinuous (‖K‖ * ‖a‖) (by
    intro h
    rw [ContinuousMap.norm_le _ (mul_nonneg (mul_nonneg (norm_nonneg K)
      (norm_nonneg a)) (norm_nonneg h))]
    intro x
    calc
      _ ≤ (‖K‖ * ‖a‖ * ‖h‖) * (volume : Measure (Icc (0 : ℝ) 1)).real univ :=
        MeasureTheory.norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall
          (fun y => by
            simp only [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul
              (mul_le_mul (K.norm_coe_le_norm (x, y)) (a.norm_coe_le_norm y)
                (abs_nonneg _) (norm_nonneg K))
              (h.norm_coe_le_norm y) (abs_nonneg _)
              (mul_nonneg (norm_nonneg K) (norm_nonneg a))))
      _ = ‖K‖ * ‖a‖ * ‖h‖ := by norm_num)

lemma apm_m98a03_weightedIntegralOperator_apply
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (a h : apm_m98a03_C01) (x : Icc (0 : ℝ) 1) :
    apm_m98a03_weightedIntegralOperator K a h x =
      ∫ y : Icc (0 : ℝ) 1, K (x, y) * a y * h y := rfl

set_option maxHeartbeats 800000 in
lemma apm_m98a03_weightedIntegralOperator_norm_le
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (a : apm_m98a03_C01) :
    ‖apm_m98a03_weightedIntegralOperator K a‖ ≤ ‖K‖ * ‖a‖ := by
  refine ContinuousLinearMap.opNorm_le_bound
    (apm_m98a03_weightedIntegralOperator K a)
    (mul_nonneg (norm_nonneg K) (norm_nonneg a)) ?_
  intro h
  rw [ContinuousMap.norm_le _ (mul_nonneg (mul_nonneg (norm_nonneg K)
    (norm_nonneg a)) (norm_nonneg h))]
  intro x
  rw [apm_m98a03_weightedIntegralOperator_apply]
  calc
    _ ≤ (‖K‖ * ‖a‖ * ‖h‖) * (volume : Measure (Icc (0 : ℝ) 1)).real univ :=
      MeasureTheory.norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall
        (fun y => by
          simp only [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul
            (mul_le_mul (K.norm_coe_le_norm (x, y)) (a.norm_coe_le_norm y)
              (abs_nonneg _) (norm_nonneg K))
            (h.norm_coe_le_norm y) (abs_nonneg _)
            (mul_nonneg (norm_nonneg K) (norm_nonneg a))))
    _ = ‖K‖ * ‖a‖ * ‖h‖ := by norm_num

noncomputable def apm_m98a03_weightedIntegralOperatorMap
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ) :
    apm_m98a03_C01 → (apm_m98a03_C01 →L[ℝ] apm_m98a03_C01) :=
  apm_m98a03_weightedIntegralOperator K

lemma apm_m98a03_weightedIntegralOperatorMap_apply
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (a : apm_m98a03_C01) :
    apm_m98a03_weightedIntegralOperatorMap K a =
      apm_m98a03_weightedIntegralOperator K a := rfl

lemma apm_m98a03_weightedIntegralOperator_sub
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (a b : apm_m98a03_C01) :
    apm_m98a03_weightedIntegralOperator K a -
        apm_m98a03_weightedIntegralOperator K b =
      apm_m98a03_weightedIntegralOperator K (a - b) := by
  ext h x
  simp only [ContinuousLinearMap.sub_apply,
    apm_m98a03_weightedIntegralOperator_apply, ContinuousMap.sub_apply]
  rw [← integral_sub]
  · congr 1
    funext y
    ring
  · exact (BoundedContinuousFunction.mkOfCompact
      (⟨fun y => K (x, y) * a y * h y, by fun_prop⟩ :
        C(Icc (0 : ℝ) 1, ℝ))).integrable volume
  · exact (BoundedContinuousFunction.mkOfCompact
      (⟨fun y => K (x, y) * b y * h y, by fun_prop⟩ :
        C(Icc (0 : ℝ) 1, ℝ))).integrable volume

lemma apm_m98a03_continuous_weightedIntegralOperatorMap
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ) :
    Continuous (apm_m98a03_weightedIntegralOperatorMap K) := by
  have hl : LipschitzWith ‖K‖₊
      (apm_m98a03_weightedIntegralOperatorMap K) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [dist_eq_norm, dist_eq_norm]
    change ‖apm_m98a03_weightedIntegralOperator K a -
      apm_m98a03_weightedIntegralOperator K b‖ ≤ ‖K‖ * ‖a - b‖
    rw [apm_m98a03_weightedIntegralOperator_sub]
    simpa using apm_m98a03_weightedIntegralOperator_norm_le K (a - b)
  exact hl.continuous

noncomputable def apm_m98a03_derivativeCoefficient (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (u : apm_m98a03_C01) : apm_m98a03_C01 :=
  (⟨deriv f, hf.continuous_deriv_one⟩ : C(ℝ, ℝ)).comp u

lemma apm_m98a03_continuous_derivativeCoefficient
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    Continuous (apm_m98a03_derivativeCoefficient f hf) := by
  exact ContinuousMap.continuous_postcomp
    (⟨deriv f, hf.continuous_deriv_one⟩ : C(ℝ, ℝ))

noncomputable def apm_m98a03_DF
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (u : apm_m98a03_C01) : apm_m98a03_C01 →L[ℝ] apm_m98a03_C01 :=
  apm_m98a03_weightedIntegralOperatorMap K
    (apm_m98a03_derivativeCoefficient f hf u)

lemma apm_m98a03_continuous_DF
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    Continuous (apm_m98a03_DF K f hf) := by
  exact (apm_m98a03_continuous_weightedIntegralOperatorMap K).comp
    (apm_m98a03_continuous_derivativeCoefficient f hf)

lemma apm_m98a03_DF_apply
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (u h : apm_m98a03_C01) (x : Icc (0 : ℝ) 1) :
    apm_m98a03_DF K f hf u h x =
      ∫ y : Icc (0 : ℝ) 1, K (x, y) * deriv f (u y) * h y := rfl

lemma apm_m98a03_uniform_scalar_remainder
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (u : apm_m98a03_C01)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ (y : Icc (0 : ℝ) 1) (v : ℝ), |v| < δ →
        |f (u y + v) - f (u y) - deriv f (u y) * v| ≤ ε * |v| := by
  let S : Set ℝ := Icc (-(‖u‖ + 1)) (‖u‖ + 1)
  have huc : UniformContinuousOn (deriv f) S :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      hf.continuous_deriv_one.continuousOn
  rcases (Metric.uniformContinuousOn_iff.mp huc) ε hε with
    ⟨δ₀, hδ₀, hmod⟩
  refine ⟨min 1 δ₀, lt_min (by norm_num) hδ₀, min_le_left _ _, ?_⟩
  intro y v hv
  have hv1 : |v| < 1 := lt_of_lt_of_le hv (min_le_left _ _)
  have hvδ : |v| < δ₀ := lt_of_lt_of_le hv (min_le_right _ _)
  have hua : |u y| ≤ ‖u‖ := by
    simpa [Real.norm_eq_abs] using u.norm_coe_le_norm y
  have haS : u y ∈ S := by
    change -(‖u‖ + 1) ≤ u y ∧ u y ≤ ‖u‖ + 1
    constructor <;> linarith [neg_abs_le (u y), le_abs_self (u y)]
  have hbS : u y + v ∈ S := by
    change -(‖u‖ + 1) ≤ u y + v ∧ u y + v ≤ ‖u‖ + 1
    have huv : |u y + v| < ‖u‖ + 1 := calc
      _ ≤ |u y| + |v| := abs_add_le _ _
      _ < ‖u‖ + 1 := by linarith
    constructor <;> linarith [neg_abs_le (u y + v), le_abs_self (u y + v)]
  let q : ℝ → ℝ := fun z => f z - deriv f (u y) * z
  have hqdiff : ∀ z ∈ segment ℝ (u y) (u y + v), DifferentiableAt ℝ q z := by
    intro z hz
    have hlin : DifferentiableAt ℝ (fun z : ℝ => deriv f (u y) * z) z :=
      (hasDerivAt_id z).const_mul (deriv f (u y)) |>.differentiableAt
    exact (hf.differentiable_one z).sub hlin
  have hqder : ∀ z ∈ segment ℝ (u y) (u y + v), ‖deriv q z‖ ≤ ε := by
    intro z hz
    have hzS : z ∈ S := (convex_Icc _ _).segment_subset haS hbS hz
    have hza : dist z (u y) < δ₀ := by
      rw [Real.dist_eq]
      exact lt_of_le_of_lt (norm_sub_le_of_mem_segment hz) (by
        simpa [Real.norm_eq_abs] using hvδ)
    have hm := (hmod z hzS (u y) haS hza).le
    have hderq : deriv q z = deriv f z - deriv f (u y) := by
      have hfz : HasDerivAt f (deriv f z) z :=
        (hf.differentiable_one z).hasDerivAt
      have hlin : HasDerivAt (fun w : ℝ => deriv f (u y) * w)
          (deriv f (u y)) z := by
        simpa using (hasDerivAt_id z).const_mul (deriv f (u y))
      exact (hfz.sub hlin).deriv
    rw [hderq, Real.norm_eq_abs]
    simpa [Real.dist_eq] using hm
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le hqdiff hqder
    (convex_segment (u y) (u y + v)) (left_mem_segment ℝ _ _)
    (right_mem_segment ℝ _ _)
  dsimp [q] at hmv
  convert hmv using 1 <;> ring

lemma apm_m98a03_hammerstein_remainder_norm_le
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (u h : apm_m98a03_C01)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hrem : ∀ y : Icc (0 : ℝ) 1,
      |f (u y + h y) - f (u y) - deriv f (u y) * h y| ≤ ε * |h y|) :
    ‖apm_m98a03_hammerstein K f hf.continuous (u + h) -
        apm_m98a03_hammerstein K f hf.continuous u -
        apm_m98a03_DF K f hf u h‖ ≤ ‖K‖ * ε * ‖h‖ := by
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro x
  change ‖apm_m98a03_hammerstein K f hf.continuous (u + h) x -
      apm_m98a03_hammerstein K f hf.continuous u x -
      apm_m98a03_DF K f hf u h x‖ ≤ ‖K‖ * ε * ‖h‖
  rw [apm_m98a03_hammerstein_apply, apm_m98a03_hammerstein_apply,
    apm_m98a03_DF_apply]
  simp only [ContinuousMap.add_apply]
  have hi₁ : Integrable (fun y : Icc (0 : ℝ) 1 =>
      K (x, y) * f (u y + h y)) := by
    exact (BoundedContinuousFunction.mkOfCompact
      (⟨fun y => K (x, y) * f (u y + h y), by fun_prop⟩ :
        C(Icc (0 : ℝ) 1, ℝ))).integrable volume
  have hi₂ : Integrable (fun y : Icc (0 : ℝ) 1 => K (x, y) * f (u y)) :=
    apm_m98a03_integrable_kernel_section K f hf.continuous u x
  rw [← integral_sub hi₁ hi₂]
  have hi₃ := apm_m98a03_integrable_derivative_kernel_section K f hf u h x
  change ‖(∫ y, ((fun z : Icc (0 : ℝ) 1 => K (x, z) * f (u z + h z)) -
      (fun z : Icc (0 : ℝ) 1 => K (x, z) * f (u z))) y) -
      ∫ y, K (x, y) * deriv f (u y) * h y‖ ≤ ‖K‖ * ε * ‖h‖
  rw [← integral_sub (hi₁.sub hi₂) hi₃]
  calc
      _ ≤ (‖K‖ * ε * ‖h‖) *
          (volume : Measure (Icc (0 : ℝ) 1)).real univ :=
        MeasureTheory.norm_integral_le_of_norm_le_const
          (Filter.Eventually.of_forall (fun y => by
            rw [Real.norm_eq_abs]
            have hk : |K (x, y)| ≤ ‖K‖ := by
              simpa [Real.norm_eq_abs] using K.norm_coe_le_norm (x, y)
            have hh : |h y| ≤ ‖h‖ := by
              simpa [Real.norm_eq_abs] using h.norm_coe_le_norm y
            simp only [Pi.sub_apply]
            rw [show K (x, y) * f (u y + h y) - K (x, y) * f (u y) -
                K (x, y) * deriv f (u y) * h y =
                K (x, y) * (f (u y + h y) - f (u y) -
                  deriv f (u y) * h y) by ring, abs_mul]
            calc
              _ ≤ ‖K‖ * (ε * |h y|) :=
                mul_le_mul hk (hrem y) (abs_nonneg _) (norm_nonneg K)
              _ ≤ ‖K‖ * (ε * ‖h‖) := mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hh hε) (norm_nonneg K)
              _ = ‖K‖ * ε * ‖h‖ := by ring))
      _ = ‖K‖ * ε * ‖h‖ := by norm_num

lemma apm_m98a03_hasFDerivAt_hammerstein
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (u : apm_m98a03_C01) :
    HasFDerivAt (apm_m98a03_hammerstein K f hf.continuous)
      (apm_m98a03_DF K f hf u) u := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have heps : 0 < c / (‖K‖ + 1) := div_pos hc (by positivity)
  rcases apm_m98a03_uniform_scalar_remainder f hf u heps with
    ⟨δ, hδ, hδ1, hscalar⟩
  filter_upwards [Metric.ball_mem_nhds u hδ] with v hv
  have hvnorm : ‖v - u‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hv
  have hp (y : Icc (0 : ℝ) 1) : |(v - u) y| < δ :=
    lt_of_le_of_lt (by simpa [Real.norm_eq_abs] using
      (v - u).norm_coe_le_norm y) hvnorm
  have hrem := apm_m98a03_hammerstein_remainder_norm_le K f hf u (v - u)
    (c / (‖K‖ + 1)) heps.le (fun y => by
      simpa [ContinuousMap.sub_apply] using hscalar y ((v - u) y) (hp y))
  have huv : u + (v - u) = v := by abel
  rw [huv] at hrem
  refine hrem.trans ?_
  have hk : ‖K‖ / (‖K‖ + 1) ≤ 1 := by
    exact (div_le_one (by positivity)).2 (by linarith [norm_nonneg K])
  calc
    ‖K‖ * (c / (‖K‖ + 1)) * ‖v - u‖ =
        c * (‖K‖ / (‖K‖ + 1)) * ‖v - u‖ := by field_simp
    _ ≤ c * 1 * ‖v - u‖ := by
      gcongr
    _ = c * ‖v - u‖ := by ring

theorem apm_m98a03
    (K : ContinuousMap ((Icc (0 : ℝ) 1) × (Icc (0 : ℝ) 1)) ℝ)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    ∃ (F : apm_m98a03_C01 → apm_m98a03_C01)
      (DF : apm_m98a03_C01 → (apm_m98a03_C01 →L[ℝ] apm_m98a03_C01)),
      apm_m98a03_IsHammersteinOperator K f F ∧
      (∀ u : apm_m98a03_C01,
        HasFDerivAt F (DF u) u ∧
        ∀ (h : apm_m98a03_C01) (x : Icc (0 : ℝ) 1),
          DF u h x = ∫ y : Icc (0 : ℝ) 1,
            K (x, y) * deriv f (u y) * h y) ∧
      Continuous DF := by
  /-
  PARTIAL boundary (codex). The scalar integral in the frozen Hammerstein
  formula is now certified as integrable by
  `apm_m98a03_integrable_kernel_section` (using `hf.continuous`). Mathlib's
  `ContinuousMap.integral_apply` gives the correct evaluation theorem if the
  operator is built as a `ContinuousMap`-valued Bochner integral.

  The remaining construction is substantial: package
  `u ↦ (x ↦ ∫ y, K (x,y) * f (u y))` as a continuous-map-valued operator,
  build its derivative as a bounded integral operator, prove the uniform
  Fréchet remainder estimate for the Nemytskii map from only `ContDiff ℝ 1 f`,
  and prove continuity in operator norm of `u ↦ DF u`. Searches for
  Hammerstein/Nemytskii APIs in Mathlib, all closed artifacts (including the
  partial mixed-exponent sibling `m94A04`), `ConstructionTargets`, and
  `YoungL2.lean` found no compiled theorem packaging this compact-domain
  differentiability argument.

  A further search found Mathlib's general Banach-valued theorem
  `hasFDerivAt_integral_of_dominated_of_fderiv_le` in
  `Mathlib.Analysis.Calculus.ParametricIntegral`.  This gives a viable route
  after rewriting the integrand as a `ContinuousMap` in `x`, and
  `ContinuousMap.integral_apply` then recovers the frozen pointwise formula.
  I also checked `contDiff_one_iff_hasFDerivAt`, which can supply the scalar
  derivative and its continuity.  Applying the parametric theorem still
  requires proving, uniformly for `u` in a sup-norm ball, an integrable bound
  on the `ContinuousMap`-valued derivative, its strong measurability as a map
  into continuous linear operators, and finally continuity of the resulting
  integral in operator norm.  Neither the closed corpus nor the construction
  libraries contain those missing compact-domain Nemytskii packaging lemmas.

  Closer hop 1 proves the corresponding integrability prerequisite for the
  derivative formula as
  `apm_m98a03_integrable_derivative_kernel_section`.  The proof uses
  `ContDiff.continuous_deriv_one` to make
  `y ↦ K(x,y) * deriv f (u y) * h y` a continuous map on the compact interval,
  then applies `BoundedContinuousFunction.mkOfCompact.integrable`.  Further
  searches of `ParametricIntegral`, continuous-map Bochner integration,
  operator-valued measurability, the closed corpus, and construction libraries
  found no theorem discharging the required uniform sup-ball domination or
  continuity of the resulting operator-valued integral.  Thus both frozen
  pointwise integrands are now certified integrable; uniform Fréchet control
  and operator-norm continuity remain open.

  Closer hop 2 compiles the domination arithmetic itself.  The lemma
  `apm_m98a03_derivative_kernel_norm_le` bounds the derivative integrand by
  `‖K‖ * M * ‖h‖` whenever `M` bounds `|deriv f|`; it uses the compact-domain
  sup-norm lemmas `ContinuousMap.norm_coe_le_norm`.  The companion
  `apm_m98a03_integrable_derivative_majorant` proves that the resulting
  constant majorant is integrable on the interval.  Searches of the
  parametric-integral source, closed artifacts, construction libraries, and
  git history found no packaged way to choose `M` uniformly on a sup-norm
  neighborhood and bundle the pointwise derivative as an operator-valued
  measurable map.  That localization/bundling step, followed by continuity in
  operator norm, is the remaining boundary.

  Closer hop 3 closes the previously open localization step.  The lemma
  `apm_m98a03_exists_deriv_bound_on_Icc` obtains a finite bound for
  `|deriv f|` on any compact interval from
  `ContDiff.continuous_deriv_one` and `IsCompact.bddAbove_image`.
  `apm_m98a03_exists_local_deriv_bound` then proves that, for every `u`, one
  such bound works simultaneously for every `v` in the open unit sup-norm
  ball around `u` and every parameter point.  Its proof uses
  `ContinuousMap.norm_coe_le_norm` to place all values of `v` in the fixed
  compact interval `[-(‖u‖+1), ‖u‖+1]`.

  A renewed inspection of `hasFDerivAt_integral_of_dominated_of_fderiv_le`,
  continuous-linear-map integration, the closed corpus, `LEMMA-INDEX.md`, the
  construction libraries, and git history found no wrapper turning the
  scalar kernel derivative into the required
  `C([0,1]) →L[ℝ] C([0,1])`-valued measurable integrand or proving continuity
  of its integral in operator norm.  Thus neighborhood-uniform domination is
  now complete; operator-valued bundling and operator-norm continuity remain
  the exact boundary.
  -/
  refine ⟨apm_m98a03_hammerstein K f hf.continuous,
    apm_m98a03_DF K f hf, apm_m98a03_hammerstein_spec K f hf.continuous, ?_,
    apm_m98a03_continuous_DF K f hf⟩
  intro u
  refine ⟨apm_m98a03_hasFDerivAt_hammerstein K f hf u, ?_⟩
  intro h x
  exact apm_m98a03_DF_apply K f hf u h x
