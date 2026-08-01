import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Normed.Lp.SmoothApprox

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

/-! # APM a02J03: Vanishing of ∫ φ(kx) f(x) dx as k → ∞

  φ measurable with |∫_Q φ| ≤ M·m(Q)/(1+m(Q)) for all rectangles Q.
  f ∈ L¹(ℝⁿ). Show: ∫ φ(kx)f(x)dx → 0 as k → ∞.

  Proof: density argument.
  Step 1: For f = χ_Q, change of variables gives
    |∫ φ(kx)χ_Q(x)dx| = k⁻ⁿ|∫_{kQ} φ| ≤ Mm(Q)/(1+kⁿm(Q)) → 0.
  Step 2: Uniform bound |T_k(f)| ≤ M‖f‖₁ from Step 1.
  Step 3: Approximate f by step functions, use Steps 1+2.
-/

-- For simplicity, state for ℝ (n=1). The proof generalizes.

-- CLOSED: The core limit computation
-- M * c / (1 + k * c) → 0 as k → ∞ (for c > 0)
lemma tendsto_bound_zero (M c : ℝ) (hc : 0 < c) :
    Tendsto (fun k : ℝ => M * c / (1 + k * c)) atTop (nhds 0) := by
  have hg : Tendsto (fun k : ℝ => 1 + k * c) atTop atTop := by
    apply tendsto_atTop_add_const_left
    exact Tendsto.atTop_mul_const hc tendsto_id
  exact hg.const_div_atTop (M * c)

-- The scaled integral operator
def scaledIntOp (φ : ℝ → ℝ) (f : ℝ → ℝ) (k : ℝ) : ℝ :=
  ∫ x, φ (k * x) * f x

-- Step 1: Indicator case
-- |∫ φ(kx) χ_Q(x) dx| ≤ Mm(Q)/(1 + k·m(Q)) → 0
-- After change of variables u = kx:
-- ∫ φ(kx) χ_Q(x) dx = (1/k) ∫_{kQ} φ(u) du
-- |...| ≤ (1/k) · M·m(kQ)/(1+m(kQ)) = (1/k) · M·k·m(Q)/(1+k·m(Q))
--       = M·m(Q)/(1+k·m(Q))
-- The change-of-variables bound (the content of Step 1)
-- |T_k(χ_{[a,b]})| ≤ M(b-a)/(1+k(b-a))
-- Proof: substitution u=kx gives T_k(χ_Q) = (1/k)∫_{kQ} φ,
-- then the hypothesis bounds |(1/k)∫_{kQ} φ| ≤ Mm(Q)/(1+km(Q)).
lemma indicator_bound (φ : ℝ → ℝ) (M : ℝ)
    (hφ : ∀ (a b : ℝ), a < b →
      |∫ x in Set.Icc a b, φ x| ≤ M * (b - a) / (1 + (b - a)))
    (a b : ℝ) (hab : a < b) (k : ℝ) (hk : 0 < k) :
    |scaledIntOp φ (Set.indicator (Set.Icc a b) (fun _ => 1)) k| ≤
      M * (b - a) / (1 + k * (b - a)) := by
  have hk0 : k ≠ 0 := ne_of_gt hk
  have hkab : k * a < k * b := mul_lt_mul_of_pos_left hab hk
  have hmem (x : ℝ) :
      k * x ∈ Set.Icc (k * a) (k * b) ↔ x ∈ Set.Icc a b := by
    constructor
    · intro hx
      constructor <;> nlinarith [hx.1, hx.2]
    · intro hx
      constructor <;> nlinarith [hx.1, hx.2]
  have hintegrand :
      (fun x => φ (k * x) * Set.indicator (Set.Icc a b) (fun _ => 1) x) =
        (fun x => Set.indicator (Set.Icc (k * a) (k * b)) φ (k * x)) := by
    funext x
    by_cases hx : x ∈ Set.Icc a b
    · simp [Set.indicator_of_mem hx, Set.indicator_of_mem ((hmem x).2 hx)]
    · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (hmem x).1 hx)]
  have hscale :
      scaledIntOp φ (Set.indicator (Set.Icc a b) (fun _ => 1)) k =
        k⁻¹ * ∫ y in Set.Icc (k * a) (k * b), φ y := by
    rw [scaledIntOp, hintegrand]
    have h := Measure.integral_comp_mul_left
      (g := Set.indicator (Set.Icc (k * a) (k * b)) φ) k
    rw [abs_of_pos (inv_pos.mpr hk), smul_eq_mul,
      integral_indicator measurableSet_Icc] at h
    exact h
  rw [hscale, abs_mul, abs_of_pos (inv_pos.mpr hk)]
  have hbound := hφ (k * a) (k * b) hkab
  calc
    k⁻¹ * |∫ y in Set.Icc (k * a) (k * b), φ y|
        ≤ k⁻¹ * (M * (k * b - k * a) / (1 + (k * b - k * a))) :=
      mul_le_mul_of_nonneg_left hbound (le_of_lt (inv_pos.mpr hk))
    _ = M * (b - a) / (1 + k * (b - a)) := by
      field_simp

/-- The indicator estimate rewritten as a bound on the scaled interval
integral.  This is the quantitative primitive estimate used by the
integration-by-parts proof for smooth compactly supported test functions. -/
lemma scaled_setIntegral_bound (φ : ℝ → ℝ) (M : ℝ)
    (hφ : ∀ (a b : ℝ), a < b →
      |∫ x in Set.Icc a b, φ x| ≤ M * (b - a) / (1 + (b - a)))
    (a b : ℝ) (hab : a < b) (k : ℝ) (hk : 0 < k) :
    |∫ x in Set.Icc a b, φ (k * x)| ≤
      M * (b - a) / (1 + k * (b - a)) := by
  simpa only [scaledIntOp, Set.indicator_apply, Pi.one_apply, mul_ite,
    mul_one, mul_zero, ← MeasureTheory.integral_indicator measurableSet_Icc]
    using indicator_bound φ M hφ a b hab k hk

/-- Oriented-interval form of `scaled_setIntegral_bound`. -/
lemma scaled_intervalIntegral_bound (φ : ℝ → ℝ) (M : ℝ)
    (hφ : ∀ (a b : ℝ), a < b →
      |∫ x in Set.Icc a b, φ x| ≤ M * (b - a) / (1 + (b - a)))
    (a b : ℝ) (k : ℝ) (hk : 0 < k) :
    |∫ x in a..b, φ (k * x)| ≤
      M * |b - a| / (1 + k * |b - a|) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · rw [intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc,
      abs_of_pos (sub_pos.mpr hab)]
    exact scaled_setIntegral_bound φ M hφ a b hab k hk
  · simp
  · rw [intervalIntegral.integral_symm, abs_neg,
      abs_of_neg (sub_neg.mpr hba), neg_sub,
      intervalIntegral.integral_of_le hba.le, ← integral_Icc_eq_integral_Ioc]
    exact scaled_setIntegral_bound φ M hφ b a hba k hk

/-- The primitive of `x ↦ φ (k * x)` has a damping-independent `M / k`
bound.  This is the small factor in the eventual integration-by-parts
estimate. -/
lemma scaled_intervalIntegral_bound_div (φ : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hφ : ∀ (a b : ℝ), a < b →
      |∫ x in Set.Icc a b, φ x| ≤ M * (b - a) / (1 + (b - a)))
    (a b : ℝ) (k : ℝ) (hk : 0 < k) :
    |∫ x in a..b, φ (k * x)| ≤ M / k := by
  refine (scaled_intervalIntegral_bound φ M hφ a b k hk).trans ?_
  have hd : 0 ≤ |b - a| := abs_nonneg _
  have hden : 0 < 1 + k * |b - a| := by positivity
  rw [div_le_div_iff₀ hden hk]
  nlinarith

lemma tendsto_scaled_primitive_bound_zero (M : ℝ) :
    Tendsto (fun k : ℝ => M / k) atTop (nhds 0) :=
  tendsto_id.const_div_atTop M

-- CLOSED: convergence from the bound via squeeze
lemma indicator_case (φ : ℝ → ℝ) (M : ℝ) (hM : 0 < M)
    (hφ : ∀ (a b : ℝ), a < b →
      |∫ x in Set.Icc a b, φ x| ≤ M * (b - a) / (1 + (b - a)))
    (a b : ℝ) (hab : a < b) :
    Tendsto (fun k : ℝ => scaledIntOp φ (Set.indicator (Set.Icc a b) (fun _ => 1)) k)
      atTop (nhds 0) := by
  have hba : 0 < b - a := by linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall (fun k => norm_nonneg _))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk
    simp only [Real.norm_eq_abs]
    exact indicator_bound φ M hφ a b hab k hk
  · exact tendsto_bound_zero M (b - a) hba

/-- The interval-average hypothesis makes `φ` essentially bounded by `M`.

The primitive of `φ` is `M`-Lipschitz by the interval bound, while the
Lebesgue differentiation theorem identifies its derivative with `φ` almost
everywhere. -/
lemma ae_abs_le_of_interval_integral_bound (φ : ℝ → ℝ) (M : ℝ)
    (hφloc : LocallyIntegrable φ volume)
    (hφ : ∀ (a b : ℝ), a < b →
      |∫ x in Set.Icc a b, φ x| ≤ M * (b - a) / (1 + (b - a))) :
    ∀ᵐ x ∂volume, |φ x| ≤ M := by
  have hM : 0 ≤ M := by
    have h := hφ 0 1 zero_lt_one
    norm_num at h
    linarith [abs_nonneg (∫ x in Set.Icc (0 : ℝ) 1, φ x)]
  let F : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, φ t
  have hint (a b : ℝ) : IntervalIntegrable φ volume a b :=
    intervalIntegrable_iff.mpr <|
      (hφloc.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  have hF_sub (x y : ℝ) (hxy : x ≤ y) :
      F y - F x = ∫ t in Set.Icc x y, φ t := by
    rw [show F y - F x = ∫ t in x..y, φ t from
      intervalIntegral.integral_interval_sub_left (hint 0 y) (hint 0 x)]
    rw [intervalIntegral.integral_of_le hxy, ← integral_Icc_eq_integral_Ioc]
  have hF : LipschitzWith (Real.toNNReal M) F := by
    apply LipschitzWith.of_dist_le'
    intro x y
    wlog hxy : x ≤ y generalizing x y
    · simpa [dist_comm] using this y x (le_of_not_ge hxy)
    by_cases hEq : x = y
    · subst y
      simp
    have hlt : x < y := lt_of_le_of_ne hxy hEq
    rw [Real.dist_eq, abs_sub_comm, hF_sub x y hxy, Real.dist_eq]
    calc
      |∫ t in Set.Icc x y, φ t|
          ≤ M * (y - x) / (1 + (y - x)) := hφ x y hlt
      _ ≤ M * (y - x) :=
        div_le_self (mul_nonneg hM (sub_nonneg.mpr hxy)) (by linarith)
      _ = M * |x - y| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
        ring
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hφloc] with x hx
  have hx' : HasDerivAt F (φ x) x := by simpa [F] using hx 0
  simpa [Real.norm_eq_abs, Real.coe_toNNReal _ hM] using hx'.le_of_lipschitz hF

-- Step 2: Uniform bound |T_k(f)| ≤ M ‖f‖₁
-- For step functions on disjoint intervals: each piece bounded by M·m(Qᵢ),
-- sum ≤ M · Σ|cᵢ|m(Qᵢ) = M · ‖f‖₁.
-- This extends to L¹ by density.
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): require local integrability
-- of `φ`, so the rectangle integrals cannot all be junk values from
-- `integral_undef`.
lemma uniform_bound (φ : ℝ → ℝ) (M : ℝ)
    (hφloc : LocallyIntegrable φ volume)
    (hφ : ∀ (a b : ℝ), a < b →
      |∫ x in Set.Icc a b, φ x| ≤ M * (b - a) / (1 + (b - a)))
    (f : ℝ → ℝ) (hf : Integrable f volume) (k : ℝ) (hk : 0 < k) :
    |scaledIntOp φ f k| ≤ M * ∫ x, ‖f x‖ := by
  have hM : 0 ≤ M := by
    have h := hφ 0 1 zero_lt_one
    norm_num at h
    linarith [abs_nonneg (∫ x in Set.Icc (0 : ℝ) 1, φ x)]
  have hφae := ae_abs_le_of_interval_integral_bound φ M hφloc hφ
  have hfcomp : Integrable (fun y => f (k⁻¹ * y)) volume :=
    hf.comp_mul_left' (inv_ne_zero hk.ne')
  have hdom :
      ∀ᵐ y ∂volume, ‖φ y * f (k⁻¹ * y)‖ ≤ M * ‖f (k⁻¹ * y)‖ := by
    filter_upwards [hφae] with y hy
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)
  have hprod : Integrable (fun y => φ y * f (k⁻¹ * y)) volume :=
    Integrable.mono' (hfcomp.norm.const_mul M)
      (hφloc.aestronglyMeasurable.mul hfcomp.aestronglyMeasurable) hdom
  have hscale :
      scaledIntOp φ f k =
        k⁻¹ * ∫ y, φ y * f (k⁻¹ * y) := by
    rw [scaledIntOp]
    have h := Measure.integral_comp_mul_left
      (fun y => φ y * f (k⁻¹ * y)) k
    rw [abs_of_pos (inv_pos.mpr hk), smul_eq_mul] at h
    calc
      ∫ x, φ (k * x) * f x =
          ∫ x, φ (k * x) * f (k⁻¹ * (k * x)) := by
        apply integral_congr_ae
        filter_upwards [] with x
        congr 2
        field_simp
      _ = k⁻¹ * ∫ y, φ y * f (k⁻¹ * y) := h
  rw [hscale, abs_mul, abs_of_pos (inv_pos.mpr hk)]
  calc
    k⁻¹ * |∫ y, φ y * f (k⁻¹ * y)|
        ≤ k⁻¹ * ∫ y, M * ‖f (k⁻¹ * y)‖ :=
      mul_le_mul_of_nonneg_left
        (norm_integral_le_of_norm_le (hfcomp.norm.const_mul M) hdom)
        (le_of_lt (inv_pos.mpr hk))
    _ = M * ∫ x, ‖f x‖ := by
      rw [integral_const_mul]
      have h := Measure.integral_comp_mul_left (fun x => ‖f x‖) k⁻¹
      rw [inv_inv, abs_of_pos hk, smul_eq_mul] at h
      rw [h]
      field_simp

/-- Once convergence is known for compactly supported continuous functions,
the uniform `L¹` estimate extends it to every integrable function. -/
lemma scaled_integral_vanishes_of_compact_continuous
    (φ : ℝ → ℝ) (M : ℝ) (hM : 0 < M)
    (hφloc : LocallyIntegrable φ volume)
    (hφ : ∀ (a b : ℝ), a < b →
      |∫ x in Set.Icc a b, φ x| ≤ M * (b - a) / (1 + (b - a)))
    (hcore : ∀ (g : ℝ → ℝ), HasCompactSupport g → Continuous g → Integrable g volume →
      Tendsto (fun k : ℝ => scaledIntOp φ g k) atTop (nhds 0))
    (f : ℝ → ℝ) (hf : Integrable f volume) :
    Tendsto (fun k : ℝ => scaledIntOp φ f k) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / (2 * M) := div_pos hε (mul_pos two_pos hM)
  obtain ⟨g, hg_support, hfg, hg_cont, hg_int⟩ :=
    hf.exists_hasCompactSupport_integral_sub_le hδ
  have hdiff : Integrable (f - g) volume := hf.sub hg_int
  have hφae := ae_abs_le_of_interval_integral_bound φ M hφloc hφ
  have hprod (u : ℝ → ℝ) (hu : Integrable u volume) (k : ℝ) (hk : 0 < k) :
      Integrable (fun x => φ (k * x) * u x) volume := by
    have hucomp : Integrable (fun y => u (k⁻¹ * y)) volume :=
      hu.comp_mul_left' (inv_ne_zero hk.ne')
    have hdom : ∀ᵐ y ∂volume,
        ‖φ y * u (k⁻¹ * y)‖ ≤ M * ‖u (k⁻¹ * y)‖ := by
      filter_upwards [hφae] with y hy
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)
    have hp : Integrable (fun y => φ y * u (k⁻¹ * y)) volume :=
      Integrable.mono' (hucomp.norm.const_mul M)
        (hφloc.aestronglyMeasurable.mul hucomp.aestronglyMeasurable) hdom
    have hp' := hp.comp_mul_left' hk.ne'
    convert hp' using 1
    funext x
    congr 2
    field_simp
  have hg_lim := hcore g hg_support hg_cont hg_int
  rw [Metric.tendsto_atTop] at hg_lim
  obtain ⟨K, hK⟩ := hg_lim (ε / 2) (half_pos hε)
  refine ⟨max K 1, fun k hk => ?_⟩
  have hkK : K ≤ k := le_trans (le_max_left _ _) hk
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hk)
  have hgsmall := hK k hkK
  rw [Real.dist_eq, sub_zero] at hgsmall ⊢
  have hadd : scaledIntOp φ f k =
      scaledIntOp φ g k + scaledIntOp φ (f - g) k := by
    rw [scaledIntOp, scaledIntOp, scaledIntOp, ← integral_add
      (hprod g hg_int k hkpos) (hprod (f - g) hdiff k hkpos)]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [Pi.sub_apply]
    ring
  rw [hadd]
  calc
    |scaledIntOp φ g k + scaledIntOp φ (f - g) k|
        ≤ |scaledIntOp φ g k| + |scaledIntOp φ (f - g) k| := abs_add_le _ _
    _ < ε / 2 + M * ∫ x, ‖f x - g x‖ :=
      add_lt_add_of_lt_of_le hgsmall (by
        simpa only [Pi.sub_apply] using
          uniform_bound φ M hφloc hφ (f - g) hdiff k hkpos)
    _ ≤ ε / 2 + M * (ε / (2 * M)) := by gcongr
    _ = ε := by
      field_simp
      norm_num

lemma scaled_integral_vanishes_of_compact_smooth
    (φ : ℝ → ℝ) (M : ℝ) (hM : 0 < M)
    (hφloc : LocallyIntegrable φ volume)
    (hφ : ∀ (a b : ℝ), a < b →
      |∫ x in Set.Icc a b, φ x| ≤ M * (b - a) / (1 + (b - a)))
    (g : ℝ → ℝ) (hg_support : HasCompactSupport g) (hg_smooth : ContDiff ℝ ∞ g) :
    Tendsto (fun k : ℝ => scaledIntOp φ g k) atTop (nhds 0) := by
  obtain ⟨R, hRpos, hR⟩ := hg_support.isBounded.subset_closedBall_lt 0 0
  let a : ℝ := -R - 1
  let b : ℝ := R + 1
  have hab : a < b := by dsimp [a, b]; linarith
  have hg_support_Ioo : Function.support g ⊆ Set.Ioo a b := by
    intro x hx
    have hxt : x ∈ tsupport g := subset_tsupport g hx
    have hxR := hR hxt
    have hxabs : |x| ≤ R := by simpa [Real.dist_eq] using hxR
    dsimp [a, b]
    constructor <;> linarith [le_abs_self x, neg_le_of_abs_le hxabs]
  have hg_ac : AbsolutelyContinuousOnInterval g a b := by
    obtain ⟨C, hC⟩ := hg_smooth.lipschitzWith_of_hasCompactSupport hg_support (by simp)
    exact hC.lipschitzOnWith.absolutelyContinuousOnInterval
  have hg_deriv_int : IntervalIntegrable (deriv g) volume a b :=
    (hg_smooth.continuous_deriv (by simp)).intervalIntegrable a b
  let C : ℝ := ∫ x in a..b, |deriv g x|
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    exact intervalIntegral.integral_nonneg hab.le (fun _ _ => abs_nonneg _)
  have hbound (k : ℝ) (hk : 0 < k) :
      |scaledIntOp φ g k| ≤ (M / k) * C := by
    have hφ_int : IntervalIntegrable φ volume (k * a) (k * b) :=
      intervalIntegrable_iff.mpr <|
        (hφloc.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
    have hφk_int : IntervalIntegrable (fun x => φ (k * x)) volume a b := by
      simpa [hk.ne'] using hφ_int.comp_mul_left (c := k)
    let P : ℝ → ℝ := fun x => ∫ t in a..x, φ (k * t)
    have hP_ac : AbsolutelyContinuousOnInterval P a b :=
      hφk_int.absolutelyContinuousOnInterval_intervalIntegral (by simp)
    have hP_deriv : ∀ᵐ x ∂volume, x ∈ uIoc a b → deriv P x = φ (k * x) := by
      filter_upwards [hφk_int.ae_hasDerivAt_integral] with x hx hxI
      exact (hx (uIoc_subset_uIcc hxI) a (by simp)).deriv
    have hglobal : scaledIntOp φ g k = ∫ x in a..b, φ (k * x) * g x := by
      rw [scaledIntOp, intervalIntegral.integral_eq_integral_of_support_subset]
      exact (Function.support_mul_subset_right _ _).trans
        (hg_support_Ioo.trans Set.Ioo_subset_Ioc_self)
    have hreplace : (∫ x in a..b, φ (k * x) * g x) =
        ∫ x in a..b, deriv P x * g x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hP_deriv] with x hx hxI
      rw [hx hxI]
    have hga : g a = 0 := by
      by_contra hga
      exact (lt_irrefl a) (hg_support_Ioo hga).1
    have hgb : g b = 0 := by
      by_contra hgb
      exact (lt_irrefl b) (hg_support_Ioo hgb).2
    have hparts := hP_ac.integral_mul_deriv_eq_deriv_mul hg_ac
    have hidentity : (∫ x in a..b, deriv P x * g x) =
        -(∫ x in a..b, P x * deriv g x) := by
      simp only [hga, hgb, mul_zero, sub_zero, zero_sub] at hparts
      linarith [hparts]
    rw [hglobal, hreplace, hidentity, abs_neg]
    have hdom (x : ℝ) :
        ‖P x * deriv g x‖ ≤ (M / k) * |deriv g x| := by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (scaled_intervalIntegral_bound_div φ M hM.le hφ a x k hk) (abs_nonneg _)
    calc
      |∫ x in a..b, P x * deriv g x|
          ≤ ∫ x in a..b, (M / k) * |deriv g x| := by
            simpa [Real.norm_eq_abs] using
              intervalIntegral.norm_integral_le_of_norm_le hab.le
                (Filter.Eventually.of_forall (fun x _ => hdom x))
                (hg_deriv_int.abs.const_mul (M / k))
      _ = (M / k) * C := by simp [C, intervalIntegral.integral_const_mul]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk
    simpa [Real.norm_eq_abs] using hbound k hk
  · simpa only [zero_mul] using (tendsto_scaled_primitive_bound_zero M).mul_const C

-- Main theorem: ∫ φ(kx) f(x) dx → 0
-- Density: approximate f by step functions, use indicator_case + uniform_bound
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): require local integrability
-- of `φ`, matching the semantic domain assumed by its interval integrals.
theorem scaled_integral_vanishes (φ : ℝ → ℝ) (M : ℝ) (hM : 0 < M)
    (hφloc : LocallyIntegrable φ volume)
    (hφ : ∀ (a b : ℝ), a < b →
      |∫ x in Set.Icc a b, φ x| ≤ M * (b - a) / (1 + (b - a)))
    (f : ℝ → ℝ) (hf : Integrable f volume) :
    Tendsto (fun k : ℝ => scaledIntOp φ f k) atTop (nhds 0) := by
  apply scaled_integral_vanishes_of_compact_continuous φ M hM hφloc hφ _ f hf
  intro g hg_support hg_cont hg_int
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / (2 * M) := div_pos hε (mul_pos two_pos hM)
  have hgLp : MemLp g 1 volume := memLp_one_iff_integrable.mpr hg_int
  obtain ⟨s, hs_support, hs_smooth, hgs⟩ :=
    hgLp.exist_eLpNorm_sub_le ENNReal.one_ne_top le_rfl hδ
  have hs_int : Integrable s volume :=
    hs_smooth.continuous.integrable_of_hasCompactSupport hs_support
  have hdiff : Integrable (g - s) volume := hg_int.sub hs_int
  have hgs_real : (∫ x, ‖g x - s x‖) ≤ ε / (2 * M) := by
    simp only [← Pi.sub_apply]
    rw [integral_norm_eq_lintegral_enorm hdiff.aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_enorm]
    exact (ENNReal.toReal_mono (by simp) hgs).trans_eq (ENNReal.toReal_ofReal hδ.le)
  have hφae := ae_abs_le_of_interval_integral_bound φ M hφloc hφ
  have hprod (u : ℝ → ℝ) (hu : Integrable u volume) (k : ℝ) (hk : 0 < k) :
      Integrable (fun x => φ (k * x) * u x) volume := by
    have hucomp : Integrable (fun y => u (k⁻¹ * y)) volume :=
      hu.comp_mul_left' (inv_ne_zero hk.ne')
    have hdom : ∀ᵐ y ∂volume,
        ‖φ y * u (k⁻¹ * y)‖ ≤ M * ‖u (k⁻¹ * y)‖ := by
      filter_upwards [hφae] with y hy
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)
    have hp : Integrable (fun y => φ y * u (k⁻¹ * y)) volume :=
      Integrable.mono' (hucomp.norm.const_mul M)
        (hφloc.aestronglyMeasurable.mul hucomp.aestronglyMeasurable) hdom
    have hp' := hp.comp_mul_left' hk.ne'
    convert hp' using 1
    funext x
    congr 2
    field_simp
  have hs_lim :=
    scaled_integral_vanishes_of_compact_smooth φ M hM hφloc hφ s hs_support hs_smooth
  rw [Metric.tendsto_atTop] at hs_lim
  obtain ⟨K, hK⟩ := hs_lim (ε / 2) (half_pos hε)
  refine ⟨max K 1, fun k hk => ?_⟩
  have hkK : K ≤ k := le_trans (le_max_left _ _) hk
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hk)
  have hssmall := hK k hkK
  rw [Real.dist_eq, sub_zero] at hssmall ⊢
  have hadd : scaledIntOp φ g k =
      scaledIntOp φ s k + scaledIntOp φ (g - s) k := by
    rw [scaledIntOp, scaledIntOp, scaledIntOp, ← integral_add
      (hprod s hs_int k hkpos) (hprod (g - s) hdiff k hkpos)]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [Pi.sub_apply]
    ring
  rw [hadd]
  calc
    |scaledIntOp φ s k + scaledIntOp φ (g - s) k|
        ≤ |scaledIntOp φ s k| + |scaledIntOp φ (g - s) k| := abs_add_le _ _
    _ < ε / 2 + M * ∫ x, ‖g x - s x‖ :=
      add_lt_add_of_lt_of_le hssmall (by
        simpa only [Pi.sub_apply] using
          uniform_bound φ M hφloc hφ (g - s) hdiff k hkpos)
    _ ≤ ε / 2 + M * (ε / (2 * M)) := by gcongr
    _ = ε := by
      field_simp
      norm_num
