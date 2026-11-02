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

/-! ## The repaired `ℝⁿ` statement -/

open scoped Pointwise

lemma locallyIntegrable_of_integrableOn_rectangles {n : ℕ}
    {φ : (Fin n → ℝ) → ℂ}
    (hrect : ∀ a b : Fin n → ℝ, a ≤ b → IntegrableOn φ (Set.Icc a b)) :
    LocallyIntegrable φ volume := by
  intro x
  let a : Fin n → ℝ := fun i => x i - 1
  let b : Fin n → ℝ := fun i => x i + 1
  refine ⟨Set.Icc a b, pi_Icc_mem_nhds (fun i => ?_) (fun i => ?_), hrect a b ?_⟩
  · dsimp [a]
    linarith
  · dsimp [b]
    linarith
  · intro i
    dsimp [a, b]
    linarith

lemma nonneg_of_rectangle_integral_bound {n : ℕ} (hn : 0 < n)
    {φ : (Fin n → ℝ) → ℂ} {M : ℝ}
    (hQ : ∀ a b : Fin n → ℝ, a ≤ b →
      ‖∫ x in Set.Icc a b, φ x‖ ≤
        M * (volume (Set.Icc a b)).toReal / (1 + (volume (Set.Icc a b)).toReal)) :
    0 ≤ M := by
  let a : Fin n → ℝ := fun _ => 0
  let b : Fin n → ℝ := fun _ => 1
  have h := hQ a b (by intro i; simp [a, b])
  have hvol : (volume (Set.Icc a b)).toReal = 1 := by
    rw [Real.volume_Icc_pi_toReal (by intro i; simp [a, b])]
    simp [a, b]
  rw [hvol] at h
  nlinarith [norm_nonneg (∫ x in Set.Icc a b, φ x)]

lemma pi_closedBall_eq_Icc {n : ℕ} (x : Fin n → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    Metric.closedBall x r = Set.Icc (fun i => x i - r) (fun i => x i + r) := by
  rw [closedBall_pi x hr]
  ext y
  simp [Real.closedBall_eq_Icc]

lemma norm_setAverage_closedBall_le {n : ℕ}
    {φ : (Fin n → ℝ) → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hQ : ∀ a b : Fin n → ℝ, a ≤ b →
      ‖∫ x in Set.Icc a b, φ x‖ ≤
        M * (volume (Set.Icc a b)).toReal / (1 + (volume (Set.Icc a b)).toReal))
    (x : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    ‖⨍ y in Metric.closedBall x r, φ y ∂volume‖ ≤ M := by
  let m : ℝ := (volume (Metric.closedBall x r)).toReal
  have hm : 0 < m := by
    dsimp [m]
    rw [Real.volume_pi_closedBall x hr.le, ENNReal.toReal_ofReal (by positivity)]
    positivity
  have hrect := hQ (fun i => x i - r) (fun i => x i + r) (by
    intro i
    linarith)
  rw [← pi_closedBall_eq_Icc x hr.le] at hrect
  rw [setAverage_eq, norm_smul, Real.norm_eq_abs, abs_inv]
  change |m|⁻¹ * ‖∫ y in Metric.closedBall x r, φ y‖ ≤ M
  rw [abs_of_pos hm]
  calc
    m⁻¹ * ‖∫ y in Metric.closedBall x r, φ y‖
        ≤ m⁻¹ * (M * m / (1 + m)) := mul_le_mul_of_nonneg_left hrect (by positivity)
    _ = M / (1 + m) := by field_simp
    _ ≤ M := div_le_self hM (by linarith)

lemma ae_norm_le_of_rectangle_integral_bound {n : ℕ} (hn : 0 < n)
    {φ : (Fin n → ℝ) → ℂ} {M : ℝ}
    (hQ : ∀ a b : Fin n → ℝ, a ≤ b →
      IntegrableOn φ (Set.Icc a b) ∧
      ‖∫ x in Set.Icc a b, φ x‖ ≤
        M * (volume (Set.Icc a b)).toReal / (1 + (volume (Set.Icc a b)).toReal)) :
    ∀ᵐ x ∂volume, ‖φ x‖ ≤ M := by
  have hM : 0 ≤ M := nonneg_of_rectangle_integral_bound hn (fun a b hab => (hQ a b hab).2)
  have hloc : LocallyIntegrable φ volume :=
    locallyIntegrable_of_integrableOn_rectangles (fun a b hab => (hQ a b hab).1)
  have hdiff := IsUnifLocDoublingMeasure.ae_tendsto_average volume hloc 1
  filter_upwards [hdiff] with x hx
  have hxlim : Tendsto
      (fun r : ℝ => ⨍ y in Metric.closedBall x r, φ y ∂volume)
      (𝓝[>] 0) (𝓝 (φ x)) := by
    apply hx (fun _ : ℝ => x) id tendsto_id
    filter_upwards [self_mem_nhdsWithin] with r hr
    simp only [id_eq, one_mul, Metric.mem_closedBall, dist_self, norm_zero]
    exact hr.le
  apply le_of_tendsto hxlim.norm
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact norm_setAverage_closedBall_le hM (fun a b hab => (hQ a b hab).2) x hr

lemma integrable_scaled_mul_of_ae_norm_le {n : ℕ}
    {φ : (Fin n → ℝ) → ℂ} (hφ : AEStronglyMeasurable φ volume)
    {M : ℝ} (hφM : ∀ᵐ x ∂volume, ‖φ x‖ ≤ M)
    {f : (Fin n → ℝ) → ℂ} (hf : Integrable f)
    {k : ℝ} (hk : 0 < k) :
    Integrable (fun x => φ (k • x) * f x) := by
  have hqp := Measure.quasiMeasurePreserving_smul (volume : Measure (Fin n → ℝ)) hk.ne'
  have hmeas : AEStronglyMeasurable (fun x => φ (k • x) * f x) volume :=
    (hφ.comp_quasiMeasurePreserving hqp).mul hf.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂volume, ‖φ (k • x) * f x‖ ≤ M * ‖f x‖ := by
    filter_upwards [hqp.tendsto_ae hφM] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  exact Integrable.mono' (hf.norm.const_mul M) hmeas hbound

lemma smul_Icc_eq_Icc {n : ℕ} (a b : Fin n → ℝ) {k : ℝ} (hk : 0 < k) :
    k • Set.Icc a b = Set.Icc (k • a) (k • b) := by
  ext z
  rw [mem_smul_set_iff_inv_smul_mem₀ hk.ne']
  simp only [Set.mem_Icc, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro hz
    constructor
    · intro i
      have := hz.1 i
      apply (le_inv_mul_iff₀ hk).mp
      simpa [mul_comm] using this
    · intro i
      have := hz.2 i
      apply (inv_mul_le_iff₀ hk).mp
      simpa [mul_comm] using this
  · intro hz
    constructor
    · intro i
      exact (le_inv_mul_iff₀ hk).2 (by simpa [mul_comm] using hz.1 i)
    · intro i
      exact (inv_mul_le_iff₀ hk).2 (by simpa [mul_comm] using hz.2 i)

lemma setIntegral_comp_smul_Icc {n : ℕ} (φ : (Fin n → ℝ) → ℂ)
    (a b : Fin n → ℝ) {k : ℝ} (hk : 0 < k) :
    ∫ x in Set.Icc a b, φ (k • x) =
      (k ^ n)⁻¹ • ∫ y in Set.Icc (k • a) (k • b), φ y := by
  rw [Measure.setIntegral_comp_smul_of_pos volume φ (Set.Icc a b) hk,
    smul_Icc_eq_Icc a b hk]
  congr 2
  simp [Module.finrank_pi_fintype]

lemma tendsto_setIntegral_comp_smul_Icc {n : ℕ} (hn : 0 < n)
    {φ : (Fin n → ℝ) → ℂ} {M : ℝ}
    (hQ : ∀ a b : Fin n → ℝ, a ≤ b →
      IntegrableOn φ (Set.Icc a b) ∧
      ‖∫ x in Set.Icc a b, φ x‖ ≤
        M * (volume (Set.Icc a b)).toReal /
          (1 + (volume (Set.Icc a b)).toReal))
    (a b : Fin n → ℝ) (hab : a ≤ b) :
    Tendsto (fun k : ℝ => ∫ x in Set.Icc a b, φ (k • x)) atTop (𝓝 0) := by
  have hM : 0 ≤ M :=
    nonneg_of_rectangle_integral_bound hn (fun a b hab => (hQ a b hab).2)
  have hlim : Tendsto (fun k : ℝ => (k ^ n)⁻¹ * M) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop (Nat.ne_of_gt hn)).inv_tendsto_atTop.mul_const M)
  have hlimnorm : Tendsto (fun k : ℝ => ‖(k ^ n)⁻¹ * M‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using hlim.norm
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    _ hlimnorm
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk
  have hkab : k • a ≤ k • b := by
    intro i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hab i) hk.le
  let m : ℝ := (volume (Set.Icc (k • a) (k • b))).toReal
  have hm : 0 ≤ m := by positivity
  have hfrac : M * m / (1 + m) ≤ M := by
    apply (div_le_iff₀ (by positivity : 0 < 1 + m)).2
    nlinarith [mul_nonneg hM hm]
  rw [setIntegral_comp_smul_Icc φ a b hk]
  rw [Complex.real_smul]
  rw [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity : 0 ≤ (k ^ n)⁻¹)]
  calc
    (k ^ n)⁻¹ * ‖∫ y in Set.Icc (k • a) (k • b), φ y‖
        ≤ (k ^ n)⁻¹ * (M * m / (1 + m)) :=
      mul_le_mul_of_nonneg_left (hQ _ _ hkab).2 (by positivity)
    _ ≤ (k ^ n)⁻¹ * M := mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = ‖(k ^ n)⁻¹ * M‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hM)]

lemma tendsto_scaled_mul_of_L1_approx
    {n : ℕ} {φ : (Fin n → ℝ) → ℂ}
    (hφ : AEStronglyMeasurable φ volume) {M : ℝ}
    (hφM : ∀ᵐ x ∂volume, ‖φ x‖ ≤ M)
    {f : (Fin n → ℝ) → ℂ} (hf : Integrable f)
    (happrox : ∀ ε > 0, ∃ g : (Fin n → ℝ) → ℂ,
      Integrable g ∧
      Tendsto (fun k : ℝ => ∫ x, φ (k • x) * g x) atTop (𝓝 0) ∧
      ∫ x, ‖f x - g x‖ ≤ ε) :
    Tendsto (fun k : ℝ => ∫ x, φ (k • x) * f x) atTop (𝓝 0) := by
  have hM : 0 ≤ M := by
    obtain ⟨x, hx⟩ := hφM.exists
    exact (norm_nonneg (φ x)).trans hx
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hg, hglim, hfg⟩ := happrox (ε / (2 * (M + 1))) (by positivity)
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 hglim (ε / 2) (by positivity)
  refine ⟨max K 1, fun k hk => ?_⟩
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right K 1) hk)
  have hfk := integrable_scaled_mul_of_ae_norm_le hφ hφM hf hk0
  have hgk := integrable_scaled_mul_of_ae_norm_le hφ hφM hg hk0
  have hqp := Measure.quasiMeasurePreserving_smul
    (volume : Measure (Fin n → ℝ)) hk0.ne'
  have hpoint : ∀ᵐ x ∂volume,
      ‖φ (k • x) * (f x - g x)‖ ≤ M * ‖f x - g x‖ := by
    filter_upwards [hqp.tendsto_ae hφM] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  have hdiff : ‖(∫ x, φ (k • x) * f x) - ∫ x, φ (k • x) * g x‖ ≤
      M * ∫ x, ‖f x - g x‖ := by
    rw [← integral_sub hfk hgk]
    have hi : Integrable (fun x => M * ‖f x - g x‖) :=
      (hf.sub hg).norm.const_mul M
    refine (norm_integral_le_of_norm_le hi ?_).trans_eq ?_
    · filter_upwards [hpoint] with x hx
      simpa [mul_sub] using hx
    · rw [integral_const_mul]
  have hgsmall := hK k (le_trans (le_max_left K 1) hk)
  rw [dist_zero_right] at hgsmall ⊢
  calc
    ‖∫ x, φ (k • x) * f x‖
        ≤ ‖(∫ x, φ (k • x) * f x) - ∫ x, φ (k • x) * g x‖ +
            ‖∫ x, φ (k • x) * g x‖ := by
          simpa using norm_add_le
            ((∫ x, φ (k • x) * f x) - ∫ x, φ (k • x) * g x)
            (∫ x, φ (k • x) * g x)
    _ ≤ M * (∫ x, ‖f x - g x‖) + ε / 2 :=
      add_le_add hdiff hgsmall.le
    _ ≤ M * (ε / (2 * (M + 1))) + ε / 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hfg hM) le_rfl
    _ < ε := by
      have hfirst : M * (ε / (2 * (M + 1))) < ε / 2 := by
        calc
          M * (ε / (2 * (M + 1))) = ε / 2 * (M / (M + 1)) := by
            field_simp
            <;> ring
          _ < ε / 2 * 1 := by
            apply mul_lt_mul_of_pos_left _ (by positivity)
            exact (div_lt_one (by positivity)).2 (by linarith)
          _ = ε / 2 := mul_one _
      linarith

lemma integrable_indicator_const_of_lt {n : ℕ} {s : Set (Fin n → ℝ)} (hs : MeasurableSet s)
    (h : volume s < ⊤) (c : ℂ) : Integrable (s.indicator fun _ => c) volume :=
  (integrable_indicator_iff hs).2 (integrableOn_const h.ne)

lemma tendsto_scaled_mul_of_monotone {n : ℕ}
    {φ : (Fin n → ℝ) → ℂ} (hφ : AEStronglyMeasurable φ volume) {M : ℝ}
    (hφM : ∀ᵐ x ∂volume, ‖φ x‖ ≤ M)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) (hμ : volume s < ⊤) (c : ℂ)
    {U : ℕ → Set (Fin n → ℝ)} (hU : ∀ m, MeasurableSet (U m)) (hmono : Monotone U)
    (hun : ⋃ m, U m = s)
    (hP : ∀ m, Tendsto (fun k : ℝ => ∫ x, φ (k • x) * (U m).indicator (fun _ => c) x)
      atTop (𝓝 0)) :
    Tendsto (fun k : ℝ => ∫ x, φ (k • x) * s.indicator (fun _ => c) x) atTop (𝓝 0) := by
  have hsub (m : ℕ) : U m ⊆ s := hun ▸ subset_iUnion U m
  have hlt (m : ℕ) : volume (U m) < ⊤ := (measure_mono (hsub m)).trans_lt hμ
  have hB : Tendsto (fun m => volume (s \ U m)) atTop (𝓝 0) := by
    have hanti : Antitone fun m => s \ U m := fun a b hab =>
      Set.diff_subset_diff_right (hmono hab)
    have h0 := tendsto_measure_iInter_atTop (μ := volume)
      (fun m => (hs.diff (hU m)).nullMeasurableSet) hanti
      ⟨0, ((measure_mono Set.diff_subset).trans_lt hμ).ne⟩
    have hempty : ⋂ m, s \ U m = ∅ := by
      ext x
      simp only [mem_iInter, mem_diff, mem_empty_iff_false, iff_false, not_forall]
      by_cases hx : x ∈ s
      · rw [← hun] at hx
        obtain ⟨m, hm⟩ := mem_iUnion.1 hx
        exact ⟨m, fun h => h.2 hm⟩
      · exact ⟨0, fun h => hx h.1⟩
    simpa [hempty] using h0
  refine tendsto_scaled_mul_of_L1_approx hφ hφM (integrable_indicator_const_of_lt hs hμ c) ?_
  intro ε hε
  have hne : ∀ m, volume (s \ U m) ≠ ⊤ := fun m =>
    ((measure_mono Set.diff_subset).trans_lt hμ).ne
  have hT : Tendsto (fun m => ‖c‖ * (volume (s \ U m)).toReal) atTop (𝓝 0) := by
    have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hB).const_mul ‖c‖
    simpa using this
  obtain ⟨m, hm⟩ := ((tendsto_order.1 hT).2 ε hε).exists
  refine ⟨(U m).indicator fun _ => c, integrable_indicator_const_of_lt (hU m) (hlt m) c,
    hP m, ?_⟩
  have heq : (fun x => ‖s.indicator (fun _ => c) x - (U m).indicator (fun _ => c) x‖) =
      (s \ U m).indicator fun _ => ‖c‖ := by
    funext x
    by_cases h1 : x ∈ U m
    · have h2 := hsub m h1
      simp [h1, h2]
    · by_cases h2 : x ∈ s <;> simp [h1, h2]
  rw [heq, integral_indicator (hs.diff (hU m)), setIntegral_const]
  simp only [smul_eq_mul, Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  rw [mul_comm]
  exact hm.le

lemma integral_scaled_mul_indicator {n : ℕ} (φ : (Fin n → ℝ) → ℂ) (k : ℝ)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) (c : ℂ) :
    ∫ x, φ (k • x) * s.indicator (fun _ => c) x = (∫ x in s, φ (k • x)) * c := by
  have : (fun x => φ (k • x) * s.indicator (fun _ => c) x) =
      s.indicator fun x => φ (k • x) * c := by
    funext x
    by_cases h : x ∈ s <;> simp [h]
  rw [this, integral_indicator hs]
  exact integral_mul_const _ _

lemma borel_pi_eq_generateFrom_Icc {n : ℕ} :
    (inferInstance : MeasurableSpace (Fin n → ℝ)) =
      MeasurableSpace.generateFrom {S | ∃ a b : Fin n → ℝ, a ≤ b ∧ S = Set.Icc a b} := by
  let C : Fin n → Set (Set ℝ) := fun _ => {S | ∃ l u : ℝ, l ≤ u ∧ Set.Icc l u = S}
  have hC : ∀ i, MeasurableSpace.generateFrom (C i) = (inferInstance : MeasurableSpace ℝ) := by
    intro i
    rw [BorelSpace.measurable_eq (α := ℝ), borel_eq_generateFrom_Icc ℝ]
  have hspan : ∀ i, IsCountablySpanning (C i) := fun i =>
    ⟨fun N : ℕ => Set.Icc (-(N : ℝ)) N,
      fun N => ⟨_, _, by have : (0 : ℝ) ≤ N := N.cast_nonneg
                         linarith, rfl⟩,
      iUnion_eq_univ_iff.2 fun x => by
        obtain ⟨N, hN⟩ := exists_nat_ge |x|
        exact ⟨N, (abs_le.1 hN).1, (abs_le.1 hN).2⟩⟩
  have h := generateFrom_pi_eq (C := C) hspan
  have e : (fun i => MeasurableSpace.generateFrom (C i)) =
      fun _ => (inferInstance : MeasurableSpace ℝ) := funext hC
  rw [e] at h
  have hset : pi univ '' pi univ C = {S | ∃ a b : Fin n → ℝ, a ≤ b ∧ S = Set.Icc a b} := by
    ext S
    constructor
    · rintro ⟨t, ht, rfl⟩
      choose l u hlu hlu' using fun i => ht i (mem_univ i)
      refine ⟨l, u, hlu, ?_⟩
      rw [← Set.pi_univ_Icc]
      exact congrArg _ (funext fun i => (hlu' i).symm)
    · rintro ⟨a, b, hab, rfl⟩
      exact ⟨fun i => Set.Icc (a i) (b i), fun i _ => ⟨_, _, hab i, rfl⟩, Set.pi_univ_Icc a b⟩
  rw [hset] at h
  exact h

lemma isPiSystem_rectangles {n : ℕ} :
    IsPiSystem {S : Set (Fin n → ℝ) | ∃ a b : Fin n → ℝ, a ≤ b ∧ S = Set.Icc a b} := by
  rintro _ ⟨a, b, -, rfl⟩ _ ⟨c, d, -, rfl⟩ ⟨x, hx1, hx2⟩
  refine ⟨a ⊔ c, b ⊓ d, ?_, Set.Icc_inter_Icc⟩
  exact (sup_le hx1.1 hx2.1).trans (le_inf hx1.2 hx2.2)

lemma tendsto_scaled_mul_indicator_inter_cube {n : ℕ} (hn : 0 < n)
    {φ : (Fin n → ℝ) → ℂ} (hφ : AEStronglyMeasurable φ volume) {M : ℝ}
    (hQ : ∀ a b : Fin n → ℝ, a ≤ b →
      IntegrableOn φ (Set.Icc a b) ∧
      ‖∫ x in Set.Icc a b, φ x‖ ≤
        M * (volume (Set.Icc a b)).toReal / (1 + (volume (Set.Icc a b)).toReal))
    (l u : Fin n → ℝ) (hlu : l ≤ u) (c : ℂ) {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) :
    Tendsto (fun k : ℝ => ∫ x, φ (k • x) * (s ∩ Set.Icc l u).indicator (fun _ => c) x)
      atTop (𝓝 0) := by
  have hφM := ae_norm_le_of_rectangle_integral_bound hn hQ
  have hW : volume (Set.Icc l u) < ⊤ := isCompact_Icc.measure_lt_top
  have hbox (a b : Fin n → ℝ) (hab : a ≤ b) :
      Tendsto (fun k : ℝ => ∫ x, φ (k • x) * (Set.Icc a b).indicator (fun _ => c) x)
        atTop (𝓝 0) := by
    simp only [integral_scaled_mul_indicator φ _ measurableSet_Icc c]
    simpa using (tendsto_setIntegral_comp_smul_Icc hn hQ a b hab).mul_const c
  have hint (t : Set (Fin n → ℝ)) (ht : MeasurableSet t) (hlt : volume t < ⊤) (k : ℝ)
      (hk : 0 < k) : Integrable (fun x => φ (k • x) * t.indicator (fun _ => c) x) :=
    integrable_scaled_mul_of_ae_norm_le hφ hφM (integrable_indicator_const_of_lt ht hlt c) hk
  have hsmall (t : Set (Fin n → ℝ)) : volume (t ∩ Set.Icc l u) < ⊤ :=
    (measure_mono inter_subset_right).trans_lt hW
  induction s, hs using MeasurableSpace.induction_on_inter
      (borel_pi_eq_generateFrom_Icc (n := n)) isPiSystem_rectangles with
  | empty => simp
  | basic t ht =>
    obtain ⟨a, b, hab, rfl⟩ := ht
    rw [Set.Icc_inter_Icc]
    by_cases h : a ⊔ l ≤ b ⊓ u
    · exact hbox _ _ h
    · simp [Set.Icc_eq_empty h]
  | compl t ht ih =>
    have hEq : ∀ᶠ k : ℝ in atTop,
        (∫ x, φ (k • x) * (Set.Icc l u).indicator (fun _ => c) x) -
            ∫ x, φ (k • x) * (t ∩ Set.Icc l u).indicator (fun _ => c) x =
          ∫ x, φ (k • x) * (tᶜ ∩ Set.Icc l u).indicator (fun _ => c) x := by
      filter_upwards [eventually_gt_atTop 0] with k hk
      rw [← integral_sub (hint _ measurableSet_Icc hW k hk)
        (hint _ (ht.inter measurableSet_Icc) (hsmall t) k hk)]
      congr 1
      funext x
      by_cases h1 : x ∈ t <;> by_cases h2 : x ∈ Set.Icc l u <;> simp [h1, h2]
    have := (hbox l u hlu).sub ih
    rw [sub_zero] at this
    exact this.congr' hEq
  | iUnion F hd hF ih =>
    let A : ℕ → Set (Fin n → ℝ) := fun i => F i ∩ Set.Icc l u
    let U : ℕ → Set (Fin n → ℝ) := fun m => ⋃ i ∈ Finset.range m, A i
    have hA : ∀ i, MeasurableSet (A i) := fun i => (hF i).inter measurableSet_Icc
    have hdA : Pairwise (Function.onFun Disjoint A) := fun i j hij =>
      (hd hij).mono inter_subset_left inter_subset_left
    refine tendsto_scaled_mul_of_monotone hφ hφM
      ((MeasurableSet.iUnion hF).inter measurableSet_Icc) (hsmall _) c (U := U)
      (fun m => Finset.measurableSet_biUnion _ fun i _ => hA i) ?_ ?_ ?_
    · intro a b hab
      exact biUnion_subset_biUnion_left (fun i hi => by
        simp only [Finset.coe_range, mem_Iio] at hi ⊢
        omega)
    · ext x
      simp only [U, A, mem_iUnion, mem_inter_iff, Finset.mem_range, exists_prop]
      constructor
      · rintro ⟨m, i, -, h1, h2⟩
        exact ⟨⟨i, h1⟩, h2⟩
      · rintro ⟨⟨i, h1⟩, h2⟩
        exact ⟨i + 1, i, by omega, h1, h2⟩
    · intro m
      induction m with
      | zero => simp [U]
      | succ m ihm =>
        have hUm : MeasurableSet (U m) := Finset.measurableSet_biUnion _ fun i _ => hA i
        have hUlt : volume (U m) < ⊤ := by
          refine (measure_mono ?_).trans_lt hW
          exact iUnion₂_subset fun i _ => inter_subset_right
        have hEq : ∀ᶠ k : ℝ in atTop,
            (∫ x, φ (k • x) * (U m).indicator (fun _ => c) x) +
                ∫ x, φ (k • x) * (A m).indicator (fun _ => c) x =
              ∫ x, φ (k • x) * (U (m + 1)).indicator (fun _ => c) x := by
          filter_upwards [eventually_gt_atTop 0] with k hk
          rw [← integral_add (hint _ hUm hUlt k hk) (hint _ (hA m) (hsmall _) k hk)]
          congr 1
          funext x
          have hdisj : x ∈ A m → x ∉ U m := fun h1 h2 => by
            simp only [U, mem_iUnion, Finset.mem_range, exists_prop] at h2
            obtain ⟨i, hi, h3⟩ := h2
            exact Set.disjoint_left.1 (hdA (by omega : i ≠ m)) h3 h1
          have hmem : x ∈ U (m + 1) ↔ x ∈ U m ∨ x ∈ A m := by
            simp only [U, mem_iUnion, Finset.mem_range, exists_prop]
            constructor
            · rintro ⟨i, hi, h⟩
              by_cases him : i = m
              · exact Or.inr (him ▸ h)
              · exact Or.inl ⟨i, by omega, h⟩
            · rintro (⟨i, hi, h⟩ | h)
              · exact ⟨i, by omega, h⟩
              · exact ⟨m, by omega, h⟩
          by_cases h1 : x ∈ U m
          · have h2 : x ∉ A m := fun h => hdisj h h1
            have h3 : x ∈ U (m + 1) := hmem.2 (Or.inl h1)
            simp [h1, h2, h3]
          · by_cases h2 : x ∈ A m
            · have h3 : x ∈ U (m + 1) := hmem.2 (Or.inr h2)
              simp [h1, h2, h3]
            · have h3 : x ∉ U (m + 1) := fun h => (hmem.1 h).elim h1 h2
              simp [h1, h2, h3]
        have := ihm.add (ih m)
        rw [add_zero] at this
        exact this.congr' hEq

lemma tendsto_scaled_mul_indicator
    {n : ℕ} (hn : 0 < n)
    {φ : (Fin n → ℝ) → ℂ}
    (hφ : AEStronglyMeasurable φ volume) {M : ℝ}
    (hQ : ∀ a b : Fin n → ℝ, a ≤ b →
      IntegrableOn φ (Set.Icc a b) ∧
      ‖∫ x in Set.Icc a b, φ x‖ ≤
        M * (volume (Set.Icc a b)).toReal /
          (1 + (volume (Set.Icc a b)).toReal))
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s)
    (hμs : volume s < ⊤) (c : ℂ) :
    Tendsto (fun k : ℝ => ∫ x, φ (k • x) * s.indicator (fun _ => c) x) atTop (𝓝 0) := by
  have hφM := ae_norm_le_of_rectangle_integral_bound hn hQ
  let W : ℕ → Set (Fin n → ℝ) := fun N => Set.Icc (fun _ => -(N : ℝ)) (fun _ => (N : ℝ))
  have hle (N : ℕ) : (fun _ : Fin n => -(N : ℝ)) ≤ fun _ => (N : ℝ) := fun _ => by
    have : (0 : ℝ) ≤ N := N.cast_nonneg
    simp only
    linarith
  refine tendsto_scaled_mul_of_monotone hφ hφM hs hμs c (U := fun N => s ∩ W N)
    (fun N => hs.inter measurableSet_Icc) ?_ ?_
    (fun N => tendsto_scaled_mul_indicator_inter_cube hn hφ hQ _ _ (hle N) c hs)
  · intro a b hab
    refine inter_subset_inter_right _ (Set.Icc_subset_Icc ?_ ?_)
    · intro i
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      simp only
      linarith
    · intro i
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      simpa using this
  · ext x
    simp only [mem_iUnion, mem_inter_iff, exists_and_left, and_iff_left_iff_imp]
    intro _
    obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
    refine ⟨N, fun i => ?_, fun i => ?_⟩
    · have := (abs_le.1 ((norm_le_pi_norm x i).trans hN)).1
      simpa using this
    · have := (abs_le.1 ((norm_le_pi_norm x i).trans hN)).2
      simpa using this

/-- APM a02J03.  The rectangles are the axis-parallel boxes `Set.Icc a b`.  The printed
`k > 0` clashes with the limit `k → ∞`; `k` is the limit variable here, over the reals.  The
printed bound presupposes that `φ` has a finite Lebesgue integral on each rectangle, which is
`IntegrableOn`; no other integrability is assumed, and the hypothesis forces `‖φ‖ ≤ M` a.e.,
so the conclusion's integrals are genuine (first clause).  `0 < n` is needed: on the
one-point space `ℝ⁰`, a nonzero constant `φ` with `f = 1` is a counterexample. -/
theorem apm_a02j03 {n : ℕ} (hn : 0 < n) {φ : (Fin n → ℝ) → ℂ}
    (hφ : AEStronglyMeasurable φ volume) {M : ℝ}
    (hQ : ∀ a b : Fin n → ℝ, a ≤ b →
      IntegrableOn φ (Set.Icc a b) ∧
      ‖∫ x in Set.Icc a b, φ x‖ ≤
        M * (volume (Set.Icc a b)).toReal /
          (1 + (volume (Set.Icc a b)).toReal))
    {f : (Fin n → ℝ) → ℂ} (hf : Integrable f) :
    (∀ k : ℝ, 0 < k → Integrable (fun x => φ (k • x) * f x)) ∧
    Tendsto (fun k : ℝ => ∫ x, φ (k • x) * f x) atTop (𝓝 0) := by
  have hφM := ae_norm_le_of_rectangle_integral_bound hn hQ
  refine ⟨fun k hk => integrable_scaled_mul_of_ae_norm_le hφ hφM hf hk, ?_⟩
  let P : ((Fin n → ℝ) → ℂ) → Prop := fun g =>
    Tendsto (fun k : ℝ => ∫ x, φ (k • x) * g x) atTop (𝓝 0)
  refine Integrable.induction (μ := volume) P ?_ ?_ ?_ ?_ hf
  · intro c s hs hμ
    exact tendsto_scaled_mul_indicator hn hφ hQ hs hμ c
  · intro g h _ hg hh pg ph
    have hEq : ∀ᶠ k : ℝ in atTop,
        (∫ x, φ (k • x) * g x) + (∫ x, φ (k • x) * h x) =
          ∫ x, φ (k • x) * (g + h) x := by
      filter_upwards [eventually_gt_atTop 0] with k hk
      rw [← integral_add (integrable_scaled_mul_of_ae_norm_le hφ hφM hg hk)
        (integrable_scaled_mul_of_ae_norm_le hφ hφM hh hk)]
      congr 1
      funext x
      simp [mul_add]
    have := pg.add ph
    rw [add_zero] at this
    exact this.congr' hEq
  · refine isClosed_of_closure_subset fun g hg => ?_
    refine tendsto_scaled_mul_of_L1_approx hφ hφM (L1.integrable_coeFn g) ?_
    intro ε hε
    obtain ⟨h, hhP, hd⟩ := Metric.mem_closure_iff.1 hg ε hε
    refine ⟨h, L1.integrable_coeFn h, hhP, ?_⟩
    have h1 : ∫ x, ‖g x - h x‖ = ‖g - h‖ := by
      rw [L1.norm_eq_integral_norm]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub g h] with x hx
      rw [hx]
      rfl
    rw [h1, ← dist_eq_norm]
    exact hd.le
  · intro g h hgh _ pg
    refine pg.congr fun k => integral_congr_ae ?_
    filter_upwards [hgh] with x hx
    rw [hx]
