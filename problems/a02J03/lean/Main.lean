import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

open MeasureTheory Set Filter Topology

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
  -- Density argument:
  -- For ε > 0, pick step function s with ‖f - s‖₁ < ε/(2M).
  -- |T_k(f)| ≤ |T_k(s)| + |T_k(f-s)| ≤ |T_k(s)| + M·ε/(2M) = |T_k(s)| + ε/2.
  -- T_k(s) → 0 (finite sum of indicator cases).
  -- So lim sup |T_k(f)| ≤ ε/2 < ε.
  --
  -- Mathlib path:
  -- The uniform estimate is now closed via Lebesgue differentiation:
  -- `ae_abs_le_of_interval_integral_bound` proves `|φ| ≤ M` a.e.
  -- Remaining construction: prove that finite linear combinations of bounded
  -- interval indicators are dense in real `L¹`, or equivalently prove
  -- convergence first on compactly supported smooth functions and invoke
  -- `MemLp.exist_eLpNorm_sub_le`. Generic measurable simple functions are not
  -- enough here because `indicator_case` only controls interval indicators.
  -- Uniform bound: uniform_bound lemma
  -- Filter arithmetic: Tendsto.add, squeeze_zero_norm
  sorry
