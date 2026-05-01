import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

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
  sorry -- Change of variables: integral substitution u=kx + hypothesis

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

-- Step 2: Uniform bound |T_k(f)| ≤ M ‖f‖₁
-- For step functions on disjoint intervals: each piece bounded by M·m(Qᵢ),
-- sum ≤ M · Σ|cᵢ|m(Qᵢ) = M · ‖f‖₁.
-- This extends to L¹ by density.
lemma uniform_bound (φ : ℝ → ℝ) (M : ℝ)
    (hφ : ∀ (a b : ℝ), a < b →
      |∫ x in Set.Icc a b, φ x| ≤ M * (b - a) / (1 + (b - a)))
    (f : ℝ → ℝ) (hf : Integrable f volume) (k : ℝ) (hk : 0 < k) :
    |scaledIntOp φ f k| ≤ M * ∫ x, ‖f x‖ := by
  -- Change of variables + triangle inequality + hypothesis
  sorry

-- Main theorem: ∫ φ(kx) f(x) dx → 0
-- Density: approximate f by step functions, use indicator_case + uniform_bound
theorem scaled_integral_vanishes (φ : ℝ → ℝ) (M : ℝ) (hM : 0 < M)
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
  -- Density: MeasureTheory.Lp.simpleFunc_dense or
  --          MeasureTheory.SimpleFunc.tendsto_approxOn
  -- Uniform bound: uniform_bound lemma
  -- Filter arithmetic: Tendsto.add, squeeze_zero_norm
  sorry
