import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Data.ENNReal.Holder

open MeasureTheory Set ENNReal Topology

noncomputable section

/-! # APM a02J01: Schur test — L² boundedness of integral operators

  Given k : ℝⁿ × ℝⁿ → ℝ measurable with:
    Row bound:    ∫ |k(x,y)| dy ≤ 1  a.e. x
    Column bound: ∫ |k(x,y)| dx ≤ 1  a.e. y
  Prove: ‖Tu‖₂ ≤ ‖u‖₂  where Tu(x) = ∫ k(x,y) u(y) dy

  Proof sketch:
  Step 1 (Cauchy-Schwarz): |Tu(x)|² ≤ (∫|k(x,y)|dy)(∫|k(x,y)||u(y)|²dy) ≤ ∫|k(x,y)||u(y)|²dy
  Step 2 (Fubini + column bound): ∫_x(∫_y|k(x,y)||u(y)|²dy)dx = ∫_y|u(y)|²(∫_x|k(x,y)|dx)dy ≤ ‖u‖₂²
-/

variable {d : ℕ}

-- The integral operator
def integralOp (k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (u : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) : ℝ :=
  ∫ y, k x y * u y

-- Step 1: Pointwise Cauchy-Schwarz bound
-- |Tu(x)|² ≤ ∫ |k(x,y)| |u(y)|² dy  (when ∫|k(x,y)|dy ≤ 1)
--
-- Proof idea: |Tu(x)| ≤ ∫|k(x,y)||u(y)|dy
--   = ∫ |k|^{1/2} · |k|^{1/2}|u| dy
--   ≤ (∫|k|dy)^{1/2} (∫|k||u|²dy)^{1/2}  (Cauchy-Schwarz)
-- Square: |Tu(x)|² ≤ (∫|k|dy)(∫|k||u|²dy) ≤ 1 · ∫|k||u|²dy
--
-- Mathlib path: norm_integral_le_of_norm_le for the first bound,
-- then inner_mul_le_norm_mul_norm or sq_nonneg manipulations.
-- The split |k| = |k|^{1/2}·|k|^{1/2} is the non-trivial step —
-- needs MeasureTheory.integral_mul_le_Lp_mul_Lq with p=q=2
-- applied to f=|k|^{1/2} and g=|k|^{1/2}·|u|.
-- CLOSED: |∫ f|² ≤ (∫ ‖f‖)²
lemma sq_integral_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f : α → ℝ) :
    (∫ x, f x ∂μ) ^ 2 ≤ (∫ x, ‖f x‖ ∂μ) ^ 2 := by
  have h : |∫ x, f x ∂μ| ≤ ∫ x, ‖f x‖ ∂μ := norm_integral_le_integral_norm f
  have hnn : 0 ≤ ∫ x, ‖f x‖ ∂μ := integral_nonneg (fun x => norm_nonneg _)
  calc (∫ x, f x ∂μ) ^ 2 = |∫ x, f x ∂μ| ^ 2 := by rw [sq_abs]
    _ ≤ (∫ x, ‖f x‖ ∂μ) ^ 2 := by
        exact sq_le_sq' (by linarith [abs_nonneg (∫ x, f x ∂μ)]) h

-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): require the kernel row and
-- weighted-square integrand to be integrable, so neither displayed Bochner
-- integral can acquire the `integral_undef = 0` junk value.
lemma schur_pointwise
    (k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (u : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ)
    (hrow_int : Integrable (fun y => ‖k x y‖) volume)
    (hweighted_int : Integrable (fun y => ‖k x y‖ * (u y) ^ 2) volume)
    (hrow : ∫ y, ‖k x y‖ ≤ 1) :
    (integralOp k u x) ^ 2 ≤ ∫ y, ‖k x y‖ * (u y) ^ 2 := by
  -- Step 1: |Tu(x)|² ≤ (∫ ‖k(x,·) * u‖)² via sq_integral_le
  -- Step 2: (∫ ‖k·u‖)² = (∫ ‖k‖^{1/2} · ‖k‖^{1/2}|u|)²
  --         ≤ (∫ ‖k‖)(∫ ‖k‖·u²) via Cauchy-Schwarz (p=q=2)
  -- Step 3: ∫ ‖k‖ ≤ 1, so the bound is ∫ ‖k‖·u²
  -- Blocker: integral_mul_le_Lp_mul_Lq_of_nonneg needs
  -- HolderConjugate.two_two + MemLp for √|k| and √|k|·|u|
  sorry

-- Step 2: Integrate and swap (Fubini + column bound)
-- ∫_x (∫_y |k(x,y)| |u(y)|² dy) dx
--   = ∫_y |u(y)|² (∫_x |k(x,y)| dx) dy    (Fubini-Tonelli)
--   ≤ ∫_y |u(y)|² · 1 dy                    (column bound)
--   = ‖u‖₂²
--
-- Mathlib path: MeasureTheory.lintegral_lintegral_swap for Tonelli,
-- or MeasureTheory.integral_integral_swap for Bochner integrals.
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): require integrable kernel
-- columns and an L² input, preventing junk-valued column and square integrals.
lemma schur_fubini
    (k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (u : (Fin d → ℝ) → ℝ)
    (hk_meas : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => k p.1 p.2))
    (hcol_int : ∀ᵐ y ∂volume, Integrable (fun x => ‖k x y‖) volume)
    (hcol : ∀ᵐ y ∂volume, ∫ x, ‖k x y‖ ≤ 1)
    (hu : MemLp u 2 volume) :
    ∫ x, (∫ y, ‖k x y‖ * (u y) ^ 2) ≤ ∫ y, (u y) ^ 2 := by
  -- API path: integral_integral_swap (Fubini) + integral_mono (column bound)
  -- 1. Swap: ∫_x ∫_y |k(x,y)| u(y)² dy dx = ∫_y ∫_x |k(x,y)| u(y)² dx dy
  --    via integral_integral_swap (needs Integrable (uncurry ...) for product measure)
  -- 2. Factor: ∫_y (u(y)² ∫_x |k(x,y)| dx) dy
  --    via integral_mul_left or pulling u(y)² out of inner integral
  -- 3. Bound: ∫_x |k(x,y)| dx ≤ 1 a.e. y (column bound)
  -- 4. integral_mono: ∫_y u(y)² · (∫_x |k|dx) ≤ ∫_y u(y)² · 1
  sorry

-- Main theorem: Schur test
-- Combines pointwise bound + Fubini step
-- ‖Tu‖₂² = ∫|Tu(x)|²dx ≤ ∫_x ∫_y |k(x,y)||u(y)|²dy dx ≤ ‖u‖₂²
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): require a.e. integrability of
-- both kernel sections so the Schur bounds cannot hold via `integral_undef`.
theorem schur_test
    (k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
    (hk_meas : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => k p.1 p.2))
    (hrow_int : ∀ᵐ x ∂volume, Integrable (fun y => ‖k x y‖) volume)
    (hcol_int : ∀ᵐ y ∂volume, Integrable (fun x => ‖k x y‖) volume)
    (hrow : ∀ᵐ x ∂volume, ∫ y, ‖k x y‖ ≤ 1)
    (hcol : ∀ᵐ y ∂volume, ∫ x, ‖k x y‖ ≤ 1)
    (u : (Fin d → ℝ) → ℝ) (hu : MemLp u 2 volume) :
    eLpNorm (integralOp k u) 2 volume ≤ eLpNorm u 2 volume := by
  -- ‖Tu‖₂² ≤ ‖u‖₂² via:
  -- 1. ∫|Tu(x)|²dx ≤ ∫_x ∫_y |k(x,y)||u(y)|²dy dx  (schur_pointwise + integral_mono)
  -- 2. RHS ≤ ∫_y |u(y)|²dy = ‖u‖₂²  (schur_fubini)
  -- 3. ‖Tu‖₂ ≤ ‖u‖₂  (monotonicity of sqrt)
  --
  -- Mathlib path for eLpNorm comparison:
  -- eLpNorm_le_eLpNorm_of_ae_bound or rpow_le_rpow monotonicity
  -- after converting eLpNorm² to integrals via eLpNorm_rpow_eq_lintegral
  sorry
