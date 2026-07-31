import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
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
  let a : (Fin d → ℝ) → ℝ := fun y => √‖k x y‖
  let b : (Fin d → ℝ) → ℝ := fun y => √(‖k x y‖ * (u y) ^ 2)
  have ha_meas : AEStronglyMeasurable a volume :=
    hrow_int.1.aemeasurable.sqrt.aestronglyMeasurable
  have hb_meas : AEStronglyMeasurable b volume :=
    hweighted_int.1.aemeasurable.sqrt.aestronglyMeasurable
  have ha_mem : MemLp a 2 volume := by
    rw [memLp_two_iff_integrable_sq ha_meas]
    apply hrow_int.congr
    filter_upwards with y
    exact (Real.sq_sqrt (norm_nonneg (k x y))).symm
  have hb_mem : MemLp b 2 volume := by
    rw [memLp_two_iff_integrable_sq hb_meas]
    apply hweighted_int.congr
    filter_upwards with y
    exact
      (Real.sq_sqrt
        (mul_nonneg (norm_nonneg (k x y)) (sq_nonneg (u y)))).symm
  have ha_mem' : MemLp a (ENNReal.ofReal 2) volume := by
    norm_num
    exact ha_mem
  have hb_mem' : MemLp b (ENNReal.ofReal 2) volume := by
    norm_num
    exact hb_mem
  have hholder :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := volume) (f := a) (g := b) Real.HolderConjugate.two_two
      (ae_of_all _ fun y => Real.sqrt_nonneg _)
      (ae_of_all _ fun y => Real.sqrt_nonneg _)
      ha_mem' hb_mem'
  have hab :
      (∫ y, ‖k x y * u y‖) ≤
        √(∫ y, ‖k x y‖) *
          √(∫ y, ‖k x y‖ * (u y) ^ 2) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hholder
    calc
      (∫ y, ‖k x y * u y‖) = ∫ y, a y * b y := by
        apply integral_congr_ae
        filter_upwards with y
        change ‖k x y * u y‖ =
          √‖k x y‖ * √(‖k x y‖ * (u y) ^ 2)
        rw [norm_mul, Real.sqrt_mul (norm_nonneg (k x y)),
          Real.sqrt_sq_eq_abs, ← mul_assoc, ← pow_two,
          Real.sq_sqrt (norm_nonneg (k x y))]
        simp only [Real.norm_eq_abs]
      _ ≤ √(∫ y, a y ^ 2) * √(∫ y, b y ^ 2) := hholder
      _ = √(∫ y, ‖k x y‖) *
          √(∫ y, ‖k x y‖ * (u y) ^ 2) := by
        congr 2 <;> apply integral_congr_ae <;> filter_upwards with y
        · rw [Real.rpow_two]
          exact Real.sq_sqrt (norm_nonneg (k x y))
        · rw [Real.rpow_two]
          exact
            Real.sq_sqrt
              (mul_nonneg (norm_nonneg (k x y)) (sq_nonneg (u y)))
  have hsq := sq_integral_le (μ := volume) (fun y => k x y * u y)
  have hnorm_nonneg : 0 ≤ ∫ y, ‖k x y * u y‖ :=
    integral_nonneg fun _ => norm_nonneg _
  have hweighted_nonneg :
      0 ≤ ∫ y, ‖k x y‖ * (u y) ^ 2 :=
    integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hsqrt_row :
      (√(∫ y, ‖k x y‖)) ^ 2 = ∫ y, ‖k x y‖ :=
    Real.sq_sqrt (integral_nonneg fun _ => norm_nonneg _)
  have hsqrt_weighted :
      (√(∫ y, ‖k x y‖ * (u y) ^ 2)) ^ 2 =
        ∫ y, ‖k x y‖ * (u y) ^ 2 :=
    Real.sq_sqrt hweighted_nonneg
  change (∫ y, k x y * u y) ^ 2 ≤ _
  calc
    (∫ y, k x y * u y) ^ 2 ≤ (∫ y, ‖k x y * u y‖) ^ 2 := hsq
    _ ≤ (√(∫ y, ‖k x y‖) *
          √(∫ y, ‖k x y‖ * (u y) ^ 2)) ^ 2 := by
      nlinarith
    _ ≤ ∫ y, ‖k x y‖ * (u y) ^ 2 := by
      rw [mul_pow, hsqrt_row, hsqrt_weighted]
      nlinarith

-- Step 2: Integrate and swap (Fubini + column bound)
-- ∫_x (∫_y |k(x,y)| |u(y)|² dy) dx
--   = ∫_y |u(y)|² (∫_x |k(x,y)| dx) dy    (Fubini-Tonelli)
--   ≤ ∫_y |u(y)|² · 1 dy                    (column bound)
--   = ‖u‖₂²
--
-- Mathlib path: MeasureTheory.lintegral_lintegral_swap for Tonelli,
-- or MeasureTheory.integral_integral_swap for Bochner integrals.
private lemma schur_weight_integrable
    (k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (u : (Fin d → ℝ) → ℝ)
    (hk_meas : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => k p.1 p.2))
    (hcol_int : ∀ᵐ y ∂volume, Integrable (fun x => ‖k x y‖) volume)
    (hcol : ∀ᵐ y ∂volume, ∫ x, ‖k x y‖ ≤ 1)
    (hu : MemLp u 2 volume) :
    Integrable
      (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
        ‖k p.1 p.2‖ * (u p.2) ^ 2)
      (volume.prod volume) := by
  let F : ((Fin d → ℝ) × (Fin d → ℝ)) → ℝ :=
    fun p => ‖k p.1 p.2‖ * (u p.2) ^ 2
  have hF_meas : AEStronglyMeasurable F (volume.prod volume) := by
    exact hk_meas.norm.aestronglyMeasurable.mul (hu.1.comp_snd.pow 2)
  rw [integrable_prod_iff' hF_meas]
  constructor
  · filter_upwards [hcol_int] with y hy
    exact hy.mul_const ((u y) ^ 2)
  · have hcol_meas : AEStronglyMeasurable
        (fun y => ∫ x, ‖k x y‖) volume :=
      hk_meas.norm.aestronglyMeasurable.prod_swap.integral_prod_right'
    have hbound : Integrable
        (fun y => (∫ x, ‖k x y‖) * (u y) ^ 2) volume := by
      apply hu.integrable_sq.mono (hcol_meas.mul (hu.1.pow 2))
      filter_upwards [hcol] with y hy
      have hcol_nonneg : 0 ≤ ∫ x, ‖k x y‖ :=
        integral_nonneg fun _ => norm_nonneg _
      have hu_nonneg : 0 ≤ (u y) ^ 2 := sq_nonneg _
      change ‖(∫ x, ‖k x y‖) * (u y) ^ 2‖ ≤ ‖(u y) ^ 2‖
      rw [Real.norm_of_nonneg (mul_nonneg hcol_nonneg hu_nonneg),
        Real.norm_of_nonneg hu_nonneg]
      nlinarith
    apply hbound.congr
    filter_upwards with y
    have hu_nonneg : 0 ≤ (u y) ^ 2 := sq_nonneg _
    simp only [F, Real.norm_of_nonneg
      (mul_nonneg (norm_nonneg _) hu_nonneg), integral_mul_const]

-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): require integrable kernel
-- columns and an L² input, preventing junk-valued column and square integrals.
lemma schur_fubini
    (k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (u : (Fin d → ℝ) → ℝ)
    (hk_meas : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => k p.1 p.2))
    (hcol_int : ∀ᵐ y ∂volume, Integrable (fun x => ‖k x y‖) volume)
    (hcol : ∀ᵐ y ∂volume, ∫ x, ‖k x y‖ ≤ 1)
    (hu : MemLp u 2 volume) :
    ∫ x, (∫ y, ‖k x y‖ * (u y) ^ 2) ≤ ∫ y, (u y) ^ 2 := by
  have hF := schur_weight_integrable k u hk_meas hcol_int hcol hu
  rw [integral_integral_swap hF]
  have hleft : Integrable
      (fun y => ∫ x, ‖k x y‖ * (u y) ^ 2) volume :=
    hF.integral_prod_right
  apply integral_mono_ae hleft hu.integrable_sq
  filter_upwards [hcol, hcol_int] with y hy hy_int
  rw [integral_mul_const]
  nlinarith [sq_nonneg (u y)]

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
  have hF := schur_weight_integrable k u hk_meas hcol_int hcol hu
  have hweighted_int :
      Integrable (fun x => ∫ y, ‖k x y‖ * (u y) ^ 2) volume :=
    hF.integral_prod_left
  have hweighted_sections :
      ∀ᵐ x ∂volume,
        Integrable (fun y => ‖k x y‖ * (u y) ^ 2) volume :=
    hF.prod_right_ae
  have hpoint :
      ∀ᵐ x ∂volume,
        (integralOp k u x) ^ 2 ≤
          ∫ y, ‖k x y‖ * (u y) ^ 2 := by
    filter_upwards [hrow_int, hweighted_sections, hrow] with x hxrow hxweighted hx
    exact schur_pointwise k u x hxrow hxweighted hx
  have hTu_meas : AEStronglyMeasurable (integralOp k u) volume := by
    change AEStronglyMeasurable
      (fun x => ∫ y, k x y * u y) volume
    exact
      (hk_meas.aestronglyMeasurable.mul hu.1.comp_snd).integral_prod_right'
  have hTu_sq_int : Integrable (fun x => (integralOp k u x) ^ 2) volume := by
    apply hweighted_int.mono (hTu_meas.pow 2)
    filter_upwards [hpoint] with x hx
    have hleft_nonneg : 0 ≤ (integralOp k u x) ^ 2 := sq_nonneg _
    have hright_nonneg :
        0 ≤ ∫ y, ‖k x y‖ * (u y) ^ 2 :=
      integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)
    change ‖(integralOp k u x) ^ 2‖ ≤
      ‖∫ y, ‖k x y‖ * (u y) ^ 2‖
    rw [Real.norm_of_nonneg hleft_nonneg,
      Real.norm_of_nonneg hright_nonneg]
    exact hx
  have hTu : MemLp (integralOp k u) 2 volume := by
    rw [memLp_two_iff_integrable_sq hTu_meas]
    exact hTu_sq_int
  have hsq :
      (∫ x, (integralOp k u x) ^ 2) ≤ ∫ x, (u x) ^ 2 := by
    calc
      _ ≤ ∫ x, (∫ y, ‖k x y‖ * (u y) ^ 2) :=
        integral_mono_ae hTu_sq_int hweighted_int hpoint
      _ ≤ _ := schur_fubini k u hk_meas hcol_int hcol hu
  rw [hTu.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    hu.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  norm_num
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow
    (integral_nonneg fun _ => sq_nonneg _) hsq (by norm_num)
