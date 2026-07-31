import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# APM a94A04: Orthogonality to all monomials implies zero a.e.

**Problem.** If f : [0,1] -> R is square integrable and satisfies
integral_0^1 x^n f(x) dx = 0 for n = 0,1,2,..., then f = 0 a.e.

## Proof

By linearity, integral p(x) f(x) dx = 0 for every polynomial p.
By Weierstrass, polynomials are dense in C([0,1]), hence dense in L^2.
So f is orthogonal to a dense subspace, forcing ||f||^2 = 0, hence f = 0 a.e.
-/

set_option linter.unusedVariables false in
noncomputable section

open MeasureTheory Set Filter Polynomial
open scoped Topology BoundedContinuousFunction

namespace ApmCanaries.A94A04

/-- Orthogonality extends to all polynomials by linearity. -/
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): require each monomial product
-- to be integrable, so the zero moments are not values from `integral_undef`.
lemma orthogonal_to_polynomials
    {f : ℝ → ℝ} {μ : Measure ℝ}
    (hint : ∀ n : ℕ,
      Integrable (fun x => x ^ n * f x) (μ.restrict (Icc (0 : ℝ) 1)))
    (horth : ∀ n : ℕ, ∫ x in Icc (0:ℝ) 1, x ^ n * f x ∂μ = 0)
    (p : Polynomial ℝ) :
    ∫ x in Icc (0:ℝ) 1, Polynomial.eval x p * f x ∂μ = 0 := by
  have hintp : ∀ q : Polynomial ℝ,
      Integrable (fun x => Polynomial.eval x q * f x)
        (μ.restrict (Icc (0 : ℝ) 1)) := by
    intro q
    induction q using Polynomial.induction_on' with
    | monomial k a =>
      simpa only [Polynomial.eval_monomial, mul_assoc, mul_left_comm, mul_comm] using
        (hint k).const_mul a
    | add q r hq hr =>
      simpa only [Polynomial.eval_add, add_mul] using hq.add hr
  induction p using Polynomial.induction_on' with
  | monomial k a =>
    simp only [Polynomial.eval_monomial]
    calc
      (∫ x in Icc (0 : ℝ) 1, a * x ^ k * f x ∂μ) =
          ∫ x in Icc (0 : ℝ) 1, a * (x ^ k * f x) ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = a * ∫ x in Icc (0 : ℝ) 1, x ^ k * f x ∂μ := by
            rw [integral_const_mul]
      _ = 0 := by rw [horth k, mul_zero]
  | add p q hp hq =>
    have heval : ∀ x, Polynomial.eval x (p + q) * f x =
        Polynomial.eval x p * f x + Polynomial.eval x q * f x := by
      intro x; rw [Polynomial.eval_add, add_mul]
    rw [show (∫ x in Icc (0:ℝ) 1, Polynomial.eval x (p + q) * f x ∂μ) =
        ∫ x in Icc (0:ℝ) 1, (Polynomial.eval x p * f x + Polynomial.eval x q * f x) ∂μ by
      congr 1 with x; exact heval x]
    rw [integral_add (hintp p) (hintp q), hp, hq, add_zero]

/-- **Main theorem:** f in L^2([0,1]) orthogonal to all monomials is zero a.e.

    **SORRY BOUNDARY:** The proof requires three density arguments:
    (1) Polynomials dense in C([0,1]) via Stone-Weierstrass.
    (2) C([0,1]) dense in L^2([0,1]) via `boundedContinuousFunction_dense`.
    (3) Orthogonality to a dense subspace gives ||f||^2 = 0, hence f = 0 a.e. -/
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): require the restricted
-- measure to be finite, so the L² hypothesis makes all moments integrable.
theorem zero_of_orthogonal_to_monomials
    {f : ℝ → ℝ} {μ : Measure ℝ}
    [IsFiniteMeasure (μ.restrict (Icc (0 : ℝ) 1))]
    (hf : MemLp f 2 (μ.restrict (Icc (0:ℝ) 1)))
    (hfm : AEStronglyMeasurable f (μ.restrict (Icc (0:ℝ) 1)))
    (horth : ∀ n : ℕ, ∫ x in Icc (0:ℝ) 1, x ^ n * f x ∂μ = 0) :
    f =ᵐ[μ.restrict (Icc (0:ℝ) 1)] 0 := by
  let ν := μ.restrict (Icc (0 : ℝ) 1)
  change f =ᵐ[ν] 0
  have hf1 : Integrable f ν := hf.integrable (by norm_num)
  have hmem : ∀ᵐ x ∂ν, x ∈ Icc (0 : ℝ) 1 := by
    simpa only [ν] using
      (ae_restrict_mem (μ := μ) measurableSet_Icc)
  have hint : ∀ n : ℕ, Integrable (fun x => x ^ n * f x) ν := by
    intro n
    apply hf1.bdd_mul
    · exact (continuous_id.pow n).aestronglyMeasurable
    · filter_upwards [hmem] with x hx
      rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg hx.1]
      exact pow_le_one₀ hx.1 hx.2
  have hpoly : ∀ p : Polynomial ℝ,
      ∫ x, Polynomial.eval x p * f x ∂ν = 0 := by
    intro p
    simpa only [ν] using orthogonal_to_polynomials hint horth p
  have hbcf : ∀ g : (ℝ →ᵇ ℝ), ∫ x, g x * f x ∂ν = 0 := by
    intro g
    apply norm_eq_zero.mp
    apply le_antisymm
    · refine le_of_forall_pos_le_add ?_
      intro ε hε
      rw [zero_add]
      let C := ∫ x, |f x| ∂ν
      have hC : 0 ≤ C := integral_nonneg (fun _ => abs_nonneg _)
      let δ := ε / (C + 1)
      have hδ : 0 < δ := div_pos hε (by linarith)
      obtain ⟨p, hp⟩ :=
        exists_polynomial_near_continuousMap 0 1
          (g.toContinuousMap.restrict (Icc (0 : ℝ) 1)) δ hδ
      have hclose : ∀ᵐ x ∂ν, ‖g x - Polynomial.eval x p‖ ≤ δ := by
        filter_upwards [hmem] with x hx
        let y : Icc (0 : ℝ) 1 := ⟨x, hx⟩
        have hpoint := ContinuousMap.norm_coe_le_norm
          (p.toContinuousMapOn (Icc (0 : ℝ) 1) -
            g.toContinuousMap.restrict (Icc (0 : ℝ) 1)) y
        calc
          ‖g x - Polynomial.eval x p‖ =
              ‖(p.toContinuousMapOn (Icc (0 : ℝ) 1) -
                g.toContinuousMap.restrict (Icc (0 : ℝ) 1)) y‖ := by
                  simp only [ContinuousMap.sub_apply, Polynomial.toContinuousMapOn_apply,
                    ContinuousMap.restrict_apply, y]
                  rw [norm_sub_rev]
                  rw [Polynomial.toContinuousMap_apply]
                  rfl
          _ ≤ ‖p.toContinuousMapOn (Icc (0 : ℝ) 1) -
                g.toContinuousMap.restrict (Icc (0 : ℝ) 1)‖ := hpoint
          _ ≤ δ := hp.le
      have hdiff_int :
          Integrable (fun x => (g x - Polynomial.eval x p) * f x) ν := by
        apply hf1.bdd_mul
        · exact (g.continuous.sub p.toContinuousMap.continuous).aestronglyMeasurable
        · exact hclose
      have hp_int : Integrable (fun x => Polynomial.eval x p * f x) ν := by
        apply hf1.bdd_mul
        · exact p.toContinuousMap.continuous.aestronglyMeasurable
        · filter_upwards [hmem] with x hx
          exact p.toContinuousMapOn (Icc (0 : ℝ) 1) |>.norm_coe_le_norm ⟨x, hx⟩
      have hintegral :
          ∫ x, g x * f x ∂ν =
            ∫ x, (g x - Polynomial.eval x p) * f x ∂ν := by
        calc
          (∫ x, g x * f x ∂ν) =
              ∫ x, ((g x - Polynomial.eval x p) * f x +
                Polynomial.eval x p * f x) ∂ν := by
                  apply integral_congr_ae
                  filter_upwards with x
                  ring
          _ = (∫ x, (g x - Polynomial.eval x p) * f x ∂ν) +
                ∫ x, Polynomial.eval x p * f x ∂ν :=
                  integral_add hdiff_int hp_int
          _ = ∫ x, (g x - Polynomial.eval x p) * f x ∂ν := by
                rw [hpoly p, add_zero]
      rw [hintegral]
      have hbound :
          ∀ᵐ x ∂ν, ‖(g x - Polynomial.eval x p) * f x‖ ≤ δ * |f x| := by
        filter_upwards [hclose] with x hx
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
      calc
        ‖∫ x, (g x - Polynomial.eval x p) * f x ∂ν‖
            ≤ ∫ x, δ * |f x| ∂ν :=
              norm_integral_le_of_norm_le (hf1.abs.const_mul δ) hbound
        _ = δ * C := by rw [integral_const_mul]
        _ ≤ ε := by
          have hden : 0 < C + 1 := by linarith
          calc
            δ * C ≤ δ * (C + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) hδ.le
            _ = ε := by
              dsimp only [δ]
              exact div_mul_cancel₀ ε hden.ne'
    · exact norm_nonneg _
  let F : Lp ℝ 2 ν := hf.toLp f
  have hF : F = 0 := by
    apply (BoundedContinuousFunction.toLp_denseRange ℝ ν ℝ (by norm_num)).eq_zero_of_inner_right ℝ
    intro g
    rw [L2.inner_def]
    trans ∫ x, g x * f x ∂ν
    · apply integral_congr_ae
      filter_upwards [g.coeFn_toLp 2 ν ℝ, hf.coeFn_toLp] with x hgx hfx
      rw [hgx, hfx]
      rw [show g x = g x • (1 : ℝ) by simp,
        show f x = f x • (1 : ℝ) by simp]
      rw [real_inner_smul_left, real_inner_smul_right]
      simp
    · exact hbcf g
  have hzero : (F : ℝ → ℝ) =ᵐ[ν] 0 := by
    rw [hF]
    exact Lp.coeFn_zero ℝ 2 ν
  exact hf.coeFn_toLp.symm.trans hzero

end ApmCanaries.A94A04
