import Mathlib
import ConstructionTargets.CircleParam

open Complex Polynomial MeasureTheory Real Set

noncomputable section

variable (R : ℝ) (hR : 0 < R)

/-- The polynomial p(z) = ∏(z - z_k). -/
def apm_a97A07_p (zs : Fin n → ℂ) : Polynomial ℂ :=
  ∏ k, (Polynomial.X - Polynomial.C (zs k))

@[simp] lemma apm_a97A07_p_eval_zs (zs : Fin n → ℂ) (k : Fin n) :
    (apm_a97A07_p zs).eval (zs k) = 0 := by
  simp only [apm_a97A07_p, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ k) (sub_self _)

/-- The divided-difference kernel Q(ζ, z) = (p(ζ) - p(z))/(ζ - z),
    which is polynomial in z of degree n - 1. -/
def apm_a97A07_Q (zs : Fin n → ℂ) (ζ z : ℂ) : ℂ :=
  if z = ζ then (Polynomial.derivative (apm_a97A07_p zs)).aeval ζ
  else ((apm_a97A07_p zs).aeval ζ - (apm_a97A07_p zs).aeval z) / (ζ - z)

/-- At an interpolation node, the divided difference cancels to the Cauchy
kernel numerator. -/
lemma apm_a97A07_Q_eval_zs (zs : Fin n → ℂ) (k : Fin n) (zeta : ℂ)
    (hzeta : zeta ≠ zs k) :
    apm_a97A07_Q zs zeta (zs k) =
      (apm_a97A07_p zs).aeval zeta / (zeta - zs k) := by
  have hk : (apm_a97A07_p zs).aeval (zs k) = 0 := by
    simpa [Polynomial.aeval_def] using apm_a97A07_p_eval_zs zs k
  rw [apm_a97A07_Q, if_neg hzeta.symm, hk, sub_zero]

/-- The Hermite contour-integral interpolant. -/
def apm_a97A07_P (n : ℕ) (zs : Fin n → ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ) (z : ℂ) : ℂ :=
  (1 / (2 * π * I)) • ∫ t in (0 : ℝ)..1,
    ((f (γ t) / (apm_a97A07_p zs).aeval (γ t)) * apm_a97A07_Q zs (γ t) z) * deriv γ t

/-- Helper: Q(ζ, z) is a polynomial in z of degree at most n - 1. -/
theorem apm_a97A07_Q_polynomial_in_z
    (n : ℕ) (hn : 0 < n) (zs : Fin n → ℂ) (ζ : ℂ) :
    ∃ q : Polynomial ℂ, q.natDegree ≤ n - 1 ∧
      ∀ z : ℂ, z ≠ ζ → q.aeval z = apm_a97A07_Q zs ζ z := by
  let p := apm_a97A07_p zs
  let q := (p - Polynomial.C (p.eval ζ)) /ₘ
    (Polynomial.X - Polynomial.C ζ)
  refine ⟨q, ?_, ?_⟩
  · rw [show q.natDegree =
        (p - Polynomial.C (p.eval ζ)).natDegree - 1 by
      simpa [q] using
        Polynomial.natDegree_divByMonic
          (p - Polynomial.C (p.eval ζ))
          (Polynomial.monic_X_sub_C ζ)]
    apply Nat.sub_le_sub_right
    calc
      (p - Polynomial.C (p.eval ζ)).natDegree
          ≤ max p.natDegree (Polynomial.C (p.eval ζ)).natDegree :=
        Polynomial.natDegree_sub_le _ _
      _ ≤ n := by
        simp [p, apm_a97A07_p]
  · intro z hz
    have hroot :
        Polynomial.IsRoot (p - Polynomial.C (p.eval ζ)) ζ := by
      simp [Polynomial.IsRoot]
    have hmul :
        (Polynomial.X - Polynomial.C ζ) * q =
          p - Polynomial.C (p.eval ζ) := by
      simpa [q] using
        (Polynomial.mul_divByMonic_eq_iff_isRoot
          (p := p - Polynomial.C (p.eval ζ)) (a := ζ)).2 hroot
    have heval := congrArg (fun r : Polynomial ℂ => r.eval z) hmul
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at heval
    change q.eval z = apm_a97A07_Q zs ζ z
    rw [apm_a97A07_Q, if_neg hz]
    change q.eval z = (p.eval ζ - p.eval z) / (ζ - z)
    apply (eq_div_iff (sub_ne_zero.mpr hz.symm)).2
    linear_combination -heval

/-- P is a polynomial of degree at most n - 1. -/
theorem apm_a97A07_P_polynomial
    (n : ℕ) (hn : 0 < n)
    (zs : Fin n → ℂ) (zs_distinct : Function.Injective zs)
    (f : ℂ → ℂ) (hf : AnalyticOn ℂ f univ) -- simplified: entire
    (R : ℝ) (hR : 0 < R) (hzs_in : ∀ k, ‖zs k‖ < R) :
    ∃ P_poly : Polynomial ℂ,
      P_poly.natDegree ≤ n - 1 ∧
      ∀ z : ℂ, apm_a97A07_P n zs f (fun t => R * Complex.exp (2 * π * I * t)) z =
        P_poly.aeval z := by
  /-
  Remaining construction: use the quotient polynomial from
  `apm_a97A07_Q_polynomial_in_z`, expand it in the monomial basis of degrees
  `< n`, and integrate its finitely many coefficient functions.  The contour
  stays away from every root by `hzs_in`, so those coefficient functions are
  continuous and interval-integrable.
  -/
  sorry

/-- Interpolation property: P(z_k) = f(z_k) for each k.
    Uses Cauchy's integral formula. -/
theorem apm_a97A07_interpolates
    (n : ℕ) (hn : 0 < n)
    (zs : Fin n → ℂ) (zs_distinct : Function.Injective zs)
    (f : ℂ → ℂ) (hf : AnalyticOn ℂ f univ)
    (R : ℝ) (hR : 0 < R) (hzs_in : ∀ k, ‖zs k‖ < R)
    (k : Fin n) :
    apm_a97A07_P n zs f (fun t => R * Complex.exp (2 * π * I * t)) (zs k) = f (zs k) := by
  let gamma : ℝ → ℂ := fun t ↦ R * Complex.exp (2 * π * I * t)
  let g : ℂ → ℂ := fun z ↦ (z - zs k)⁻¹ * f z
  have hw : zs k ∈ Metric.ball (0 : ℂ) R := by
    simpa [Metric.mem_ball, dist_zero_right] using hzs_in k
  have hcircle_ne_node : ∀ z ∈ Metric.sphere (0 : ℂ) |R|, ∀ j, z ≠ zs j := by
    intro z hz j hEq
    have hz_norm : ‖z‖ = |R| := by
      simpa [Metric.mem_sphere, dist_zero_right] using hz
    have hk_norm : ‖zs j‖ < R := hzs_in j
    rw [hEq] at hz_norm
    rw [abs_of_pos hR] at hz_norm
    linarith
  have hg_cont : ContinuousOn g (Metric.sphere (0 : ℂ) |R|) := by
    apply ContinuousOn.mul
    · exact (continuousOn_id.sub continuousOn_const).inv₀ fun z hz ↦
        sub_ne_zero.mpr (hcircle_ne_node z hz k)
    · exact hf.continuousOn.mono (by simp)
  have hp_gamma_ne : ∀ t : ℝ, (apm_a97A07_p zs).aeval (gamma t) ≠ 0 := by
    intro t
    simp only [apm_a97A07_p, map_prod, map_sub, aeval_X, aeval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply sub_ne_zero.mpr
    apply hcircle_ne_node (gamma t) _ j
    rw [show gamma t = circleMap 0 R (2 * π * t) by
      simp only [gamma, circleMap, zero_add]
      congr 2
      norm_num
      ring]
    exact circleMap_mem_sphere' 0 R (2 * π * t)
  have hintegral :
      (∫ t in (0 : ℝ)..1,
          ((f (gamma t) / (apm_a97A07_p zs).aeval (gamma t)) *
              apm_a97A07_Q zs (gamma t) (zs k)) * deriv gamma t) =
        ∫ t in (0 : ℝ)..1, g (gamma t) * deriv gamma t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hgamma_sphere : gamma t ∈ Metric.sphere (0 : ℂ) |R| := by
      rw [show gamma t = circleMap 0 R (2 * π * t) by
        simp only [gamma, circleMap, zero_add]
        congr 2
        norm_num
        ring]
      exact circleMap_mem_sphere' 0 R (2 * π * t)
    change
      (f (gamma t) / (apm_a97A07_p zs).aeval (gamma t) *
          apm_a97A07_Q zs (gamma t) (zs k)) * deriv gamma t =
        g (gamma t) * deriv gamma t
    rw [apm_a97A07_Q_eval_zs zs k (gamma t)
      (hcircle_ne_node (gamma t) hgamma_sphere k)]
    dsimp [g]
    have hp_eval_ne : (apm_a97A07_p zs).eval (gamma t) ≠ 0 := by
      simpa [Polynomial.aeval_def] using hp_gamma_ne t
    have hnode_ne : gamma t - zs k ≠ 0 :=
      sub_ne_zero.mpr (hcircle_ne_node (gamma t) hgamma_sphere k)
    field_simp [hp_eval_ne, hnode_ne]
  rw [apm_a97A07_P, show (fun t : ℝ ↦ R * Complex.exp (2 * π * I * t)) = gamma by rfl,
    hintegral]
  rw [ConstructionTargets.CircleParam.unitParam_eq_circleIntegral R g hg_cont]
  have hdiff : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) R) :=
    hf.differentiableOn.mono (by simp)
  have hcauchy := hdiff.circleIntegral_sub_inv_smul hw
  change (∮ z in C(0, R), (z - zs k)⁻¹ * f z) = (2 * π * I) * f (zs k) at hcauchy
  rw [hcauchy]
  have htwo_pi_I : (2 * (π : ℂ) * I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  change (1 / (2 * (π : ℂ) * I)) * ((2 * (π : ℂ) * I) * f (zs k)) = f (zs k)
  rw [one_div]
  exact inv_mul_cancel_left₀ htwo_pi_I _

/-- Main theorem: P is a polynomial of degree ≤ n - 1 and interpolates f
    at z_1, ..., z_n. (Using a circle of radius R as the Jordan curve
    enclosing all the z_k.) -/
theorem apm_a97A07_main
    (n : ℕ) (hn : 0 < n)
    (zs : Fin n → ℂ) (zs_distinct : Function.Injective zs)
    (f : ℂ → ℂ) (hf : AnalyticOn ℂ f univ)
    (R : ℝ) (hR : 0 < R) (hzs_in : ∀ k, ‖zs k‖ < R) :
    ∃ P_poly : Polynomial ℂ,
      P_poly.natDegree ≤ n - 1 ∧
      (∀ z : ℂ, apm_a97A07_P n zs f (fun t => R * Complex.exp (2 * π * I * t)) z =
        P_poly.aeval z) ∧
      (∀ k : Fin n, P_poly.aeval (zs k) = f (zs k)) := by
  rcases apm_a97A07_P_polynomial n hn zs zs_distinct f hf R hR hzs_in with
    ⟨P_poly, hdeg, hP⟩
  refine ⟨P_poly, hdeg, hP, ?_⟩
  intro k
  rw [← hP (zs k)]
  exact apm_a97A07_interpolates n hn zs zs_distinct f hf R hR hzs_in k
