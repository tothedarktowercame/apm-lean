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

/-- An explicit polynomial form of the divided difference.  The geometric-sum
formula makes its dependence on the first variable manifestly continuous. -/
def apm_a97A07_divDiffPoly (p : Polynomial ℂ) (ζ : ℂ) : Polynomial ℂ :=
  p.sum fun j a ↦ ∑ i ∈ Finset.range j,
    Polynomial.C (a * ζ ^ (j - 1 - i)) * Polynomial.X ^ i

@[simp] lemma apm_a97A07_divDiffPoly_eval (p : Polynomial ℂ) (ζ z : ℂ) :
    (apm_a97A07_divDiffPoly p ζ).eval z =
      if z = ζ then p.derivative.eval ζ
      else (p.eval ζ - p.eval z) / (ζ - z) := by
  classical
  by_cases hz : z = ζ
  · subst z
    simp only [apm_a97A07_divDiffPoly, Polynomial.eval_sum,
      Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, if_pos]
    rw [Polynomial.derivative_eval]
    simp only [Polynomial.sum_def]
    apply Finset.sum_congr rfl
    intro j hj
    calc
      ∑ x ∈ Finset.range j, p.coeff j * ζ ^ (j - 1 - x) * ζ ^ x =
          p.coeff j * ∑ x ∈ Finset.range j, ζ ^ x * ζ ^ (j - 1 - x) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = p.coeff j * (j : ℂ) * ζ ^ (j - 1) := by
        rw [geom_sum₂_self]
        ring
  · rw [if_neg hz]
    simp only [apm_a97A07_divDiffPoly, Polynomial.eval_sum,
      Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
    apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm hz))).2
    simp only [Polynomial.sum_def]
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hgeom := (Commute.all z ζ).geom_sum₂ hz j
    calc
      (∑ x ∈ Finset.range j, p.coeff j * ζ ^ (j - 1 - x) * z ^ x) * (ζ - z) =
          (p.coeff j * ∑ x ∈ Finset.range j, z ^ x * ζ ^ (j - 1 - x)) *
            (ζ - z) := by
            congr 2
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = p.coeff j * ζ ^ j - p.coeff j * z ^ j := by
        rw [hgeom]
        field_simp [sub_ne_zero.mpr hz]
        ring

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
  classical
  let p := apm_a97A07_p zs
  let γ : ℝ → ℂ := fun t ↦ R * Complex.exp (2 * π * I * t)
  let φ : ℝ → ℝ := fun t ↦ 2 * π * t
  let D : ℝ → ℂ := fun t ↦
    (2 * π : ℝ) • (circleMap 0 R (2 * π * t) * I)
  have hγcircle : ∀ t, γ t = circleMap 0 R (φ t) := by
    intro t
    simp only [γ, φ, circleMap, zero_add]
    congr 2
    norm_num
    ring
  have hφ : ∀ t : ℝ, HasDerivAt φ (2 * π) t := by
    intro t
    simpa [φ] using (hasDerivAt_id t).const_mul (2 * π)
  have hderiv : ∀ t, deriv γ t = D t := by
    intro t
    have hfun : γ = circleMap 0 R ∘ φ := by
      funext u
      exact hγcircle u
    rw [hfun]
    exact (((hasDerivAt_circleMap 0 R (φ t)).scomp t (hφ t)).deriv)
  have hp_ne : ∀ t, p.eval (γ t) ≠ 0 := by
    intro t
    simp only [p, apm_a97A07_p, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    apply sub_ne_zero.mpr
    intro heq
    have hnorm : ‖γ t‖ = R := by
      rw [hγcircle]
      simpa [φ, abs_of_pos hR] using norm_circleMap_zero R (φ t)
    rw [heq] at hnorm
    linarith [hzs_in k]
  have hfcont : Continuous f := by
    simpa only [continuousOn_univ] using hf.continuousOn
  let c : ℕ → ℕ → ℝ → ℂ := fun j i t ↦
    ((f (γ t) / p.eval (γ t)) *
      (p.coeff j * (γ t) ^ (j - 1 - i))) * D t
  have hccont : ∀ j i, Continuous (c j i) := by
    intro j i
    dsimp only [c, D]
    fun_prop (disch := aesop)
  have hcint : ∀ j i, IntervalIntegrable (c j i) volume 0 1 := by
    intro j i
    exact (hccont j i).intervalIntegrable 0 1
  let scalar : ℂ := 1 / (2 * π * I)
  let P_poly : Polynomial ℂ :=
    ∑ j ∈ p.support, ∑ i ∈ Finset.range j,
      Polynomial.C (scalar * ∫ t in (0 : ℝ)..1, c j i t) * Polynomial.X ^ i
  have hpdeg : p.natDegree ≤ n := by
    simp [p, apm_a97A07_p]
  refine ⟨P_poly, ?_, ?_⟩
  · dsimp only [P_poly]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans <| by
      have hij : i < j := Finset.mem_range.mp hi
      have hjdeg : j ≤ p.natDegree := Polynomial.le_natDegree_of_mem_supp j hj
      omega
  · intro z
    have hQ : ∀ t, apm_a97A07_Q zs (γ t) z =
        (apm_a97A07_divDiffPoly p (γ t)).eval z := by
      intro t
      change (if z = γ t then p.derivative.aeval (γ t)
        else (p.aeval (γ t) - p.aeval z) / (γ t - z)) = _
      rw [apm_a97A07_divDiffPoly_eval]
      simp only [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      simp
    have hintegrand : ∀ t,
        ((f (γ t) / p.eval (γ t)) * apm_a97A07_Q zs (γ t) z) * deriv γ t =
          ∑ j ∈ p.support, ∑ i ∈ Finset.range j, c j i t * z ^ i := by
      intro t
      rw [hQ t, hderiv t]
      simp only [apm_a97A07_divDiffPoly, Polynomial.eval_finset_sum,
        Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.sum_def]
      dsimp only [c]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    change scalar • (∫ t in (0 : ℝ)..1,
      ((f (γ t) / p.eval (γ t)) * apm_a97A07_Q zs (γ t) z) * deriv γ t) =
        P_poly.aeval z
    rw [intervalIntegral.integral_congr (fun t ht ↦ hintegrand t)]
    have houter :
        (∫ t in (0 : ℝ)..1, ∑ j ∈ p.support,
          ∑ i ∈ Finset.range j, c j i t * z ^ i) =
        ∑ j ∈ p.support, ∫ t in (0 : ℝ)..1,
          ∑ i ∈ Finset.range j, c j i t * z ^ i := by
      apply intervalIntegral.integral_finset_sum
      intro j hj
      rw [show (fun t ↦ ∑ i ∈ Finset.range j, c j i t * z ^ i) =
          ∑ i ∈ Finset.range j, fun t ↦ c j i t * z ^ i by
        funext t
        simp]
      exact IntervalIntegrable.sum (Finset.range j) fun i hi ↦
        (hcint j i).mul_const (z ^ i)
    rw [houter]
    simp_rw [intervalIntegral.integral_finset_sum (fun i hi ↦
      (hcint _ i).mul_const (z ^ i))]
    rw [show P_poly.aeval z = P_poly.eval z by
      simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]]
    simp only [P_poly, Polynomial.eval_finset_sum,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      smul_eq_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    have hmul : (∫ x in (0 : ℝ)..1, c j i x * z ^ i) =
        (∫ x in (0 : ℝ)..1, c j i x) * z ^ i :=
      intervalIntegral.integral_mul_const (z ^ i) (c j i)
    rw [hmul]
    rw [mul_assoc]

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
