import Mathlib
import ConstructionTargets.SchwarzEquality

/-!
# APM a96J06 — a normalized polynomial expands every centered disk

## Statement repairs

None.

## Encoding questions

None. The polynomial is the finite sum printed in the source, with its
coefficient sequence and terminal nonzero coefficient explicit.
-/

noncomputable section

def apm_a96J06_polynomial (N : ℕ) (c : ℕ → ℂ) (z : ℂ) : ℂ :=
  z + ∑ n ∈ Finset.Icc 2 N, c n * z ^ n

def apm_a96J06_poly (N : ℕ) (c : ℕ → ℂ) : Polynomial ℂ :=
  Polynomial.X + ∑ n ∈ Finset.Icc 2 N,
    Polynomial.C (c n) * Polynomial.X ^ n

lemma apm_a96J06_eval_poly (N : ℕ) (c : ℕ → ℂ) (z : ℂ) :
    (apm_a96J06_poly N c).eval z = apm_a96J06_polynomial N c z := by
  simp [apm_a96J06_poly, apm_a96J06_polynomial, Polynomial.eval_finset_sum]

lemma apm_a96J06_coeff_top (N : ℕ) (hN : 2 ≤ N) (c : ℕ → ℂ) :
    (apm_a96J06_poly N c).coeff N = c N := by
  have h1N : 1 ≠ N := by omega
  have hx : (Polynomial.X : Polynomial ℂ).coeff N = 0 := by
    rw [Polynomial.coeff_X]
    simp [h1N]
  simp [apm_a96J06_poly, Polynomial.finset_sum_coeff, hN, hx]

/-- The displayed polynomial has the normalized derivative `1` at zero. -/
lemma apm_a96J06_hasDerivAt_zero (N : ℕ) (c : ℕ → ℂ) :
    HasDerivAt (apm_a96J06_polynomial N c) 1 0 := by
  unfold apm_a96J06_polynomial
  have hsum : HasDerivAt
      (fun z : ℂ => ∑ n ∈ Finset.Icc 2 N, c n * z ^ n) 0 0 := by
    have hterm : ∀ n ∈ Finset.Icc 2 N,
        HasDerivAt (fun z : ℂ => c n * z ^ n) 0 0 := by
      intro n hn
      convert (hasDerivAt_const (x := (0 : ℂ)) (c n)).mul
        ((hasDerivAt_id (𝕜 := ℂ) (0 : ℂ)).pow n) using 1
      · have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
        have hn1 : n - 1 ≠ 0 := by omega
        simp [hn1]
    convert HasDerivAt.sum (u := Finset.Icc 2 N) hterm using 1
    · funext z
      simp [Finset.sum_apply]
    · simp
  simpa using (hasDerivAt_id (𝕜 := ℂ) (0 : ℂ)).add hsum

/-- Rescaling by a positive radius preserves the normalized derivative. -/
lemma apm_a96J06_rescaled_hasDerivAt_zero
    (N : ℕ) (c : ℕ → ℂ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt
      (fun z : ℂ => (r : ℂ)⁻¹ * apm_a96J06_polynomial N c ((r : ℂ) * z))
      1 0 := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hinner : HasDerivAt (fun z : ℂ => (r : ℂ) * z) (r : ℂ) 0 := by
    simpa using (hasDerivAt_const (x := (0 : ℂ)) (r : ℂ)).mul
      (hasDerivAt_id (𝕜 := ℂ) (0 : ℂ))
  have hout : HasDerivAt (apm_a96J06_polynomial N c) 1 ((r : ℂ) * 0) := by
    simpa using apm_a96J06_hasDerivAt_zero N c
  convert (hasDerivAt_const (x := (0 : ℂ)) (r : ℂ)⁻¹).mul
    (HasDerivAt.comp (x := (0 : ℂ)) (h := fun z : ℂ => (r : ℂ) * z)
      hout hinner) using 1 <;>
    simp [hrC]

theorem apm_a96j06
    (N : ℕ) (hN : 2 ≤ N) (c : ℕ → ℂ) (hcN : c N ≠ 0) :
    ∀ r : ℝ, 0 < r →
      ∃ ζ : ℂ, ‖ζ‖ < r ∧ r < ‖apm_a96J06_polynomial N c ζ‖ := by
  intro r hr
  by_contra hcontra
  push_neg at hcontra
  let g : ℂ → ℂ := fun z => (r : ℂ)⁻¹ *
    apm_a96J06_polynomial N c ((r : ℂ) * z)
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hgzero : g 0 = 0 := by
    dsimp [g, apm_a96J06_polynomial]
    simp only [mul_zero, zero_add, mul_eq_zero, inv_eq_zero, hrC, false_or]
    apply Finset.sum_eq_zero
    intro n hn
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    simp [hn0]
  have hgdiff : DifferentiableOn ℂ g (Metric.ball 0 1) := by
    dsimp [g, apm_a96J06_polynomial]
    fun_prop
  have hgmap : Set.MapsTo g (Metric.ball 0 1) (Metric.closedBall (g 0) 1) := by
    intro w hw
    rw [hgzero, Metric.mem_closedBall, dist_zero_right]
    have hwr : ‖(r : ℂ) * w‖ < r := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      have := (Metric.mem_ball.mp hw)
      simp only [dist_zero_right] at this
      nlinarith
    have hpbound := hcontra ((r : ℂ) * w) hwr
    simp only [g, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr]
    rw [inv_mul_le_iff₀ hr]
    simpa using hpbound
  have hgderiv : deriv g 0 = 1 :=
    (apm_a96J06_rescaled_hasDerivAt_zero N c hr).deriv
  have hzero_mem : (0 : ℂ) ∈ Metric.ball 0 1 := Metric.mem_ball_self (by norm_num)
  have haffine := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div
    hgdiff hgmap hzero_mem (by simp [dslope_same, hgderiv])
  have hgeq : ∀ w ∈ Metric.ball (0 : ℂ) 1, g w = w := by
    intro w hw
    simpa [hgzero, hgderiv] using haffine hw
  have heval : ∀ ζ ∈ Metric.ball (0 : ℂ) r,
      (apm_a96J06_poly N c).eval ζ = Polynomial.X.eval ζ := by
    intro ζ hζ
    have hw : (r : ℂ)⁻¹ * ζ ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr]
      rw [inv_mul_lt_one₀ hr]
      simpa [Metric.mem_ball, dist_zero_right] using hζ
    have heq := hgeq ((r : ℂ)⁻¹ * ζ) hw
    dsimp [g] at heq
    rw [← mul_assoc, mul_inv_cancel₀ hrC, one_mul] at heq
    rw [apm_a96J06_eval_poly]
    simp only [Polynomial.eval_X]
    apply (mul_left_cancel₀ hrC)
    simpa [mul_assoc] using congrArg (fun u : ℂ => (r : ℂ) * u) heq
  have hset : Set.Infinite
      {ζ : ℂ | (apm_a96J06_poly N c).eval ζ = Polynomial.X.eval ζ} := by
    let u : ℕ → ℂ := fun n => (r / (n + 2 : ℝ) : ℝ)
    have huinj : Function.Injective u := by
      intro n m hnm
      dsimp [u] at hnm
      push_cast at hnm
      have hnpos : (0 : ℝ) < n + 2 := by positivity
      have hmpos : (0 : ℝ) < m + 2 := by positivity
      have hrne : r ≠ 0 := hr.ne'
      apply Nat.cast_injective (R := ℝ)
      have hinv : ((n : ℝ) + 2)⁻¹ = ((m : ℝ) + 2)⁻¹ := by
        apply mul_left_cancel₀ hrne
        simpa [div_eq_mul_inv] using hnm
      have hden : (n : ℝ) + 2 = (m : ℝ) + 2 := inv_injective hinv
      have hcast : (n : ℝ) = m := by linarith
      exact_mod_cast hcast
    apply (Set.infinite_range_of_injective huinj).mono
    intro ζ hζ
    rcases hζ with ⟨n, rfl⟩
    apply heval
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos hr (by positivity))]
    apply div_lt_self hr
    have hnnonneg : (0 : ℝ) ≤ n := by positivity
    linarith
  have hpoly : apm_a96J06_poly N c = Polynomial.X :=
    Polynomial.eq_of_infinite_eval_eq _ _ hset
  have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff N) hpoly
  change (apm_a96J06_poly N c).coeff N = Polynomial.X.coeff N at hcoeff
  rw [apm_a96J06_coeff_top N hN c] at hcoeff
  have hXN : (Polynomial.X : Polynomial ℂ).coeff N = 0 := by
    have hOne : 1 ≠ N := by omega
    rw [Polynomial.coeff_X]
    simp [hOne]
  exact hcN (hcoeff.trans hXN)
