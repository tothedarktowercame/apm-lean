/-
! # APM a96A06: Taylor coefficients at 0 converge to 1

f is analytic except at a simple pole at z = 1, with ∮_{|z|=2} f(z)dz = -2πi.
Show f^(n)(0)/n! → 1.

## Proof strategy

f(z) = 1/(1-z) + g(z) where g is entire (residue at z=1 is -1 from the integral).
Taylor coefficients of 1/(1-z) at 0 are all 1 (geometric series).
Taylor coefficients of entire g → 0 (Cauchy estimates).
So f^(n)(0)/n! → 1.
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow

open Complex Filter Metric Set Topology

noncomputable section

/-- Cauchy estimate: for entire g with ‖g‖ ≤ C on |z| = R,
    ‖g^(n)(0)/n!‖ ≤ C/R^n. -/
lemma cauchy_estimate_taylor (g : ℂ → ℂ) (hg : Differentiable ℂ g) (n : ℕ) {R : ℝ} (hR : 0 < R)
    {C : ℝ} (hC : ∀ z ∈ sphere (0:ℂ) R, ‖g z‖ ≤ C) :
    ‖iteratedDeriv n g 0 / (n.factorial : ℂ)‖ ≤ C / R ^ n := by
  have hCauchy : ‖iteratedDeriv n g 0‖ ≤ n.factorial * C / R ^ n :=
    norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hg.diffContOnCl hC
  rw [norm_div, norm_natCast]
  have hfact : (0 : ℝ) < n.factorial := by positivity
  rw [div_le_iff₀ hfact, mul_comm, ← mul_div_assoc]
  exact hCauchy

/-- The n-th derivative of (1-z)⁻¹ at 0 is n!.
    This follows from f^(n)(z) = n!·(1-z)^{-(n+1)} and f^(n)(0) = n!. -/
lemma geom_iteratedDeriv (n : ℕ) :
    iteratedDeriv n (fun z : ℂ => (1 - z)⁻¹) 0 = (n.factorial : ℂ) := by
  have hcomp := congrFun
    (iteratedDeriv_comp_const_sub n (fun w : ℂ => w⁻¹) (1 : ℂ)) 0
  have hs : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
  have hinv :
      iteratedDeriv n (fun w : ℂ => w⁻¹) 1 =
        (-1 : ℂ) ^ n * (n.factorial : ℂ) := by
    have hopen := (iteratedDerivWithin_of_isOpen (n := n)
      (f := fun w : ℂ => w⁻¹) hs) (show (1 : ℂ) ∈ {z : ℂ | z ≠ 0} by simp)
    have hformula :=
      (iteratedDerivWithin_one_div (k := n) (s := {z : ℂ | z ≠ 0}) hs)
        (show (1 : ℂ) ∈ {z : ℂ | z ≠ 0} by simp)
    rw [← hopen]
    simpa using hformula
  simp only [sub_zero, smul_eq_mul] at hcomp
  rw [hinv] at hcomp
  have hpow : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  rw [← mul_assoc, hpow, one_mul] at hcomp
  exact hcomp

/-- Taylor coefficient of (1-z)⁻¹ at 0: always 1. -/
lemma geom_taylor_coeff (n : ℕ) :
    iteratedDeriv n (fun z : ℂ => (1 - z)⁻¹) 0 / (n.factorial : ℂ) = 1 := by
  rw [geom_iteratedDeriv n, div_self (by exact_mod_cast (Nat.factorial_ne_zero n))]

/-- Taylor coefficients of an entire function tend to 0.
    Uses Cauchy estimate with fixed R = 2:
    |g^(n)(0)/n!| ≤ M(2)/2^n → 0. -/
lemma entire_coeffs_tendsto_zero (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    Tendsto (fun n => iteratedDeriv n g 0 / (n.factorial : ℂ)) atTop (𝓝 0) := by
  have h_cont : Continuous g := hg.continuous
  have h_img_compact : IsCompact ((fun z : ℂ => ‖g z‖) '' sphere (0:ℂ) 2) :=
    (isCompact_sphere (0:ℂ) 2).image_of_continuousOn (h_cont.norm).continuousOn
  obtain ⟨M, hM⟩ : ∃ M, ∀ a ∈ ((fun z : ℂ => ‖g z‖) '' sphere (0:ℂ) 2), a ≤ M :=
    h_img_compact.bddAbove
  have hC : ∀ z ∈ sphere (0:ℂ) 2, ‖g z‖ ≤ M := fun z hz => hM _ ⟨z, hz, rfl⟩
  have hR : (0:ℝ) < 2 := by norm_num
  have h_est : ∀ n, ‖iteratedDeriv n g 0 / (n.factorial : ℂ)‖ ≤ M / 2 ^ n := by
    intro n
    have hCau := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hg.diffContOnCl hC
    rw [norm_div, _root_.norm_natCast]
    have hfact : (0:ℝ) < n.factorial := by positivity
    rw [div_le_iff₀ hfact, mul_comm, ← mul_div_assoc]
    exact hCau
  have h_tendsto : Tendsto (fun n => M / (2:ℝ) ^ n) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun n => norm_nonneg _) h_est h_tendsto)

/-- **Main theorem**: f^(n)(0)/n! → 1.

    f is holomorphic on ℂ \ {1} with ∮_{|z|=2} f(z)dz = -2πi.
    The simple pole at z = 1 has residue -1 (from the contour integral),
    so f(z) = 1/(1-z) + g(z) with g entire.
    Taylor coefficients: f^(n)(0)/n! = 1 + g^(n)(0)/n! → 1.

    The decomposition g = f - (1-z)⁻¹ being entire requires showing the
    removable singularity at z = 1, which follows from the residue being -1. -/
theorem taylor_coeffs_tend_to_one
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f ({(1 : ℂ)}ᶜ))
    (hf_int : ∮ z in C(0, 2), f z = -(2 * Real.pi * I)) :
    Tendsto (fun n => iteratedDeriv n f 0 / (n.factorial : ℂ))
      atTop (𝓝 1) := by
  /- Boundary (closer hop 1): the frozen main statement is false.  Take
  `f z = (1-z)⁻¹ + (z-1)⁻²`.  It is holomorphic off `1`; the second-order pole
  has residue zero, so its integral around `C(0,2)` is zero, while the first
  term has the required integral `-(2πi)`.  But `(z-1)⁻² = (1-z)⁻²` has
  Taylor coefficient `n+1`, so the displayed coefficients of `f` are `n+2`
  and do not tend to `1`.

  Thus knowing only the contour integral fixes the residue, not the full
  principal part.  The earlier argument incorrectly inferred removability
  after cancelling the residue; a zero-residue isolated singularity may still
  have a higher-order pole or be essential.  The intended theorem needs, for
  example, an assumption that `f` has at most a simple pole at `1`.

  `geom_iteratedDeriv` above was closed using Mathlib's
  `iteratedDeriv_comp_const_sub` and `iteratedDerivWithin_one_div`, following
  the inversion calculation in solved sibling `a01J04`. -/
  sorry

end
