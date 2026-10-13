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

/-! ## Definition of the missing source hypothesis -/

/-- `f` has a simple pole at `1` and no other singular part: off `1` it is a
nonzero scalar multiple of `(z - 1)⁻¹` plus an entire function. -/
def apm_a96A06_HasSimplePoleAtOne (f : ℂ → ℂ) : Prop :=
  ∃ c : ℂ, ∃ g : ℂ → ℂ, c ≠ 0 ∧ Differentiable ℂ g ∧
    ∀ z : ℂ, z ≠ 1 → f z = c / (z - 1) + g z

/-! ## Remaining bridges -/

theorem apm_a96A06_pole_coefficient_eq_neg_one
    {f g : ℂ → ℂ} {c : ℂ}
    (hg : Differentiable ℂ g)
    (hrep : ∀ z : ℂ, z ≠ 1 → f z = c / (z - 1) + g z)
    (hf_int : ∮ z in C(0, 2), f z = -(2 * Real.pi * I)) :
    c = -1 := by
  have hone : (1 : ℂ) ∈ ball 0 2 := by
    simp [mem_ball]
  have hnot : (1 : ℂ) ∉ sphere 0 |(2 : ℝ)| := by
    simp [mem_sphere]
  have hinv : CircleIntegrable (fun z : ℂ ↦ (z - 1)⁻¹) 0 2 := by
    rw [circleIntegrable_sub_inv_iff]
    exact Or.inr hnot
  have hgint : CircleIntegrable g 0 2 :=
    hg.continuous.continuousOn.circleIntegrable'
  have hcongr : (∮ z in C(0, 2), f z) =
      ∮ z in C(0, 2), c * (z - 1)⁻¹ + g z := by
    apply circleIntegral.integral_congr (by norm_num)
    intro z hz
    rw [hrep z]
    · simp [div_eq_mul_inv]
    · intro h
      subst z
      simpa [mem_sphere] using hz
  have hgzero : (∮ z in C(0, 2), g z) = 0 := by
    exact hg.diffContOnCl.circleIntegral_eq_zero (by norm_num)
  have hpole : (∮ z in C(0, 2), (z - 1)⁻¹) = 2 * Real.pi * I :=
    circleIntegral.integral_sub_inv_of_mem_ball hone
  have hcinv : CircleIntegrable (fun z : ℂ ↦ c * (z - 1)⁻¹) 0 2 := by
    exact CircleIntegrable.const_smul (a := c) hinv
  rw [hcongr, circleIntegral.integral_add hcinv hgint,
    circleIntegral.integral_const_mul, hpole, hgzero, add_zero] at hf_int
  have hfac : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  apply (mul_right_cancel₀ hfac)
  simpa [mul_assoc] using hf_int

-- BEGIN SEAT AREA
theorem apm_a96A06_coeffs_tendsto_of_representation
    {f g : ℂ → ℂ} {c : ℂ}
    (hg : Differentiable ℂ g) (hc : c = -1)
    (hrep : ∀ z : ℂ, z ≠ 1 → f z = c / (z - 1) + g z) :
    Tendsto (fun n => iteratedDeriv n f 0 / (n.factorial : ℂ))
      atTop (𝓝 1) := by
  subst c
  have hlocal : f =ᶠ[𝓝 0] fun z : ℂ ↦ (1 - z)⁻¹ + g z := by
    filter_upwards [eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num)] with z hz
    rw [hrep z hz]
    congr 1
    field_simp [sub_ne_zero.mpr hz, sub_ne_zero.mpr hz.symm]
    ring
  have hcoeff (n : ℕ) :
      iteratedDeriv n f 0 / (n.factorial : ℂ) =
        1 + iteratedDeriv n g 0 / (n.factorial : ℂ) := by
    rw [hlocal.iteratedDeriv_eq n]
    have hgeom : ContDiffAt ℂ n (fun z : ℂ ↦ (1 - z)⁻¹) 0 := by
      exact (contDiffAt_const.sub contDiffAt_id).inv (by norm_num)
    have hg' : ContDiffAt ℂ n g 0 := hg.contDiff.contDiffAt
    change iteratedDeriv n ((fun z : ℂ ↦ (1 - z)⁻¹) + g) 0 /
      (n.factorial : ℂ) = _
    rw [iteratedDeriv_add hgeom hg', add_div, geom_taylor_coeff]
  have ht : Tendsto
      (fun n : ℕ ↦ (1 : ℂ) + iteratedDeriv n g 0 / (n.factorial : ℂ))
      atTop (𝓝 ((1 : ℂ) + 0)) :=
    tendsto_const_nhds.add (entire_coeffs_tendsto_zero g hg)
  simpa only [hcoeff, add_zero] using ht
-- END SEAT AREA

/-- **Main theorem**: f^(n)(0)/n! → 1.

    f is holomorphic on ℂ \ {1} with ∮_{|z|=2} f(z)dz = -2πi.
    The simple pole at z = 1 has residue -1 (from the contour integral),
    so f(z) = 1/(1-z) + g(z) with g entire.
    Taylor coefficients: f^(n)(0)/n! = 1 + g^(n)(0)/n! → 1.

    The simple-pole hypothesis supplies the entire remainder explicitly. -/
theorem apm_a96a06
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f ({(1 : ℂ)}ᶜ))
    (hf_pole : apm_a96A06_HasSimplePoleAtOne f)
    (hf_int : ∮ z in C(0, 2), f z = -(2 * Real.pi * I)) :
    Tendsto (fun n => iteratedDeriv n f 0 / (n.factorial : ℂ))
      atTop (𝓝 1) := by
  obtain ⟨c, g, hc0, hg, hrep⟩ := hf_pole
  have hc : c = -1 :=
    apm_a96A06_pole_coefficient_eq_neg_one hg hrep hf_int
  exact apm_a96A06_coeffs_tendsto_of_representation hg hc hrep

#print axioms apm_a96a06
end
