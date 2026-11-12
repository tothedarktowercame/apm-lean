import ConstructionTargets.SectorCauchy

import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Real Filter Set MeasureTheory Topology Complex
open ConstructionTargets.SectorCauchy
open scoped Interval

noncomputable section

namespace ApmCanaries.A94A06

private lemma sqrt3_sq : (Real.sqrt 3 : ℝ) ^ 2 = 3 := by
  norm_num

/-- The three roots of `1 + z³`, ordered counterclockwise starting in the
upper half-plane. -/
def poleA : ℂ := (1 + Real.sqrt 3 * I) / 2
def poleB : ℂ := -1
def poleC : ℂ := (1 - Real.sqrt 3 * I) / 2

lemma poleA_cube : poleA ^ 3 = -1 := by
  unfold poleA
  push_cast
  have hs : ((Real.sqrt 3 : ℂ) ^ 2) = 3 := by
    exact_mod_cast sqrt3_sq
  have hs3 : ((Real.sqrt 3 : ℂ) ^ 3) = 3 * Real.sqrt 3 := by
    calc
      _ = (Real.sqrt 3 : ℂ) ^ 2 * Real.sqrt 3 := by ring
      _ = _ := by rw [hs]
  field_simp
  ring_nf
  rw [hs, hs3, show I ^ 2 = (-1 : ℂ) by norm_num,
    show I ^ 3 = -I by norm_num]
  ring

lemma poleB_cube : poleB ^ 3 = -1 := by norm_num [poleB]

lemma poleC_cube : poleC ^ 3 = -1 := by
  unfold poleC
  push_cast
  have hs : ((Real.sqrt 3 : ℂ) ^ 2) = 3 := by
    exact_mod_cast sqrt3_sq
  have hs3 : ((Real.sqrt 3 : ℂ) ^ 3) = 3 * Real.sqrt 3 := by
    calc
      _ = (Real.sqrt 3 : ℂ) ^ 2 * Real.sqrt 3 := by ring
      _ = _ := by rw [hs]
  field_simp
  ring_nf
  rw [hs, hs3, show I ^ 2 = (-1 : ℂ) by norm_num,
    show I ^ 3 = -I by norm_num]
  ring

lemma poleA_ne_zero : poleA ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [poleA] at this

lemma poleB_ne_zero : poleB ≠ 0 := by norm_num [poleB]

lemma poleC_ne_zero : poleC ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [poleC] at this

lemma poleA_im_pos : 0 < poleA.im := by
  simp [poleA]

lemma poleA_re_value : poleA.re = 1 / 2 := by
  norm_num [poleA, div_re]

lemma poleA_im_value : poleA.im = Real.sqrt 3 / 2 := by
  norm_num [poleA, div_im]

lemma poleC_im_neg : poleC.im < 0 := by
  simp [poleC]
  have : 0 < Real.sqrt 3 := by positivity
  linarith

lemma cubic_factorization (z : ℂ) :
    1 + z ^ 3 = (z - poleA) * (z - poleB) * (z - poleC) := by
  rw [poleA, poleB, poleC]
  push_cast
  have hs : ((Real.sqrt 3 : ℂ) ^ 2) = 3 := by
    exact_mod_cast sqrt3_sq
  field_simp
  ring_nf
  rw [hs, show I ^ 2 = (-1 : ℂ) by norm_num]
  ring

/-- Partial fractions for the transformed sector integrand. -/
lemma cubic_partial_fractions {z : ℂ}
    (ha : z ≠ poleA) (hb : z ≠ poleB) (hc : z ≠ poleC) :
    z / (1 + z ^ 3) =
      (3 * poleA)⁻¹ * (z - poleA)⁻¹ +
      (3 * poleB)⁻¹ * (z - poleB)⁻¹ +
      (3 * poleC)⁻¹ * (z - poleC)⁻¹ := by
  rw [cubic_factorization]
  have hab : poleA ≠ poleB := by
    intro h
    have := congrArg Complex.im h
    simpa [poleA, poleB] using this
  have hac : poleA ≠ poleC := by
    intro h
    have := congrArg Complex.im h
    simp [poleA, poleC] at this
    have hs : 0 < Real.sqrt 3 := by positivity
    linarith
  have hbc : poleB ≠ poleC := by
    intro h
    have := congrArg Complex.im h
    simp [poleB, poleC] at this
    have hspos : 0 < Real.sqrt 3 := by positivity
    linarith
  have hza : z - poleA ≠ 0 := sub_ne_zero.mpr ha
  have hzb : z - poleB ≠ 0 := sub_ne_zero.mpr hb
  have hzc : z - poleC ≠ 0 := sub_ne_zero.mpr hc
  field_simp [hza, hzb, hzc, poleA_ne_zero, poleB_ne_zero, poleC_ne_zero,
    hab, hac, hbc]
  rw [poleA, poleB, poleC]
  push_cast
  have hs : ((Real.sqrt 3 : ℂ) ^ 2) = 3 := by
    exact_mod_cast sqrt3_sq
  have hs4 : ((Real.sqrt 3 : ℂ) ^ 4) = 9 := by
    calc
      _ = ((Real.sqrt 3 : ℂ) ^ 2) ^ 2 := by ring
      _ = 9 := by rw [hs]; norm_num
  field_simp
  ring_nf
  rw [hs, hs4, show I ^ 2 = (-1 : ℂ) by norm_num,
    show I ^ 4 = (1 : ℂ) by norm_num]
  ring

def sectorBeta : ℝ := π / 3
def sectorAlpha : ℝ := 2 * π / 3

lemma exp_I_real (θ : ℝ) :
    Complex.exp (I * θ) = Real.cos θ + Real.sin θ * I := by
  rw [show I * (θ : ℂ) = (θ : ℂ) * I by ring, Complex.exp_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma exp_I_sectorBeta : Complex.exp (I * sectorBeta) = poleA := by
  rw [exp_I_real, sectorBeta, poleA, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  push_cast
  ring

lemma exp_I_sectorAlpha : Complex.exp (I * sectorAlpha) = -poleC := by
  rw [sectorAlpha, show (2 * π / 3 : ℝ) = π - π / 3 by ring,
    exp_I_real, Real.cos_pi_sub, Real.sin_pi_sub,
    Real.cos_pi_div_three, Real.sin_pi_div_three, poleC]
  push_cast
  ring

lemma cos_ge_half_of_mem_zero_beta {θ : ℝ} (hθ : θ ∈ [[(0 : ℝ), sectorBeta]]) :
    1 / 2 ≤ Real.cos θ := by
  rw [uIcc_of_le (by simp [sectorBeta]; positivity)] at hθ
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hθ.1
    (by dsimp [sectorBeta] at hθ ⊢; nlinarith [Real.pi_pos]) hθ.2
  simpa [sectorBeta, Real.cos_pi_div_three] using hc

lemma sin_ge_sqrt3_div_two_of_mem_beta_alpha {θ : ℝ}
    (hθ : θ ∈ [[sectorBeta, sectorAlpha]]) :
    Real.sqrt 3 / 2 ≤ Real.sin θ := by
  have hba : sectorBeta ≤ sectorAlpha := by
    dsimp [sectorBeta, sectorAlpha]
    nlinarith [Real.pi_pos]
  rw [uIcc_of_le hba] at hθ
  by_cases hmid : θ ≤ π / 2
  · have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
      (x := π / 3) (y := θ)
      (by nlinarith [Real.pi_pos]) hmid (by simpa [sectorBeta] using hθ.1)
    simpa [Real.sin_pi_div_three] using hs
  · have hθpi : π - θ ≤ π / 2 := by linarith
    have hlower : π / 3 ≤ π - θ := by
      dsimp [sectorBeta, sectorAlpha] at hθ
      calc
        π / 3 = π - 2 * π / 3 := by ring
        _ ≤ π - θ := sub_le_sub_left hθ.2 π
    have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
      (x := π / 3) (y := π - θ)
      (by nlinarith [Real.pi_pos]) hθpi hlower
    rw [Real.sin_pi_sub] at hs
    simpa [Real.sin_pi_div_three] using hs

/-- The pole in the transformed sector contributes one unit of winding. -/
lemma poleA_sector_integral (R : ℝ) (hR : 1 < R) :
    sectorBoundaryIntegral (fun z => (z - poleA)⁻¹) R sectorAlpha =
      2 * π * I := by
  apply sectorBoundaryIntegral_sub_inv_eq_two_pi_I_of_split_arc
    R sectorAlpha sectorBeta poleA
  · intro x hx
    rw [Complex.mem_slitPlane_iff]
    right
    have him : ((x : ℂ) - poleA).im = -poleA.im := by simp
    rw [him]
    exact neg_ne_zero.mpr poleA_im_pos.ne'
  · intro θ hθ
    rw [Complex.mem_slitPlane_iff]
    left
    have hre : (R * Complex.exp (I * θ) - poleA).re =
        R * Real.cos θ - 1 / 2 := by
      rw [exp_I_real]
      simp only [sub_re, mul_re, add_re, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, mul_one, zero_mul, add_zero, zero_add, poleA_re_value]
      ring
    rw [hre]
    have hc := cos_ge_half_of_mem_zero_beta hθ
    nlinarith
  · intro θ hθ
    rw [Complex.mem_slitPlane_iff]
    right
    have him : (poleA - R * Complex.exp (I * θ)).im =
        Real.sqrt 3 / 2 - R * Real.sin θ := by
      rw [exp_I_real]
      simp only [sub_im, mul_im, add_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, mul_one, zero_mul, add_zero, zero_add, poleA_im_value]
    rw [him]
    have hs := sin_ge_sqrt3_div_two_of_mem_beta_alpha hθ
    have hsqrt : 0 < Real.sqrt 3 := by positivity
    have : Real.sqrt 3 / 2 - R * Real.sin θ < 0 := by nlinarith
    exact this.ne
  · intro x hx
    rw [Complex.mem_slitPlane_iff]
    left
    rw [exp_I_sectorAlpha]
    have hx0 : 0 ≤ x := by
      rw [uIcc_of_le (by linarith : 0 ≤ R)] at hx
      exact hx.1
    have hre : (poleA - x * -poleC).re = (1 + x) / 2 := by
      norm_num [poleA, poleC, mul_re, div_re]
      ring
    rw [hre]
    linarith
  · exact poleA_im_pos
  · rw [exp_I_sectorBeta]
    have him : (R * poleA - poleA).im = (R - 1) * poleA.im := by
      simp [mul_im]
      ring
    rw [him]
    have := poleA_im_pos
    nlinarith

def poleBHalfPlane : Set ℂ :=
  {z | -(Real.sqrt 3) / 2 < Real.sqrt 3 * z.re + z.im}

lemma poleBHalfPlane_open : IsOpen poleBHalfPlane := by
  exact isOpen_lt continuous_const
    ((continuous_const.mul continuous_re).add continuous_im)

lemma poleBHalfPlane_convex : Convex ℝ poleBHalfPlane := by
  intro x hx y hy a b ha hb hab
  change -(Real.sqrt 3) / 2 < Real.sqrt 3 * x.re + x.im at hx
  change -(Real.sqrt 3) / 2 < Real.sqrt 3 * y.re + y.im at hy
  change -(Real.sqrt 3) / 2 <
    Real.sqrt 3 * (a • x + b • y).re + (a • x + b • y).im
  simp only [add_re, add_im, smul_re, smul_im, smul_eq_mul]
  rcases ha.eq_or_lt with rfl | ha'
  · have hb1 : b = 1 := by linarith
    simpa [hb1] using hy
  · have hax := mul_lt_mul_of_pos_left hx ha'
    have hby := mul_le_mul_of_nonneg_left hy.le hb
    calc
      -(Real.sqrt 3) / 2 =
          (a + b) * (-(Real.sqrt 3) / 2) := by rw [hab, one_mul]
      _ = a * (-(Real.sqrt 3) / 2) + b * (-(Real.sqrt 3) / 2) := by ring
      _ < a * (Real.sqrt 3 * x.re + x.im) +
          b * (Real.sqrt 3 * y.re + y.im) := add_lt_add_of_lt_of_le hax hby
      _ = Real.sqrt 3 * (a * x.re + b * y.re) +
          (a * x.im + b * y.im) := by ring

lemma poleB_not_mem_halfPlane : poleB ∉ poleBHalfPlane := by
  change ¬(-(Real.sqrt 3) / 2 < Real.sqrt 3 * poleB.re + poleB.im)
  simp [poleB]

lemma sector_linear_nonneg {θ : ℝ} (hθ : θ ∈ [[(0 : ℝ), sectorAlpha]]) :
    0 ≤ Real.sqrt 3 * Real.cos θ + Real.sin θ := by
  have hα : 0 ≤ sectorAlpha := by dsimp [sectorAlpha]; positivity
  rw [uIcc_of_le hα] at hθ
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (x := θ + π / 3)
    (add_nonneg hθ.1 (by positivity)) (by
      calc
        θ + π / 3 ≤ sectorAlpha + π / 3 := add_le_add hθ.2 le_rfl
        _ = π := by simp [sectorAlpha]; ring)
  rw [Real.sin_add, Real.sin_pi_div_three, Real.cos_pi_div_three] at hs
  have hsqrt : 0 < Real.sqrt 3 := by positivity
  nlinarith

lemma poleB_sector_integral (R : ℝ) (hR : 0 ≤ R) :
    sectorBoundaryIntegral (fun z => (z - poleB)⁻¹) R sectorAlpha = 0 := by
  apply sectorBoundaryIntegral_eq_zero_of_convex
    (s := poleBHalfPlane) _ _ _ poleBHalfPlane_convex poleBHalfPlane_open
  · intro z hz
    have hne : z - poleB ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      subst z
      exact poleB_not_mem_halfPlane hz
    exact ((differentiableAt_id.sub_const poleB).inv hne).differentiableWithinAt
  · intro x hx
    change -(Real.sqrt 3) / 2 < Real.sqrt 3 * x + 0
    have hx0 : 0 ≤ x := by
      rw [uIcc_of_le hR] at hx
      exact hx.1
    have hs : 0 < Real.sqrt 3 := by positivity
    nlinarith
  · intro θ hθ
    change -(Real.sqrt 3) / 2 <
      Real.sqrt 3 * (R * Complex.exp (I * θ)).re +
        (R * Complex.exp (I * θ)).im
    rw [exp_I_real]
    simp only [mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im,
      I_re, I_im, mul_zero, mul_one, zero_mul, add_zero, zero_add]
    have hlin := sector_linear_nonneg hθ
    have hs : 0 < Real.sqrt 3 := by positivity
    nlinarith
  · intro x hx
    change -(Real.sqrt 3) / 2 <
      Real.sqrt 3 * (x * Complex.exp (I * sectorAlpha)).re +
        (x * Complex.exp (I * sectorAlpha)).im
    have hx0 : 0 ≤ x := by
      rw [uIcc_of_le hR] at hx
      exact hx.1
    rw [exp_I_sectorAlpha]
    have hlin : Real.sqrt 3 * (-poleC).re + (-poleC).im = 0 := by
      norm_num [poleC, div_re, div_im]
      ring
    rw [mul_re, mul_im]
    simp only [ofReal_re, ofReal_im, zero_mul, add_zero]
    calc
      -(Real.sqrt 3) / 2 < 0 := by
        have hs : 0 < Real.sqrt 3 := by positivity
        linarith
      _ = x * (Real.sqrt 3 * (-poleC).re + (-poleC).im) := by rw [hlin, mul_zero]
      _ = Real.sqrt 3 * (x * (-poleC).re - 0) + x * (-poleC).im := by ring

def poleCHalfPlane : Set ℂ := {z | -(Real.sqrt 3) / 4 < z.im}

lemma poleCHalfPlane_open : IsOpen poleCHalfPlane :=
  isOpen_lt continuous_const continuous_im

lemma poleCHalfPlane_convex : Convex ℝ poleCHalfPlane := by
  intro x hx y hy a b ha hb hab
  change -(Real.sqrt 3) / 4 < x.im at hx
  change -(Real.sqrt 3) / 4 < y.im at hy
  change -(Real.sqrt 3) / 4 < (a • x + b • y).im
  simp only [add_im, smul_im, smul_eq_mul]
  rcases ha.eq_or_lt with rfl | ha'
  · have hb1 : b = 1 := by linarith
    simpa [hb1] using hy
  · have hax := mul_lt_mul_of_pos_left hx ha'
    have hby := mul_le_mul_of_nonneg_left hy.le hb
    calc
      -(Real.sqrt 3) / 4 =
          (a + b) * (-(Real.sqrt 3) / 4) := by rw [hab, one_mul]
      _ = a * (-(Real.sqrt 3) / 4) + b * (-(Real.sqrt 3) / 4) := by ring
      _ < a * x.im + b * y.im := add_lt_add_of_lt_of_le hax hby

lemma poleC_not_mem_halfPlane : poleC ∉ poleCHalfPlane := by
  change ¬(-(Real.sqrt 3) / 4 < poleC.im)
  simp [poleC]
  have hs : 0 < Real.sqrt 3 := by positivity
  linarith

lemma sin_nonneg_of_mem_sector {θ : ℝ} (hθ : θ ∈ [[(0 : ℝ), sectorAlpha]]) :
    0 ≤ Real.sin θ := by
  have hα : 0 ≤ sectorAlpha := by dsimp [sectorAlpha]; positivity
  rw [uIcc_of_le hα] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
    (calc
      θ ≤ sectorAlpha := hθ.2
      _ ≤ π := by simp [sectorAlpha]; nlinarith [Real.pi_pos])

lemma poleC_sector_integral (R : ℝ) (hR : 0 ≤ R) :
    sectorBoundaryIntegral (fun z => (z - poleC)⁻¹) R sectorAlpha = 0 := by
  apply sectorBoundaryIntegral_eq_zero_of_convex
    (s := poleCHalfPlane) _ _ _ poleCHalfPlane_convex poleCHalfPlane_open
  · intro z hz
    have hne : z - poleC ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      subst z
      exact poleC_not_mem_halfPlane hz
    exact ((differentiableAt_id.sub_const poleC).inv hne).differentiableWithinAt
  · intro x hx
    change -(Real.sqrt 3) / 4 < (x : ℂ).im
    simp
    have hs : 0 < Real.sqrt 3 := by positivity
    linarith
  · intro θ hθ
    change -(Real.sqrt 3) / 4 < (R * Complex.exp (I * θ)).im
    rw [exp_I_real]
    simp only [mul_im, add_im, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, mul_one, zero_mul, add_zero, zero_add]
    have hs := sin_nonneg_of_mem_sector hθ
    have hsqrt : 0 < Real.sqrt 3 := by positivity
    nlinarith
  · intro x hx
    change -(Real.sqrt 3) / 4 <
      (x * Complex.exp (I * sectorAlpha)).im
    rw [exp_I_sectorAlpha]
    have hx0 : 0 ≤ x := by
      rw [uIcc_of_le hR] at hx
      exact hx.1
    simp [poleC, mul_im]
    have hs : 0 < Real.sqrt 3 := by positivity
    nlinarith

lemma norm_poleA : ‖poleA‖ = 1 := by
  have h := congrArg norm poleA_cube
  rw [norm_pow, norm_neg, norm_one] at h
  apply (pow_left_inj₀ (norm_nonneg poleA) zero_le_one (by norm_num : (3 : ℕ) ≠ 0)).mp
  simpa using h

lemma norm_poleB : ‖poleB‖ = 1 := by simp [poleB]

lemma norm_poleC : ‖poleC‖ = 1 := by
  have h := congrArg norm poleC_cube
  rw [norm_pow, norm_neg, norm_one] at h
  apply (pow_left_inj₀ (norm_nonneg poleC) zero_le_one (by norm_num : (3 : ℕ) ≠ 0)).mp
  simpa using h

lemma lower_ne_pole {p : ℂ} (hp : p ^ 3 = -1)
    {x : ℝ} (hx : 0 ≤ x) : (x : ℂ) ≠ p := by
  intro h
  have hc := congrArg (fun z : ℂ => z ^ 3) h
  change (x : ℂ) ^ 3 = p ^ 3 at hc
  rw [hp] at hc
  have hr : x ^ 3 = -1 := by exact_mod_cast hc
  nlinarith [pow_nonneg hx 3]

lemma arc_ne_pole {p : ℂ} (hp : ‖p‖ = 1)
    {R θ : ℝ} (hR : 1 < R) : R * Complex.exp (I * θ) ≠ p := by
  intro h
  have hn := congrArg norm h
  rw [norm_mul, norm_exp] at hn
  norm_num at hn
  rw [abs_of_pos (lt_trans zero_lt_one hR)] at hn
  linarith

lemma upper_ne_pole {p : ℂ} (hp : p ^ 3 = -1)
    {x : ℝ} (hx : 0 ≤ x) :
    x * Complex.exp (I * sectorAlpha) ≠ p := by
  intro h
  have hc := congrArg (fun z : ℂ => z ^ 3) h
  change ((x : ℂ) * Complex.exp (I * sectorAlpha)) ^ 3 = p ^ 3 at hc
  rw [hp, exp_I_sectorAlpha] at hc
  have hnegc : (-poleC) ^ 3 = 1 := by rw [neg_pow, poleC_cube]; norm_num
  rw [mul_pow, hnegc, mul_one] at hc
  have hr : x ^ 3 = -1 := by exact_mod_cast hc
  nlinarith [pow_nonneg hx 3]

def transformedIntegrand (z : ℂ) : ℂ := z / (1 + z ^ 3)

def transformedPrincipalParts (z : ℂ) : ℂ :=
  (3 * poleA)⁻¹ * (z - poleA)⁻¹ +
    (3 * poleB)⁻¹ * (z - poleB)⁻¹ +
    (3 * poleC)⁻¹ * (z - poleC)⁻¹

lemma transformed_eq_principalParts_on_sector_lower (R : ℝ) (hR : 0 ≤ R)
    {x : ℝ} (hx : x ∈ [[(0 : ℝ), R]]) :
    transformedIntegrand x = transformedPrincipalParts x := by
  have hx0 : 0 ≤ x := (uIcc_of_le hR ▸ hx).1
  exact cubic_partial_fractions
    (lower_ne_pole poleA_cube hx0)
    (lower_ne_pole poleB_cube hx0)
    (lower_ne_pole poleC_cube hx0)

lemma transformed_eq_principalParts_on_sector_arc (R : ℝ) (hR : 1 < R)
    (θ : ℝ) :
    transformedIntegrand (R * Complex.exp (I * θ)) =
      transformedPrincipalParts (R * Complex.exp (I * θ)) :=
  cubic_partial_fractions
    (arc_ne_pole norm_poleA hR)
    (arc_ne_pole norm_poleB hR)
    (arc_ne_pole norm_poleC hR)

lemma transformed_eq_principalParts_on_sector_upper (R : ℝ) (hR : 0 ≤ R)
    {x : ℝ} (hx : x ∈ [[(0 : ℝ), R]]) :
    transformedIntegrand (x * Complex.exp (I * sectorAlpha)) =
      transformedPrincipalParts (x * Complex.exp (I * sectorAlpha)) := by
  have hx0 : 0 ≤ x := (uIcc_of_le hR ▸ hx).1
  exact cubic_partial_fractions
    (upper_ne_pole poleA_cube hx0)
    (upper_ne_pole poleB_cube hx0)
    (upper_ne_pole poleC_cube hx0)

lemma transformed_sector_congr (R : ℝ) (hR : 1 < R) :
    sectorBoundaryIntegral transformedIntegrand R sectorAlpha =
      sectorBoundaryIntegral transformedPrincipalParts R sectorAlpha := by
  apply sectorBoundaryIntegral_congr
  · intro x hx
    exact transformed_eq_principalParts_on_sector_lower R
      (le_trans zero_le_one hR.le) hx
  · intro θ _
    exact transformed_eq_principalParts_on_sector_arc R hR θ
  · intro x hx
    exact transformed_eq_principalParts_on_sector_upper R
      (le_trans zero_le_one hR.le) hx

lemma sub_inv_sectorBoundaryIntegrable {p : ℂ} {R α : ℝ}
    (hlower : ∀ x ∈ [[(0 : ℝ), R]], (x : ℂ) ≠ p)
    (harc : ∀ θ ∈ [[(0 : ℝ), α]],
      R * Complex.exp (I * θ) ≠ p)
    (hupper : ∀ x ∈ [[(0 : ℝ), R]],
      x * Complex.exp (I * α) ≠ p) :
    SectorBoundaryIntegrable (fun z => (z - p)⁻¹) R α := by
  constructor
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
      ((continuous_ofReal.sub continuous_const).continuousOn)
    intro x hx
    exact sub_ne_zero.mpr (hlower x hx)
  constructor
  · apply ContinuousOn.intervalIntegrable
    have hpath : Continuous (fun θ : ℝ =>
        (R : ℂ) * Complex.exp (I * θ)) := by fun_prop
    have hinv : ContinuousOn (fun θ : ℝ =>
        ((R : ℂ) * Complex.exp (I * θ) - p)⁻¹) [[(0 : ℝ), α]] := by
      apply ContinuousOn.inv₀ (hpath.sub continuous_const).continuousOn
      intro θ hθ
      exact sub_ne_zero.mpr (harc θ hθ)
    exact hinv.mul (by fun_prop)
  · apply ContinuousOn.intervalIntegrable
    have hpath : Continuous (fun x : ℝ =>
        (x : ℂ) * Complex.exp (I * α)) := by fun_prop
    apply ContinuousOn.inv₀ (hpath.sub continuous_const).continuousOn
    intro x hx
    exact sub_ne_zero.mpr (hupper x hx)

lemma pole_kernel_integrable {p : ℂ} (hcube : p ^ 3 = -1)
    (hnorm : ‖p‖ = 1) (R : ℝ) (hR : 1 < R) :
    SectorBoundaryIntegrable (fun z => (z - p)⁻¹) R sectorAlpha := by
  apply sub_inv_sectorBoundaryIntegrable
  · intro x hx
    exact lower_ne_pole hcube ((uIcc_of_le (le_trans zero_le_one hR.le) ▸ hx).1)
  · intro θ _
    exact arc_ne_pole hnorm hR
  · intro x hx
    exact upper_ne_pole hcube ((uIcc_of_le (le_trans zero_le_one hR.le) ▸ hx).1)

lemma transformed_sector_value (R : ℝ) (hR : 1 < R) :
    sectorBoundaryIntegral transformedIntegrand R sectorAlpha =
      (3 * poleA)⁻¹ * (2 * π * I) := by
  rw [transformed_sector_congr R hR]
  unfold transformedPrincipalParts
  let fA : ℂ → ℂ := fun z => (z - poleA)⁻¹
  let fB : ℂ → ℂ := fun z => (z - poleB)⁻¹
  let fC : ℂ → ℂ := fun z => (z - poleC)⁻¹
  have hA : SectorBoundaryIntegrable fA R sectorAlpha :=
    pole_kernel_integrable poleA_cube norm_poleA R hR
  have hB : SectorBoundaryIntegrable fB R sectorAlpha :=
    pole_kernel_integrable poleB_cube norm_poleB R hR
  have hC : SectorBoundaryIntegrable fC R sectorAlpha :=
    pole_kernel_integrable poleC_cube norm_poleC R hR
  rw [sectorBoundaryIntegral_add
    ((hA.const_mul _).add (hB.const_mul _)) (hC.const_mul _)]
  rw [sectorBoundaryIntegral_add
    (hA.const_mul _) (hB.const_mul _)]
  rw [sectorBoundaryIntegral_const_mul, sectorBoundaryIntegral_const_mul,
    sectorBoundaryIntegral_const_mul]
  rw [poleA_sector_integral R hR,
    poleB_sector_integral R (le_trans zero_le_one hR.le),
    poleC_sector_integral R (le_trans zero_le_one hR.le)]
  ring

def sectorRoot : ℂ := Complex.exp (I * sectorAlpha)

lemma sectorRoot_eq : sectorRoot = -poleC := exp_I_sectorAlpha

lemma sectorRoot_cube : sectorRoot ^ 3 = 1 := by
  rw [sectorRoot_eq, neg_pow, poleC_cube]
  norm_num

lemma transformed_upper_ray (x : ℝ) :
    transformedIntegrand (x * sectorRoot) * sectorRoot =
      sectorRoot ^ 2 * transformedIntegrand x := by
  unfold transformedIntegrand
  rw [mul_pow, sectorRoot_cube, mul_one]
  ring

def radialIntegral (R : ℝ) : ℂ :=
  ∫ x : ℝ in 0..R, transformedIntegrand x

def sectorArcIntegral (R : ℝ) : ℂ :=
  ∫ θ : ℝ in 0..sectorAlpha,
    transformedIntegrand (R * Complex.exp (I * θ)) *
      (I * R * Complex.exp (I * θ))

lemma transformed_boundary_decomposition (R : ℝ) :
    sectorBoundaryIntegral transformedIntegrand R sectorAlpha =
      (1 - sectorRoot ^ 2) * radialIntegral R + sectorArcIntegral R := by
  have hupper :
      sectorRoot * (∫ x : ℝ in 0..R,
        transformedIntegrand (x * sectorRoot)) =
        sectorRoot ^ 2 * radialIntegral R := by
    calc
      _ = ∫ x : ℝ in 0..R,
          sectorRoot * transformedIntegrand (x * sectorRoot) :=
        (intervalIntegral.integral_const_mul (μ := volume)
          (a := (0 : ℝ)) (b := R) sectorRoot
          (fun x : ℝ => transformedIntegrand (x * sectorRoot))).symm
      _ = ∫ x : ℝ in 0..R,
          sectorRoot ^ 2 * transformedIntegrand x := by
        apply intervalIntegral.integral_congr
        intro x _
        simpa [mul_comm] using transformed_upper_ray x
      _ = _ := by
        exact intervalIntegral.integral_const_mul (μ := volume)
          (a := (0 : ℝ)) (b := R) (sectorRoot ^ 2)
          (fun x : ℝ => transformedIntegrand x)
  simp only [radialIntegral] at hupper
  unfold sectorBoundaryIntegral sectorArcIntegral radialIntegral
  change _ - sectorRoot * (∫ x : ℝ in 0..R,
    transformedIntegrand (x * sectorRoot)) = _
  rw [hupper]
  ring

lemma sectorArcIntegral_norm_le (R : ℝ) (hR : 1 < R) :
    ‖sectorArcIntegral R‖ ≤ sectorAlpha * (R ^ 2 / (R ^ 3 - 1)) := by
  unfold sectorArcIntegral
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := R ^ 2 / (R ^ 3 - 1)) fun θ _ => ?_).trans_eq ?_
  · have hR0 : 0 < R := lt_trans zero_lt_one hR
    have hden : 0 < R ^ 3 - 1 := by nlinarith [one_lt_pow₀ hR (by norm_num : 3 ≠ 0)]
    unfold transformedIntegrand
    simp only [norm_mul, norm_div]
    simp [Complex.norm_exp, Complex.mul_re, abs_of_pos hR0]
    have htriangle : R ^ 3 - 1 ≤ ‖1 + ((R : ℂ) * Complex.exp (I * θ)) ^ 3‖ := by
      have ht := norm_sub_norm_le
        (((R : ℂ) * Complex.exp (I * θ)) ^ 3) (-1 : ℂ)
      calc
        R ^ 3 - 1 = ‖((R : ℂ) * Complex.exp (I * θ)) ^ 3‖ - ‖(1 : ℂ)‖ := by
          simp [norm_pow, abs_of_pos hR0]
        _ ≤ _ := by simpa [add_comm] using ht
    have hdennorm : 0 < ‖1 + ((R : ℂ) * Complex.exp (I * θ)) ^ 3‖ :=
      lt_of_lt_of_le hden htriangle
    simp [Complex.norm_exp, Complex.mul_re, abs_of_pos hR0]
    calc
      R / ‖1 + ((R : ℂ) * Complex.exp (I * θ)) ^ 3‖ * R =
          R ^ 2 / ‖1 + ((R : ℂ) * Complex.exp (I * θ)) ^ 3‖ := by ring
      _ ≤ R ^ 2 / (R ^ 3 - 1) :=
        div_le_div_of_nonneg_left (sq_nonneg R) hden htriangle
  · rw [sub_zero, abs_of_nonneg (by dsimp [sectorAlpha]; positivity)]
    ring

lemma sectorArcIntegral_tendsto_zero :
    Tendsto sectorArcIntegral atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun R : ℝ =>
      sectorAlpha * (R ^ 2 / (R ^ 3 - 1)))
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
    exact sectorArcIntegral_norm_le R hR
  · have hinv : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero
    have hden : Tendsto (fun R : ℝ => (1 - R⁻¹ ^ 3)⁻¹) atTop (𝓝 1) := by
      have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
        tendsto_const_nhds
      convert (hone.sub (hinv.pow 3)).inv₀
        (by norm_num : (1 : ℝ) - 0 ^ 3 ≠ 0) using 1
      norm_num
    have hrat : Tendsto (fun R : ℝ => R ^ 2 / (R ^ 3 - 1)) atTop (𝓝 0) := by
      have ht := hinv.mul hden
      convert ht.congr' ?_ using 1
      · norm_num
      · filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
        field_simp
    simpa using (tendsto_const_nhds.mul hrat)

lemma one_sub_sectorRoot_sq_ne_zero : (1 - sectorRoot ^ 2 : ℂ) ≠ 0 := by
  intro h
  have hs : sectorRoot ^ 2 = 1 := (sub_eq_zero.mp h).symm
  have hr : sectorRoot = 1 := calc
    sectorRoot = sectorRoot * 1 := by ring
    _ = sectorRoot * sectorRoot ^ 2 := by rw [hs]
    _ = sectorRoot ^ 3 := by ring
    _ = 1 := sectorRoot_cube
  have hi := congrArg Complex.im hr
  rw [sectorRoot_eq, poleC] at hi
  have hz : Real.sqrt 3 = 0 := by simpa using hi
  exact (by positivity : 0 < Real.sqrt 3).ne' hz

def transformedLimit : ℂ :=
  (1 - sectorRoot ^ 2)⁻¹ * ((3 * poleA)⁻¹ * (2 * π * I))

lemma radialIntegral_eventually_eq (R : ℝ) (hR : 1 < R) :
    radialIntegral R = (1 - sectorRoot ^ 2)⁻¹ *
      ((3 * poleA)⁻¹ * (2 * π * I) - sectorArcIntegral R) := by
  have h := transformed_sector_value R hR
  rw [transformed_boundary_decomposition] at h
  calc
    radialIntegral R = (1 - sectorRoot ^ 2)⁻¹ *
        ((1 - sectorRoot ^ 2) * radialIntegral R) := by
      field_simp [one_sub_sectorRoot_sq_ne_zero]
    _ = _ := by
      congr 1
      linear_combination h

lemma radialIntegral_tendsto :
    Tendsto radialIntegral atTop (𝓝 transformedLimit) := by
  have hc : Tendsto (fun _ : ℝ => (3 * poleA)⁻¹ * (2 * π * I)) atTop
      (𝓝 ((3 * poleA)⁻¹ * (2 * π * I))) := tendsto_const_nhds
  have hlim := (hc.sub sectorArcIntegral_tendsto_zero).const_mul
    ((1 - sectorRoot ^ 2)⁻¹)
  change Tendsto radialIntegral atTop
    (𝓝 ((1 - sectorRoot ^ 2)⁻¹ * ((3 * poleA)⁻¹ * (2 * π * I))))
  convert hlim.congr' ?_ using 1
  · simp only [sub_zero]
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
  exact (radialIntegral_eventually_eq R hR).symm

lemma transformedLimit_value :
    transformedLimit = ((2 * π / (3 * Real.sqrt 3) : ℝ) : ℂ) := by
  unfold transformedLimit sectorRoot poleA
  rw [exp_I_sectorAlpha]
  unfold poleC
  have hsC : ((Real.sqrt 3 : ℂ) ^ 2) = 3 := by exact_mod_cast sqrt3_sq
  have hs0R : Real.sqrt 3 ≠ 0 := by positivity
  have hs0 : (Real.sqrt 3 : ℂ) ≠ 0 := by exact_mod_cast hs0R
  have hs3 : ((Real.sqrt 3 : ℂ) ^ 3) = 3 * Real.sqrt 3 := by
    calc
      _ = (Real.sqrt 3 : ℂ) ^ 2 * Real.sqrt 3 := by ring
      _ = _ := by rw [hsC]
  field_simp
  ring_nf
  rw [hsC, hs3, show I ^ 2 = (-1 : ℂ) by norm_num,
    show I ^ 3 = -I by norm_num]
  ring_nf
  rw [Complex.inv_I]
  have hIp : I * (π : ℂ) * (-I) = π := by
    rw [show I * (π : ℂ) * (-I) = -(I * I) * π by ring, I_mul_I]
    ring
  rw [hIp]
  push_cast
  ring

def transformedReal (x : ℝ) : ℝ := x / (1 + x ^ 3)

lemma radialIntegral_eq_ofReal (R : ℝ) :
    radialIntegral R = (∫ x : ℝ in 0..R, transformedReal x : ℝ) := by
  unfold radialIntegral transformedIntegrand transformedReal
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro x _
  push_cast
  rfl

lemma transformedReal_integrable :
    IntegrableOn transformedReal (Ioi 0) volume := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  constructor
  · apply (show ContinuousOn transformedReal (Icc 0 1) from ?_).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
    intro x hx
    apply ContinuousAt.continuousWithinAt
    unfold transformedReal
    fun_prop (disch :=
      have hx0 : 0 ≤ x := hx.1
      positivity)
  · have hp : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
    refine hp.mono' ?_ ?_
    · have hc : ContinuousOn transformedReal (Ioi 1) := by
        intro x hx
        apply ContinuousAt.continuousWithinAt
        unfold transformedReal
        apply ContinuousAt.div (by fun_prop)
        · fun_prop
        · have hx1 : 1 < x := hx
          positivity
      exact hc.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      change 1 < x at hx
      unfold transformedReal
      rw [Real.norm_eq_abs, abs_of_pos (div_pos (lt_trans zero_lt_one hx) (by positivity))]
      calc
        x / (1 + x ^ 3) ≤ 1 / x ^ 2 := by
          apply (div_le_iff₀ (by positivity)).2
          field_simp
          nlinarith
        _ = x ^ (-2 : ℝ) := by
          rw [Real.rpow_neg (le_of_lt (lt_trans zero_lt_one hx)), Real.rpow_two]
          ring

lemma integral_transformedReal :
    ∫ x in Ioi (0 : ℝ), transformedReal x =
      2 * π / (3 * Real.sqrt 3) := by
  have hfinite := MeasureTheory.intervalIntegral_tendsto_integral_Ioi
    (0 : ℝ) transformedReal_integrable tendsto_id
  have hcont := Complex.continuous_re.tendsto transformedLimit
  have hcontour : Tendsto (fun R : ℝ =>
      ∫ x : ℝ in 0..R, transformedReal x) atTop
      (𝓝 (2 * π / (3 * Real.sqrt 3))) := by
    have h := hcont.comp radialIntegral_tendsto
    rw [transformedLimit_value] at h
    apply h.congr'
    filter_upwards with R
    simp only [Function.comp_apply]
    rw [radialIntegral_eq_ofReal]
    simp
  exact tendsto_nhds_unique hfinite hcontour

lemma transformed_substitution :
    4 * (∫ x in Ioi (0 : ℝ), x ^ 7 / (1 + x ^ 12)) =
      ∫ u in Ioi (0 : ℝ), transformedReal u := by
  have h := MeasureTheory.integral_comp_rpow_Ioi_of_pos
    (g := transformedReal) (p := (4 : ℝ)) (by norm_num)
  rw [← h]
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := hx.le
  unfold transformedReal
  have h4 : x ^ (4 : ℝ) = x ^ (4 : ℕ) := by
    simpa using (Real.rpow_natCast x 4)
  have h3 : x ^ ((4 : ℝ) - 1) = x ^ (3 : ℕ) := by
    norm_num
  rw [h4, h3]
  change 4 * (x ^ 7 / (1 + x ^ 12)) =
    (4 * x ^ 3) * (x ^ 4 / (1 + (x ^ 4) ^ 3))
  ring

/-- APM a94A06, proved from the prescribed pie-slice contour after the
substitution `u = x⁴`. -/
theorem integral_x7_over_1_plus_x12 :
    ∫ x in Ioi (0:ℝ), x^7 / (1 + x^12) = Real.sqrt 3 * π / 18 := by
  have hsub := transformed_substitution
  rw [integral_transformedReal] at hsub
  have hs : (Real.sqrt 3) ^ 2 = 3 := sqrt3_sq
  have hs0 : Real.sqrt 3 ≠ 0 := by positivity
  calc
    _ = π / (6 * Real.sqrt 3) := by
      apply (eq_div_iff (mul_ne_zero (by norm_num) hs0)).2
      field_simp [hs0] at hsub
      linarith
    _ = _ := by
      field_simp [hs0]
      nlinarith

end ApmCanaries.A94A06
