import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

open Complex Set Filter Topology

noncomputable section

/-! # APM a01A12: Conformal mapping H → wedge minus slit
    f(z) = (1 - z²)^{1/4}, 4-step composition.
-/

-- Target domain
def wedgeSlit : Set ℂ :=
  {z : ℂ | z ≠ 0 ∧ |z.arg| < Real.pi / 4} \
  {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ z.im = 0}

-- The map
def conformalMap (z : ℂ) : ℂ :=
  (1 - z ^ 2) ^ (1/4 : ℂ)

-- Step 1: rotation maps H to RHP
lemma step1_maps (z : ℂ) (hz : 0 < z.im) : 0 < (-I * z).re := by
  have : (-I * z).re = z.im := by
    simp [Complex.mul_re]
  simpa [this] using hz

-- Step 1: injective
lemma step1_inj : Function.Injective (fun z : ℂ => -I * z) :=
  fun _ _ h => by simpa [neg_mul] using h

-- Step 2: squaring is differentiable
lemma step2_diff (w : ℂ) : DifferentiableAt ℂ (· ^ 2) w :=
  differentiableAt_pow 2

-- Step 2: squaring is injective on RHP
-- HtDP: a²=b², Re a>0, Re b>0 ⟹ a=b (since a=-b would give Re a = -Re b < 0)
lemma step2_inj_RHP : InjOn (· ^ 2 : ℂ → ℂ) {w | 0 < w.re} := by
  intro a ha b hb hsq
  have hcases : a = b ∨ a = -b := sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  rcases hcases with h | h
  · exact h
  · have ha_pos : 0 < a.re := by simpa using ha
    have hb_pos : 0 < b.re := by simpa using hb
    have hb_neg : b.re < 0 := by
      have hlt : 0 < (-b).re := by simpa [h] using ha_pos
      have : 0 < -(b.re) := by simpa [Complex.neg_re] using hlt
      exact neg_pos.mp this
    exact (lt_asymm hb_pos hb_neg).elim

-- Step 2: squaring maps RHP onto slit plane
-- HtDP: w ∈ RHP ⟹ arg(w) ∈ (-π/2,π/2) ⟹ arg(w²) ∈ (-π,π) ⟹ w² ∉ (-∞,0]
lemma step2_image : MapsTo (· ^ 2 : ℂ → ℂ) {w | 0 < w.re} {ζ : ℂ | (0:ℝ) < ζ.re ∨ ζ.im ≠ 0} := by
  intro w hw
  change 0 < w.re at hw
  change 0 < (w ^ 2).re ∨ (w ^ 2).im ≠ 0
  by_cases him : (w ^ 2).im = 0
  · left
    have him' : w.re * w.im + w.im * w.re = 0 := by
      simpa [pow_two, Complex.mul_im] using him
    have hmul : w.re * w.im = 0 := by
      nlinarith
    have hwim : w.im = 0 := (mul_eq_zero.mp hmul).resolve_left hw.ne'
    simp [pow_two, Complex.mul_re, hwim]
    exact hw.ne'
  · exact Or.inr him

-- Step 4: fourth root maps slit plane to wedge
-- HtDP: arg(η) ∈ (-π,π) ⟹ arg(η^{1/4}) ∈ (-π/4,π/4)
lemma step4_to_wedge (η : ℂ) (hη : η ≠ 0 ∧ η.arg ≠ Real.pi) :
    |((η : ℂ) ^ (1/4 : ℂ)).arg| < Real.pi / 4 := by
  have harg_lt : η.arg < Real.pi :=
    lt_of_le_of_ne (arg_le_pi η) hη.2
  have hscaled :
      |η.arg * (1 / 4 : ℝ)| < Real.pi / 4 := by
    rw [abs_lt]
    constructor <;> nlinarith [neg_pi_lt_arg η, Real.pi_pos]
  have hr : 0 < ‖η‖ ^ (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (norm_pos_iff.mpr hη.1) _
  have hangle :
      η.arg * (1 / 4 : ℝ) ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor <;> nlinarith [neg_pi_lt_arg η, arg_le_pi η, Real.pi_pos]
  have hquarter : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by norm_num
  rw [hquarter, cpow_ofReal]
  have harg := arg_mul_cos_add_sin_mul_I hr hangle
  rw [← ofReal_cos, ← ofReal_sin] at *
  rw [harg]
  exact hscaled

lemma fourthRoot_not_mem_unitSegment (η : ℂ)
    (hη : 1 < η.re ∨ η.im ≠ 0) :
    η ^ (1 / 4 : ℂ) ∉ {q : ℂ | 0 ≤ q.re ∧ q.re ≤ 1 ∧ q.im = 0} := by
  intro hq
  change 0 ≤ (η ^ (1 / 4 : ℂ)).re ∧
      (η ^ (1 / 4 : ℂ)).re ≤ 1 ∧
      (η ^ (1 / 4 : ℂ)).im = 0 at hq
  let q := η ^ (1 / 4 : ℂ)
  have hq_nonneg : 0 ≤ q.re := by
    simpa [q] using hq.1
  have hq_le_one : q.re ≤ 1 := by
    simpa [q] using hq.2.1
  have hq_real : q = (q.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa [q] using hq.2.2
  have hquarter : (1 / 4 : ℂ) = (4 : ℂ)⁻¹ := by norm_num
  have hq_pow : q ^ 4 = η := by
    simp [q, hquarter]
  have hη_im : η.im = 0 := by
    rw [← hq_pow, hq_real]
    norm_num [pow_succ]
  have hη_re : η.re ≤ 1 := by
    rw [← hq_pow, hq_real]
    norm_num [pow_succ]
    simpa [pow_succ] using (pow_le_one₀ hq_nonneg hq_le_one : q.re ^ 4 ≤ 1)
  rcases hη with hη_re' | hη_im'
  · exact (not_lt_of_ge hη_re) hη_re'
  · exact hη_im' hη_im

-- The composed map sends H into A
theorem conformalMap_maps_H_to_A (z : ℂ) (hz : 0 < z.im) :
    conformalMap z ∈ wedgeSlit := by
  let w : ℂ := -I * z
  let η : ℂ := 1 - z ^ 2
  have hw : 0 < w.re := by
    simpa [w] using step1_maps z hz
  have hw_sq := step2_image hw
  have hw_sq_eq : w ^ 2 = -z ^ 2 := by
    simp only [w]
    rw [mul_pow]
    norm_num
  have hη_eq : η = 1 + w ^ 2 := by
    simp only [η, hw_sq_eq]
    ring
  have hη_image : 1 < η.re ∨ η.im ≠ 0 := by
    rcases hw_sq with hw_re | hw_im
    · left
      rw [hη_eq]
      simp only [add_re, one_re]
      linarith
    · right
      rw [hη_eq]
      simpa using hw_im
  have hη_ne : η ≠ 0 := by
    intro hzero
    rcases hη_image with hη_re | hη_im
    · have : (1 : ℝ) < 0 := by simpa [hzero] using hη_re
      linarith
    · simp [hzero] at hη_im
  have hη_arg : η.arg ≠ Real.pi := by
    intro harg
    have hneg : η.re < 0 ∧ η.im = 0 :=
      arg_eq_pi_iff.mp harg
    rcases hη_image with hη_re | hη_im
    · linarith
    · exact hη_im hneg.2
  rw [wedgeSlit]
  constructor
  · constructor
    · rw [conformalMap]
      exact (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr hη_ne
    · rw [conformalMap]
      simpa [η] using step4_to_wedge η ⟨hη_ne, hη_arg⟩
  · rw [conformalMap]
    simpa [η] using fourthRoot_not_mem_unitSegment η hη_image

-- Part (b): all such maps are f ∘ φ for φ ∈ Aut(H)
-- RMT not in Mathlib. The statement:
-- theorem all_conformal_maps :
--   ∀ g, ConformalBij H wedgeSlit g →
--     ∃ (a b c d : ℝ), 0 < a*d - b*c ∧
--       ∀ z, g z = conformalMap ((a*z+b)/(c*z+d))
-- Aut(H) = PSL(2,ℝ) action exists in Mathlib: UpperHalfPlane.sl2_action
