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

-- The composed map sends H into A
theorem conformalMap_maps_H_to_A (z : ℂ) (hz : 0 < z.im) :
    conformalMap z ∈ wedgeSlit := by
  sorry -- compose steps 1-4, verify slit maps to slit

-- Part (b): all such maps are f ∘ φ for φ ∈ Aut(H)
-- RMT not in Mathlib. The statement:
-- theorem all_conformal_maps :
--   ∀ g, ConformalBij H wedgeSlit g →
--     ∃ (a b c d : ℝ), 0 < a*d - b*c ∧
--       ∀ z, g z = conformalMap ((a*z+b)/(c*z+d))
-- Aut(H) = PSL(2,ℝ) action exists in Mathlib: UpperHalfPlane.sl2_action
