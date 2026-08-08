import Mathlib

/-!
# APM a03J07 — Phragmén–Lindelöf on the upper half-plane

## Statement repairs

The source's boundary hypothesis quantifies `x ∈ ℝ` but writes `|f(z)|`;
the free `z` is corrected to `x`, as required by the intended real-axis
boundary bound.

## Encoding questions

None. The open upper half-plane, its closure, boundedness, continuity, and
complex differentiability are represented directly.
-/

open Set

noncomputable section

def apm_a03J07_H : Set ℂ := {z : ℂ | 0 < z.im}

theorem apm_a03j07 (f : ℂ → ℂ) (M C0 : ℝ)
    (hcont : ContinuousOn f (closure apm_a03J07_H))
    (hanal : DifferentiableOn ℂ f apm_a03J07_H)
    (hbdd : ∀ z ∈ closure apm_a03J07_H, ‖f z‖ ≤ C0)
    (hreal : ∀ x : ℝ, ‖f (x : ℂ)‖ ≤ M) :
    ∀ z ∈ apm_a03J07_H, ‖f z‖ ≤ M := by
  -- Reuse the rotation/Phragmén--Lindelöf packaging from solved sibling
  -- `b99A01`: rotation by `I` identifies the upper and right half-planes.
  intro z hz
  let g : ℂ → ℂ := fun w ↦ f (Complex.I * w)
  have hgdc : DiffContOnCl ℂ g {w : ℂ | 0 < w.re} := by
    constructor
    · apply hanal.comp
        ((differentiable_const Complex.I).mul differentiable_id).differentiableOn
      intro w hw
      simpa [apm_a03J07_H, Complex.mul_im] using hw
    · apply hcont.comp (continuous_const_mul Complex.I).continuousOn
      intro w hw
      rw [Complex.closure_setOf_lt_re] at hw
      simpa [apm_a03J07_H, Complex.mul_im, Complex.closure_setOf_lt_im] using hw
  have hg_bound : ∀ w : ℂ, 0 ≤ w.re → ‖g w‖ ≤ C0 := by
    intro w hw
    apply hbdd
    unfold apm_a03J07_H
    rw [Complex.closure_setOf_lt_im]
    simpa [Complex.mul_im] using hw
  have hgexp : ∃ c < (2 : ℝ), ∃ B,
      g =O[Bornology.cobounded ℂ ⊓ Filter.principal {w : ℂ | 0 < w.re}]
        fun w ↦ Real.exp (B * ‖w‖ ^ c) := by
    refine ⟨0, by norm_num, 0, Asymptotics.IsBigO.of_bound C0 ?_⟩
    apply Filter.Eventually.filter_mono inf_le_right
    rw [Filter.eventually_principal]
    intro w hw
    simpa only [zero_mul, Real.exp_zero, Real.norm_eq_abs, abs_one, mul_one] using
      hg_bound w hw.le
  have hgreal : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop fun x : ℝ ↦ ‖g x‖ := by
    refine ⟨C0, (Filter.eventually_ge_atTop 0).mono fun x hx ↦ ?_⟩
    exact hg_bound x (by simpa using hx)
  have hgimag : ∀ x : ℝ, ‖g (x * Complex.I)‖ ≤ M := by
    intro x
    have heq : Complex.I * ((x : ℂ) * Complex.I) = ((-x : ℝ) : ℂ) := calc
      Complex.I * ((x : ℂ) * Complex.I) = (x : ℂ) * (Complex.I * Complex.I) := by ring
      _ = (-x : ℝ) := by rw [Complex.I_mul_I]; norm_num
    simpa only [g, heq] using hreal (-x)
  have hright : ‖g (-Complex.I * z)‖ ≤ M := by
    apply PhragmenLindelof.right_half_plane_of_bounded_on_real
      hgdc hgexp hgreal hgimag
    simpa [Complex.mul_re, apm_a03J07_H] using hz.le
  have heq : Complex.I * (-Complex.I * z) = z := calc
    Complex.I * (-Complex.I * z) = -(Complex.I * Complex.I) * z := by ring
    _ = z := by rw [Complex.I_mul_I]; simp
  simpa only [g, heq] using hright
