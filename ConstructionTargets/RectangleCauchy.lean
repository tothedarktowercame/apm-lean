import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Cauchy's theorem on an axis-aligned rectangle

This module packages Mathlib's four interval integrals for the positively
oriented boundary of the rectangle whose opposite corners are `z` and `w`.
It supplies the algebraic operations needed by contour computations without
hiding the actual four-side integral.
-/

open Complex MeasureTheory Real Set
open scoped Interval

noncomputable section

namespace ConstructionTargets.RectangleCauchy

/-- The positively oriented boundary integral around the axis-aligned
rectangle with opposite corners `z` and `w`. -/
def rectangleBoundaryIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) -
    (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
    I * (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

/-- Integrability of an integrand on all four parameterized rectangle sides. -/
def RectangleBoundaryIntegrable (f : ℂ → ℂ) (z w : ℂ) : Prop :=
  IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im w.im ∧
  IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im w.im

/-- Multiplication by a constant preserves integrability on a rectangle boundary. -/
lemma RectangleBoundaryIntegrable.const_mul {f : ℂ → ℂ} {z w : ℂ}
    (hf : RectangleBoundaryIntegrable f z w) (c : ℂ) :
    RectangleBoundaryIntegrable (fun u => c * f u) z w :=
  ⟨hf.1.const_mul c, hf.2.1.const_mul c,
    hf.2.2.1.const_mul c, hf.2.2.2.const_mul c⟩

/-- Addition preserves integrability on a rectangle boundary. -/
lemma RectangleBoundaryIntegrable.add {f g : ℂ → ℂ} {z w : ℂ}
    (hf : RectangleBoundaryIntegrable f z w)
    (hg : RectangleBoundaryIntegrable g z w) :
    RectangleBoundaryIntegrable (fun u => f u + g u) z w :=
  ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
    hf.2.2.1.add hg.2.2.1, hf.2.2.2.add hg.2.2.2⟩

/-- Rectangle boundary integration is additive for integrable boundary data. -/
lemma rectangleBoundaryIntegral_add {f g : ℂ → ℂ} {z w : ℂ}
    (hf : RectangleBoundaryIntegrable f z w)
    (hg : RectangleBoundaryIntegrable g z w) :
    rectangleBoundaryIntegral (fun u => f u + g u) z w =
      rectangleBoundaryIntegral f z w + rectangleBoundaryIntegral g z w := by
  unfold rectangleBoundaryIntegral
  rw [intervalIntegral.integral_add hf.1 hg.1,
    intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2.1 hg.2.2.1,
    intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  ring

/-- Constants pull through a rectangle boundary integral. -/
lemma rectangleBoundaryIntegral_const_mul (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    rectangleBoundaryIntegral (fun u => c * f u) z w =
      c * rectangleBoundaryIntegral f z w := by
  have hbottom :
      (∫ x : ℝ in z.re..w.re, c * f (x + z.im * I)) =
        c * ∫ x : ℝ in z.re..w.re, f (x + z.im * I) :=
    intervalIntegral.integral_const_mul (μ := volume)
      (a := z.re) (b := w.re) c (fun x : ℝ => f (x + z.im * I))
  have htop :
      (∫ x : ℝ in z.re..w.re, c * f (x + w.im * I)) =
        c * ∫ x : ℝ in z.re..w.re, f (x + w.im * I) :=
    intervalIntegral.integral_const_mul (μ := volume)
      (a := z.re) (b := w.re) c (fun x : ℝ => f (x + w.im * I))
  have hright :
      (∫ y : ℝ in z.im..w.im, c * f (w.re + y * I)) =
        c * ∫ y : ℝ in z.im..w.im, f (w.re + y * I) :=
    intervalIntegral.integral_const_mul (μ := volume)
      (a := z.im) (b := w.im) c (fun y : ℝ => f (w.re + y * I))
  have hleft :
      (∫ y : ℝ in z.im..w.im, c * f (z.re + y * I)) =
        c * ∫ y : ℝ in z.im..w.im, f (z.re + y * I) :=
    intervalIntegral.integral_const_mul (μ := volume)
      (a := z.im) (b := w.im) c (fun y : ℝ => f (z.re + y * I))
  unfold rectangleBoundaryIntegral
  rw [hbottom, htop, hright, hleft]
  ring

/-- Rectangle boundary integrals respect pointwise equality on all four sides. -/
lemma rectangleBoundaryIntegral_congr {f g : ℂ → ℂ} {z w : ℂ}
    (hlower : ∀ x ∈ [[z.re, w.re]],
      f (x + z.im * I) = g (x + z.im * I))
    (hupper : ∀ x ∈ [[z.re, w.re]],
      f (x + w.im * I) = g (x + w.im * I))
    (hright : ∀ y ∈ [[z.im, w.im]],
      f (w.re + y * I) = g (w.re + y * I))
    (hleft : ∀ y ∈ [[z.im, w.im]],
      f (z.re + y * I) = g (z.re + y * I)) :
    rectangleBoundaryIntegral f z w = rectangleBoundaryIntegral g z w := by
  unfold rectangleBoundaryIntegral
  rw [intervalIntegral.integral_congr hlower,
    intervalIntegral.integral_congr hupper,
    intervalIntegral.integral_congr hright,
    intervalIntegral.integral_congr hleft]

/-- **Cauchy's theorem for a rectangle.** The boundary integral of a function
differentiable on the closed rectangle is zero. -/
theorem rectangleBoundaryIntegral_eq_zero_of_differentiableOn
    (f : ℂ → ℂ) (z w : ℂ)
    (hf : DifferentiableOn ℂ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    rectangleBoundaryIntegral f z w = 0 := by
  unfold rectangleBoundaryIntegral
  simpa [smul_eq_mul] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hf

/-- The rectangle boundary integral of an entire function is zero. -/
theorem rectangleBoundaryIntegral_eq_zero
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (z w : ℂ) :
    rectangleBoundaryIntegral f z w = 0 := by
  apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn
  exact hf.differentiableOn

end ConstructionTargets.RectangleCauchy
