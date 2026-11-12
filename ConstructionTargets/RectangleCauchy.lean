import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import ConstructionTargets.UpperSemicircleCauchy

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

open ConstructionTargets.UpperSemicircleCauchy

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

/-- A four-side fundamental theorem of calculus: if `f` is the complex
derivative of one primitive at every boundary point, its rectangle boundary
integral vanishes. No differentiability inside the rectangle is required. -/
theorem rectangleBoundaryIntegral_eq_zero_of_boundary_primitive
    (f P : ℂ → ℂ) (z w : ℂ)
    (hf : RectangleBoundaryIntegrable f z w)
    (hP : ∀ u, (u.re ∈ [[z.re, w.re]] ∧
          (u.im = z.im ∨ u.im = w.im)) ∨
        (u.im ∈ [[z.im, w.im]] ∧
          (u.re = z.re ∨ u.re = w.re)) →
      HasDerivAt P (f u) u) :
    rectangleBoundaryIntegral f z w = 0 := by
  have hbottom :
      (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) =
        P (w.re + z.im * I) - P (z.re + z.im * I) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ => P (x + z.im * I))
      (f' := fun x : ℝ => f (x + z.im * I)) ?_ hf.1
    · intro x hx
      have hp := hP (x + z.im * I) (by
        left
        constructor
        · simpa using hx
        · left; simp)
      convert primitive_comp_path_hasDerivAt
        (γ := fun u : ℂ => u + z.im * I) hp
        ((hasDerivAt_id (x := (x : ℂ))).add_const (z.im * I)) using 1 <;>
          simp <;> ring
  have htop :
      (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) =
        P (w.re + w.im * I) - P (z.re + w.im * I) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ => P (x + w.im * I))
      (f' := fun x : ℝ => f (x + w.im * I)) ?_ hf.2.1
    · intro x hx
      have hp := hP (x + w.im * I) (by
        left
        constructor
        · simpa using hx
        · right; simp)
      convert primitive_comp_path_hasDerivAt
        (γ := fun u : ℂ => u + w.im * I) hp
        ((hasDerivAt_id (x := (x : ℂ))).add_const (w.im * I)) using 1 <;>
          simp <;> ring
  have hright :
      I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) =
        P (w.re + w.im * I) - P (w.re + z.im * I) := by
    have hi : IntervalIntegrable
        (fun y : ℝ => I * f (w.re + y * I)) volume z.im w.im :=
      hf.2.2.1.const_mul I
    have hFTC : (∫ y : ℝ in z.im..w.im, I * f (w.re + y * I)) =
        P (w.re + w.im * I) - P (w.re + z.im * I) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun y : ℝ => P (w.re + y * I))
        (f' := fun y : ℝ => I * f (w.re + y * I)) ?_ hi
      · intro y hy
        have hp := hP (w.re + y * I) (by
          right
          constructor
          · simpa using hy
          · right; simp)
        convert primitive_comp_path_hasDerivAt
          (γ := fun u : ℂ => w.re + u * I) hp
          (((hasDerivAt_id (x := (y : ℂ))).mul_const I).const_add (w.re : ℂ)) using 1 <;>
            simp <;> ring
    have hconst :
        (∫ y : ℝ in z.im..w.im, I * f (w.re + y * I)) =
          I * ∫ y : ℝ in z.im..w.im, f (w.re + y * I) :=
      intervalIntegral.integral_const_mul (μ := volume)
        (a := z.im) (b := w.im) I (fun y : ℝ => f (w.re + y * I))
    rw [hconst] at hFTC
    exact hFTC
  have hleft :
      I * (∫ y : ℝ in z.im..w.im, f (z.re + y * I)) =
        P (z.re + w.im * I) - P (z.re + z.im * I) := by
    have hi : IntervalIntegrable
        (fun y : ℝ => I * f (z.re + y * I)) volume z.im w.im :=
      hf.2.2.2.const_mul I
    have hFTC : (∫ y : ℝ in z.im..w.im, I * f (z.re + y * I)) =
        P (z.re + w.im * I) - P (z.re + z.im * I) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun y : ℝ => P (z.re + y * I))
        (f' := fun y : ℝ => I * f (z.re + y * I)) ?_ hi
      · intro y hy
        have hp := hP (z.re + y * I) (by
          right
          constructor
          · simpa using hy
          · left; simp)
        convert primitive_comp_path_hasDerivAt
          (γ := fun u : ℂ => z.re + u * I) hp
          (((hasDerivAt_id (x := (y : ℂ))).mul_const I).const_add (z.re : ℂ)) using 1 <;>
            simp <;> ring
    have hconst :
        (∫ y : ℝ in z.im..w.im, I * f (z.re + y * I)) =
          I * ∫ y : ℝ in z.im..w.im, f (z.re + y * I) :=
      intervalIntegral.integral_const_mul (μ := volume)
        (a := z.im) (b := w.im) I (fun y : ℝ => f (z.re + y * I))
    rw [hconst] at hFTC
    exact hFTC
  unfold rectangleBoundaryIntegral
  rw [hbottom, htop, hright, hleft]
  ring

/-- On the lower-right quadrant, negation crosses the principal logarithm
cut upward and adds `π i`. -/
lemma log_neg_eq_add_pi_I_of_re_pos_of_im_neg {q : ℂ}
    (hre : 0 < q.re) (him : q.im < 0) :
    Complex.log (-q) = Complex.log q + π * I := by
  have hq : q ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hneg : (-1 : ℂ) ≠ 0 := by norm_num
  have hargneg : q.arg < 0 := Complex.arg_neg_iff.mpr him
  have hmem : (-1 : ℂ).arg + q.arg ∈ Ioc (-π) π := by
    rw [Complex.arg_neg_one]
    constructor
    · have hp := Real.pi_pos
      have hlow := Complex.neg_pi_lt_arg q
      linarith
    · exact (add_le_iff_nonpos_right π).mpr hargneg.le
  rw [show -q = (-1 : ℂ) * q by ring, Complex.log_mul hneg hq hmem,
    Complex.log_neg_one]
  ring

/-- On the upper-right quadrant, negation crosses the principal logarithm
cut downward and subtracts `π i`. -/
lemma log_neg_eq_sub_pi_I_of_re_pos_of_im_pos {q : ℂ}
    (hre : 0 < q.re) (him : 0 < q.im) :
    Complex.log (-q) = Complex.log q - π * I := by
  have hq : q ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hnq : -q ≠ 0 := neg_ne_zero.mpr hq
  have hneg : (-1 : ℂ) ≠ 0 := by norm_num
  have hargneg : (-q).arg < 0 :=
    Complex.arg_neg_iff.mpr (by simpa using neg_lt_zero.mpr him)
  have hmem : (-q).arg + (-1 : ℂ).arg ∈ Ioc (-π) π := by
    rw [Complex.arg_neg_one]
    constructor
    · have hlow := Complex.neg_pi_lt_arg (-q)
      have hp := Real.pi_pos
      linarith
    · exact add_le_iff_nonpos_left.mpr hargneg.le
  have hmul := Complex.log_mul hnq hneg hmem
  rw [show (-q) * (-1 : ℂ) = q by ring, Complex.log_neg_one] at hmul
  linear_combination -hmul

/-- A horizontal segment away from the real axis integrates the Cauchy
kernel by the principal logarithm. -/
lemma integral_horizontal_sub_inv_eq_log
    (a : ℂ) (c l u : ℝ) (hc : c ≠ a.im) :
    (∫ x : ℝ in l..u, ((x : ℂ) + c * I - a)⁻¹) =
      Complex.log ((u : ℂ) + c * I - a) -
        Complex.log ((l : ℂ) + c * I - a) := by
  have hne (x : ℝ) : (x : ℂ) + c * I - a ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact hc (sub_eq_zero.mp hi)
  have hd (x : ℝ) : HasDerivAt
      (fun t : ℝ => Complex.log ((t : ℂ) + c * I - a))
      (((x : ℂ) + c * I - a)⁻¹) x := by
    have hslit : (x : ℂ) + c * I - a ∈ Complex.slitPlane := by
      right
      simpa using sub_ne_zero.mpr hc
    convert ((Complex.hasDerivAt_log hslit).comp x
      (((Complex.ofRealCLM.hasDerivAt (x := x)).add_const (c * I)).sub_const a)) using 1
    simp [Complex.ofRealCLM_apply]
  have hi : IntervalIntegrable
      (fun x : ℝ => ((x : ℂ) + c * I - a)⁻¹) volume l u := by
    exact (((continuous_ofReal.add continuous_const).sub continuous_const).inv₀
      (fun x => hne x)).intervalIntegrable _ _
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hd x) hi

/-- On a vertical line strictly to the right of the pole, multiplying the
parameter integral by `i` gives the logarithm endpoint difference. -/
lemma I_mul_integral_vertical_sub_inv_eq_log
    (a : ℂ) (d l u : ℝ) (hd : a.re < d) :
    I * (∫ y : ℝ in l..u, ((d : ℂ) + y * I - a)⁻¹) =
      Complex.log ((d : ℂ) + u * I - a) -
        Complex.log ((d : ℂ) + l * I - a) := by
  have hne (y : ℝ) : (d : ℂ) + y * I - a ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have hderiv (y : ℝ) : HasDerivAt
      (fun t : ℝ => Complex.log ((d : ℂ) + t * I - a))
      (I * (((d : ℂ) + y * I - a)⁻¹)) y := by
    have hslit : (d : ℂ) + y * I - a ∈ Complex.slitPlane := by
      left
      simp
      linarith
    have hpath : HasDerivAt (fun t : ℝ => (d : ℂ) + t * I - a) I y := by
      convert ((((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I).const_add
        (d : ℂ)).sub_const a) using 1 <;> simp [Complex.ofRealCLM_apply]
    convert ((Complex.hasDerivAt_log hslit).comp y hpath) using 1 <;> ring
  have hi : IntervalIntegrable
      (fun y : ℝ => I * (((d : ℂ) + y * I - a)⁻¹)) volume l u := by
    exact (continuous_const.mul
      (((continuous_const.add (continuous_ofReal.mul continuous_const)).sub
        continuous_const).inv₀ (fun y => hne y))).intervalIntegrable _ _
  have hconst :
      (∫ y : ℝ in l..u, I * (((d : ℂ) + y * I - a)⁻¹)) =
        I * ∫ y : ℝ in l..u, ((d : ℂ) + y * I - a)⁻¹ :=
    intervalIntegral.integral_const_mul (μ := volume)
      (a := l) (b := u) I (fun y : ℝ => ((d : ℂ) + y * I - a)⁻¹)
  rw [← hconst]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hderiv y) hi

/-- On a vertical line strictly to the left of the pole, `log (-(z-a))`
is a primitive that stays on the principal slit plane. -/
lemma neg_I_mul_integral_vertical_sub_inv_eq_log_neg
    (a : ℂ) (d l u : ℝ) (hd : d < a.re) :
    -I * (∫ y : ℝ in l..u, ((d : ℂ) + y * I - a)⁻¹) =
      Complex.log (-((d : ℂ) + l * I - a)) -
        Complex.log (-((d : ℂ) + u * I - a)) := by
  have hne (y : ℝ) : (d : ℂ) + y * I - a ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have hderiv (y : ℝ) : HasDerivAt
      (fun t : ℝ => Complex.log (-((d : ℂ) + t * I - a)))
      (I * (((d : ℂ) + y * I - a)⁻¹)) y := by
    have hslit : -((d : ℂ) + y * I - a) ∈ Complex.slitPlane := by
      left
      simp
      linarith
    have hpath : HasDerivAt (fun t : ℝ => -((d : ℂ) + t * I - a)) (-I) y := by
      convert (((((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I).const_add
        (d : ℂ)).sub_const a).neg) using 1 <;> simp [Complex.ofRealCLM_apply]
    convert ((Complex.hasDerivAt_log hslit).comp y hpath) using 1 <;>
      simp only [inv_neg] <;> ring
  have hi : IntervalIntegrable
      (fun y : ℝ => I * (((d : ℂ) + y * I - a)⁻¹)) volume l u := by
    exact (continuous_const.mul
      (((continuous_const.add (continuous_ofReal.mul continuous_const)).sub
        continuous_const).inv₀ (fun y => hne y))).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hderiv y) hi
  have hconst :
      (∫ y : ℝ in l..u, I * (((d : ℂ) + y * I - a)⁻¹)) =
        I * ∫ y : ℝ in l..u, ((d : ℂ) + y * I - a)⁻¹ :=
    intervalIntegral.integral_const_mul (μ := volume)
      (a := l) (b := u) I (fun y : ℝ => ((d : ℂ) + y * I - a)⁻¹)
  rw [hconst] at hFTC
  linear_combination -hFTC

/-- The explicit positively oriented boundary integral of a centered square
of half-side `R`. -/
def centeredSquareBoundaryIntegral (f : ℂ → ℂ) (R : ℝ) : ℂ :=
  rectangleBoundaryIntegral f (-R - R * I) (R + R * I)

/-- The Cauchy kernel winds once around a real point strictly inside a
centered square. This is the rectangle analogue of the circle integral
`∮ (z-a)⁻¹ dz = 2πi`. -/
theorem centeredSquareBoundaryIntegral_sub_inv
    (a R : ℝ) (ha : |a| < R) :
    centeredSquareBoundaryIntegral (fun z => (z - (a : ℂ))⁻¹) R =
      2 * π * I := by
  have hR : 0 < R := lt_of_le_of_lt (abs_nonneg a) ha
  have har : a < R := lt_of_le_of_lt (le_abs_self a) ha
  have hla : -R < a := by
    have := neg_abs_le a
    linarith
  have hbottom := integral_horizontal_sub_inv_eq_log
    (a : ℂ) (-R) (-R) R (by simp; exact hR.ne')
  have htop := integral_horizontal_sub_inv_eq_log
    (a : ℂ) R (-R) R (by simp; exact hR.ne')
  have hright := I_mul_integral_vertical_sub_inv_eq_log
    (a : ℂ) R (-R) R (by simpa using har)
  have hleft := neg_I_mul_integral_vertical_sub_inv_eq_log_neg
    (a : ℂ) (-R) (-R) R (by simpa using hla)
  unfold centeredSquareBoundaryIntegral rectangleBoundaryIntegral
  simp only [neg_re, ofReal_re, mul_re, mul_im, I_re, ofReal_im, I_im, mul_zero,
    mul_one, sub_re, sub_im, neg_im, add_re, add_im, zero_mul, add_zero,
    zero_add, sub_zero, neg_zero, zero_sub]
  rw [hbottom, htop, hright]
  have hleft' :
      -(I * (∫ y : ℝ in -R..R,
        ((((-R : ℝ) : ℂ) + y * I - (a : ℂ))⁻¹))) =
        Complex.log (-((((-R : ℝ) : ℂ) + (-R : ℝ) * I - (a : ℂ)))) -
          Complex.log (-((((-R : ℝ) : ℂ) + R * I - (a : ℂ)))) := by
    simpa only [neg_mul] using hleft
  change _ + (-(I * (∫ y : ℝ in -R..R,
    ((((-R : ℝ) : ℂ) + y * I - (a : ℂ))⁻¹)))) = 2 * π * I
  rw [hleft']
  have hB : 0 < R + a := by linarith
  have hnegUpper := log_neg_eq_add_pi_I_of_re_pos_of_im_neg
    (q := (R + a : ℝ) - R * I) (by simp; linarith) (by simp; linarith)
  have hnegLower := log_neg_eq_sub_pi_I_of_re_pos_of_im_pos
    (q := (R + a : ℝ) + R * I) (by simp; linarith) (by simp; linarith)
  rw [show (((-R : ℝ) : ℂ)) + (-R : ℝ) * I - (a : ℂ) =
      -((R + a : ℝ) + R * I) by push_cast; ring,
    show (((-R : ℝ) : ℂ)) + R * I - (a : ℂ) =
      -((R + a : ℝ) - R * I) by push_cast; ring,
    hnegUpper, hnegLower]
  simp only [neg_neg]
  ring

/-- Every higher principal part has zero integral around a centered square.
The proof uses its explicit single-valued power primitive on the boundary. -/
theorem centeredSquareBoundaryIntegral_zpow_eq_zero
    (a R : ℝ) (ha : |a| < R) (k : ℤ) (hk : k ≤ -2) :
    centeredSquareBoundaryIntegral (fun z => (z - (a : ℂ)) ^ k) R = 0 := by
  let z₀ : ℂ := -R - R * I
  let w₀ : ℂ := R + R * I
  let f : ℂ → ℂ := fun z => (z - (a : ℂ)) ^ k
  let P : ℂ → ℂ := fun z =>
    (z - (a : ℂ)) ^ (k + 1) / (k + 1 : ℂ)
  have hR : 0 < R := lt_of_le_of_lt (abs_nonneg a) ha
  have har : a < R := lt_of_le_of_lt (le_abs_self a) ha
  have hla : -R < a := by
    have := neg_abs_le a
    linarith
  have hk1 : k + 1 ≠ 0 := by omega
  have boundary_ne (u : ℂ)
      (hu : (u.re ∈ [[z₀.re, w₀.re]] ∧
          (u.im = z₀.im ∨ u.im = w₀.im)) ∨
        (u.im ∈ [[z₀.im, w₀.im]] ∧
          (u.re = z₀.re ∨ u.re = w₀.re))) :
      u - (a : ℂ) ≠ 0 := by
    intro h
    have hua : u = (a : ℂ) := sub_eq_zero.mp h
    subst u
    rcases hu with hu | hu
    · rcases hu.2 with him | him
      · simp [z₀] at him
        linarith
      · simp [w₀] at him
        linarith
    · rcases hu.2 with hre | hre
      · simp [z₀] at hre
        linarith
      · simp [w₀] at hre
        linarith
  have hbottom_ne (x : ℝ) :
      (x : ℂ) + z₀.im * I - (a : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp [z₀] at hi
    linarith
  have htop_ne (x : ℝ) :
      (x : ℂ) + w₀.im * I - (a : ℂ) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp [w₀] at hi
    linarith
  have hright_ne (y : ℝ) :
      (w₀.re : ℂ) + y * I - (a : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [w₀] at hr
    linarith
  have hleft_ne (y : ℝ) :
      (z₀.re : ℂ) + y * I - (a : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [z₀] at hr
    linarith
  have hf : RectangleBoundaryIntegrable f z₀ w₀ := by
    have hside (γ : ℝ → ℂ) (hγ : Continuous γ)
        (hne : ∀ t, γ t - (a : ℂ) ≠ 0) (l u : ℝ) :
        IntervalIntegrable (fun t => f (γ t)) volume l u := by
      unfold f
      exact ((hγ.sub continuous_const).zpow₀
        k (fun t => Or.inl (hne t))).intervalIntegrable _ _
    exact ⟨hside _ (by fun_prop) hbottom_ne _ _,
      hside _ (by fun_prop) htop_ne _ _,
      hside _ (by fun_prop) hright_ne _ _,
      hside _ (by fun_prop) hleft_ne _ _⟩
  have hP (u : ℂ) (hu : (u.re ∈ [[z₀.re, w₀.re]] ∧
          (u.im = z₀.im ∨ u.im = w₀.im)) ∨
        (u.im ∈ [[z₀.im, w₀.im]] ∧
          (u.re = z₀.re ∨ u.re = w₀.re))) :
      HasDerivAt P (f u) u := by
    have hpow := (hasDerivAt_zpow (k + 1) (u - (a : ℂ))
      (Or.inl (boundary_ne u hu))).comp u
        ((hasDerivAt_id (x := u)).sub_const (a : ℂ))
    unfold P f
    convert hpow.div_const (k + 1 : ℂ) using 1
    · rw [show k + 1 - 1 = k by ring]
      have hk1c : ((k + 1 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hk1
      rw [show ((k : ℂ) + 1) = ((k + 1 : ℤ) : ℂ) by simp]
      field_simp [hk1c]
  unfold centeredSquareBoundaryIntegral
  exact rectangleBoundaryIntegral_eq_zero_of_boundary_primitive f P z₀ w₀ hf hP

end ConstructionTargets.RectangleCauchy
