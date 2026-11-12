import ConstructionTargets.RectangleCauchy
import ConstructionTargets.FinitePolePatch

/-!
# A finite simple-pole residue theorem for centered squares

This is the small residue theorem needed by the APM contour computations.  It
is proved directly from rectangle Cauchy: subtract the finitely many Cauchy
kernels, integrate the resulting entire function, and evaluate each kernel.
-/

open Complex MeasureTheory Real Set
open scoped Interval

noncomputable section

namespace ConstructionTargets.FiniteResidueRectangle

open ConstructionTargets.RectangleCauchy

/-- The geometric boundary of the centered square of half-side `R`. -/
def OnCenteredSquareBoundary (R : ℝ) (z : ℂ) : Prop :=
  (|z.re| = R ∧ |z.im| ≤ R) ∨ (|z.im| = R ∧ |z.re| ≤ R)

/-- Every point on one of the four parameterized sides satisfies the
geometric square-boundary predicate. -/
lemma onBoundary_horizontal (R x y : ℝ) (hR : 0 ≤ R) (hy : |y| = R)
    (hx : x ∈ [[-R, R]]) :
    OnCenteredSquareBoundary R (x + y * I) := by
  right
  constructor
  · simpa using hy
  · rw [uIcc_of_le (neg_le_self hR)] at hx
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im,
      zero_mul, sub_zero, add_zero]
    rw [abs_le]
    exact hx

/-- Vertical parameterized sides satisfy the square-boundary predicate. -/
lemma onBoundary_vertical (R x y : ℝ) (hR : 0 ≤ R) (hx : |x| = R)
    (hy : y ∈ [[-R, R]]) :
    OnCenteredSquareBoundary R (x + y * I) := by
  left
  constructor
  · simpa using hx
  · rw [uIcc_of_le (neg_le_self hR)] at hy
    simp only [add_im, ofReal_im, ofReal_re, mul_im, I_im, mul_one, I_re,
      mul_zero, zero_add, add_zero]
    rw [abs_le]
    exact hy

/-- **Finite residue theorem for a centered square.**  If subtracting the
listed simple principal parts from `f` gives an entire function `g`, then the
four-side integral of `f` is `2πi` times the sum of their coefficients.
The equality need only hold on the contour itself. -/
theorem centeredSquareBoundaryIntegral_eq_finset_residues
    (f g : ℂ → ℂ) (s : Finset ℝ) (c : ℝ → ℂ) (R : ℝ)
    (hR : 0 < R)
    (hinside : ∀ a ∈ s, |a| < R)
    (hg : Differentiable ℂ g)
    (hdecomp : ∀ z, OnCenteredSquareBoundary R z →
      f z = g z + ∑ a ∈ s, c a * (z - (a : ℂ))⁻¹) :
    centeredSquareBoundaryIntegral f R =
      2 * π * I * ∑ a ∈ s, c a := by
  let z₀ : ℂ := -R - R * I
  let w₀ : ℂ := R + R * I
  have hgint : RectangleBoundaryIntegrable g z₀ w₀ := by
    have hc := hg.continuous
    exact ⟨(hc.comp (by fun_prop)).intervalIntegrable _ _,
      (hc.comp (by fun_prop)).intervalIntegrable _ _,
      (hc.comp (by fun_prop)).intervalIntegrable _ _,
      (hc.comp (by fun_prop)).intervalIntegrable _ _⟩
  let p : ℝ → ℂ → ℂ := fun a z => c a * (z - (a : ℂ))⁻¹
  have hpint : ∀ a ∈ s, RectangleBoundaryIntegrable (p a) z₀ w₀ := by
    intro a ha
    exact (centeredSquareBoundaryIntegrable_sub_inv a R (hinside a ha)).const_mul (c a)
  have hcongr : centeredSquareBoundaryIntegral f R =
      centeredSquareBoundaryIntegral (fun z => g z + ∑ a ∈ s, p a z) R := by
    unfold centeredSquareBoundaryIntegral
    apply rectangleBoundaryIntegral_congr
    · intro x hx
      apply hdecomp
      convert onBoundary_horizontal R x (-R) hR.le (by
        simp [abs_of_pos hR]) (by simpa [z₀, w₀] using hx) using 1 <;>
        simp [z₀, w₀]
    · intro x hx
      apply hdecomp
      convert onBoundary_horizontal R x R hR.le (by
        simpa [abs_of_pos hR]) (by simpa [z₀, w₀] using hx) using 1 <;>
        simp [z₀, w₀]
    · intro y hy
      apply hdecomp
      convert onBoundary_vertical R R y hR.le (by
        simpa [abs_of_pos hR]) (by simpa [z₀, w₀] using hy) using 1 <;>
        simp [z₀, w₀]
    · intro y hy
      apply hdecomp
      convert onBoundary_vertical R (-R) y hR.le (by
        simp [abs_of_pos hR]) (by simpa [z₀, w₀] using hy) using 1 <;>
        simp [z₀, w₀]
  rw [hcongr]
  unfold centeredSquareBoundaryIntegral
  rw [rectangleBoundaryIntegral_add hgint
    (RectangleBoundaryIntegrable.finset_sum hpint)]
  rw [rectangleBoundaryIntegral_eq_zero g hg z₀ w₀, zero_add]
  rw [rectangleBoundaryIntegral_finset_sum hpint]
  have hpval (a : ℝ) (ha : a ∈ s) :
      rectangleBoundaryIntegral (p a) z₀ w₀ = c a * (2 * π * I) := by
    unfold p
    rw [rectangleBoundaryIntegral_const_mul]
    change c a * centeredSquareBoundaryIntegral
      (fun z => (z - (a : ℂ))⁻¹) R = _
    rw [centeredSquareBoundaryIntegral_sub_inv a R (hinside a ha)]
  rw [Finset.sum_congr rfl (fun a ha => hpval a ha)]
  simp_rw [mul_assoc]
  rw [← Finset.sum_mul]
  ring

end ConstructionTargets.FiniteResidueRectangle
