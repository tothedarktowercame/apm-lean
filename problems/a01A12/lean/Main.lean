import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# APM a01A12 — conformal maps onto a wedge with a slit

## Statement repairs

None. The previous artifact covered only containment of the image. This
statement restores the source's requirements that the displayed map be
one-to-one and onto, and that all such maps be described.

## Encoding questions

None. Conformality is represented by complex differentiability with nonzero
derivative on the domain, and automorphisms of the upper half-plane are
represented concretely by real Möbius transformations with positive
determinant.
-/

open Complex Set

noncomputable section

def apm_a01A12_H : Set ℂ := {z : ℂ | 0 < z.im}

def apm_a01A12_wedgeSlit : Set ℂ :=
  {z : ℂ | z ≠ 0 ∧ |z.arg| < Real.pi / 4} \
    {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ z.im = 0}

def apm_a01A12_conformalMap (z : ℂ) : ℂ :=
  (1 - z ^ 2) ^ (1 / 4 : ℂ)

def apm_a01A12_mobius (a b c d : ℝ) (z : ℂ) : ℂ :=
  ((a : ℂ) * z + b) / ((c : ℂ) * z + d)

def apm_a01A12_ConformalBijOn (f : ℂ → ℂ) (U V : Set ℂ) : Prop :=
  Set.BijOn f U V ∧
    ∀ z ∈ U, DifferentiableAt ℂ f z ∧ fderiv ℂ f z ≠ 0

/-- The quadratic input to the fourth root has no zero in the upper
half-plane.  This is the first branch-domain obligation in the explicit
conformal-map proof. -/
lemma apm_a01A12_one_sub_sq_ne_zero {z : ℂ} (hz : z ∈ apm_a01A12_H) :
    1 - z ^ 2 ≠ 0 := by
  intro hzero
  have hfac : (1 - z) * (1 + z) = 0 := by
    calc
      (1 - z) * (1 + z) = 1 - z ^ 2 := by ring
      _ = 0 := hzero
  rcases mul_eq_zero.mp hfac with hminus | hplus
  · have hz1 : z = 1 := (sub_eq_zero.mp hminus).symm
    subst z
    simpa [apm_a01A12_H] using hz
  · have hzn1 : z = -1 := by
      apply eq_neg_of_add_eq_zero_left
      simpa [add_comm] using hplus
    subst z
    simpa [apm_a01A12_H] using hz

/-- The positive-determinant Möbius family contains the identity map. -/
lemma apm_a01A12_mobius_one_zero_zero_one (z : ℂ) :
    apm_a01A12_mobius 1 0 0 1 z = z := by
  simp [apm_a01A12_mobius]

lemma apm_a01A12_identity_parameters_positive :
    (0 : ℝ) < 1 * 1 - 0 * 0 := by norm_num

/-- Squaring sends the right half-plane away from the nonpositive real axis.
This is adapted from the earlier, range-only a01A12 artifact at commit
`fddc86c`. -/
lemma apm_a01A12_sq_mem_slitPlane {w : ℂ} (hw : 0 < w.re) :
    0 < (w ^ 2).re ∨ (w ^ 2).im ≠ 0 := by
  by_cases him : (w ^ 2).im = 0
  · left
    have him' : w.re * w.im + w.im * w.re = 0 := by
      simpa [pow_two, Complex.mul_im] using him
    have hmul : w.re * w.im = 0 := by nlinarith
    have hwim : w.im = 0 := (mul_eq_zero.mp hmul).resolve_left hw.ne'
    simp [pow_two, Complex.mul_re, hwim]
    exact hw.ne'
  · exact Or.inr him

theorem apm_a01a12 :
    apm_a01A12_ConformalBijOn apm_a01A12_conformalMap
      apm_a01A12_H apm_a01A12_wedgeSlit ∧
    ∀ g : ℂ → ℂ,
      apm_a01A12_ConformalBijOn g apm_a01A12_H apm_a01A12_wedgeSlit ↔
        ∃ a b c d : ℝ, 0 < a * d - b * c ∧
          Set.EqOn g
            (apm_a01A12_conformalMap ∘ apm_a01A12_mobius a b c d)
            apm_a01A12_H := by
  /-
  Closer hop 1 recovered the earlier range-only development from git history
  (`3ed025e`, `3fa3a92`, and `fddc86c`) and localized its algebraic core above:
  the quadratic input is nonzero on `H`, squaring the rotated half-plane avoids
  the principal branch cut, and the concrete Möbius family contains the
  identity with positive determinant.  Those earlier commits prove only that
  the displayed fourth root maps `H` into `wedgeSlit`; they do not prove
  surjectivity, injectivity of the principal fourth root on the exact slit
  plane, or its nonvanishing derivative.

  Searches of `LEMMA-INDEX.md`, every `ConstructionTargets/` module, solved and
  partial complex-analysis siblings, Mathlib's `UpperHalfPlane` Möbius-action
  sources, and git history found no classification theorem saying that every
  conformal self-bijection of the upper half-plane is a real fractional-linear
  map.  Mathlib's `SL(2, ℝ)` action supplies the forward family, not the converse
  automorphism classification.  Closing the frozen theorem therefore still
  requires (1) finishing the explicit biholomorphism, including an inverse on
  the wedge slit, and (2) developing that classical automorphism theorem (or an
  equivalent disk-automorphism classification).
  -/
  sorry
