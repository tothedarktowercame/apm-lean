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

theorem apm_a01a12 :
    apm_a01A12_ConformalBijOn apm_a01A12_conformalMap
      apm_a01A12_H apm_a01A12_wedgeSlit ∧
    ∀ g : ℂ → ℂ,
      apm_a01A12_ConformalBijOn g apm_a01A12_H apm_a01A12_wedgeSlit ↔
        ∃ a b c d : ℝ, 0 < a * d - b * c ∧
          Set.EqOn g
            (apm_a01A12_conformalMap ∘ apm_a01A12_mobius a b c d)
            apm_a01A12_H := by
  sorry
