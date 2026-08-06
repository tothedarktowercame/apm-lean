import Mathlib

/-! # APM t01A06: differential forms and periods on an embedded torus

## Statement repairs

None.

## Encoding note

Mathlib does not yet bundle integration of differential forms over manifolds.
The surface integral is encoded by the pullback of the printed two-form along
the standard outward-oriented torus parametrization.  An ambient one-form is
encoded without loss as a smooth field of continuous linear covectors on
`ℝ³`; closedness is symmetry of its derivative.
-/

open MeasureTheory
open scoped ContDiff

noncomputable section

abbrev t01A06Point := EuclideanSpace ℝ (Fin 3)
abbrev t01A06OneForm := t01A06Point → (t01A06Point →L[ℝ] ℝ)

def t01A06Torus (R r : ℝ) : Set t01A06Point :=
  {p | (Real.sqrt (p 0 ^ 2 + p 1 ^ 2) - R) ^ 2 + p 2 ^ 2 = r ^ 2}

def t01A06Param (R r u v : ℝ) : t01A06Point :=
  EuclideanSpace.equiv (Fin 3) ℝ |>.symm
    ![(R + r * Real.cos v) * Real.cos u,
      (R + r * Real.cos v) * Real.sin u,
      r * Real.sin v]

def t01A06OmegaPullback (R r u v : ℝ) : ℝ :=
  r * (R + r * Real.cos v) ^ 2 * Real.sin u ^ 2 * Real.cos v

def t01A06SurfaceIntegral (R r : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..2 * Real.pi,
    ∫ v in (0 : ℝ)..2 * Real.pi, t01A06OmegaPullback R r u v

def IsT01A06ClosedOneForm (η : t01A06OneForm) : Prop :=
  ContDiff ℝ ∞ η ∧ ∀ (p v w : t01A06Point),
    fderiv ℝ η p v w = fderiv ℝ η p w v

def IsT01A06LoopOnTorus (R r : ℝ) (γ : ℝ → t01A06Point) : Prop :=
  ContDiff ℝ ∞ γ ∧
  (∀ t : ℝ, γ (t + 2 * Real.pi) = γ t) ∧
  ∀ t : ℝ, γ t ∈ t01A06Torus R r

def t01A06LineIntegral (η : t01A06OneForm) (γ : ℝ → t01A06Point) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi, η (γ t) (deriv γ t)

theorem apm_t01a06 :
    (∀ R r : ℝ, R > r → r > 0 →
      t01A06SurfaceIntegral R r = 2 * Real.pi ^ 2 * R * r ^ 2) ∧
    (∀ R r : ℝ, R > r → r > 0 →
      ¬∃ (η : t01A06OneForm) (γ : ℝ → t01A06Point),
        IsT01A06ClosedOneForm η ∧ IsT01A06LoopOnTorus R r γ ∧
        t01A06LineIntegral η γ ≠ 0) := by
  sorry
