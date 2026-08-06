import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# APM t98A05

## Statement repairs

Since `dα` is a two-form, `Γ` must be two-dimensional. The phrase “region
that lies between the coordinate planes and the standard 2-simplex” is read
as the standard triangular 2-simplex itself:
`x,y,z ≥ 0` and `x+y+z=1`. It is oriented by the normal `(1,1,1)`.

## Encoding questions

Mathlib provides ambient alternating differential forms and their exterior
derivative, but not wedge products, oriented integration over an embedded
simplex, or intrinsic exterior differentiation and exactness on the circle in
a common manifold API. Those operations are isolated as typed placeholders.
The three original forms, their exterior derivatives, the simplex and its
orientation, the actual unit circle, and the restricted one-form remain
explicit.
-/

noncomputable section

abbrev apm_t98a05_E3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t98a05_Form (k : ℕ) :=
  apm_t98a05_E3 → apm_t98a05_E3 [⋀^Fin k]→L[ℝ] ℝ

def apm_t98a05_isAlpha (alpha : apm_t98a05_Form 1) : Prop :=
  ∀ (x : apm_t98a05_E3) (v : Fin 1 → apm_t98a05_E3),
    alpha x v = x 0 * v 0 1 - x 1 * v 0 0

def apm_t98a05_isBeta (beta : apm_t98a05_Form 2) : Prop :=
  ∀ (x : apm_t98a05_E3) (v : Fin 2 → apm_t98a05_E3),
    beta x v =
      x 0 * (v 0 1 * v 1 2 - v 0 2 * v 1 1) +
      x 1 * (v 0 2 * v 1 0 - v 0 0 * v 1 2) +
      x 2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0)

def apm_t98a05_isGamma (gamma : apm_t98a05_Form 3) : Prop :=
  ∀ (_x : apm_t98a05_E3) (v : Fin 3 → apm_t98a05_E3),
    gamma _x v =
      v 0 0 * (v 1 1 * v 2 2 - v 1 2 * v 2 1) -
      v 0 1 * (v 1 0 * v 2 2 - v 1 2 * v 2 0) +
      v 0 2 * (v 1 0 * v 2 1 - v 1 1 * v 2 0)

def apm_t98a05_simplex : Set apm_t98a05_E3 :=
  {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2 ∧ x 0 + x 1 + x 2 = 1}

def apm_t98a05_simplexNormal : apm_t98a05_E3 :=
  WithLp.toLp 2 ![(1 : ℝ), 1, 1]

abbrev apm_t98a05_circle :=
  {x : apm_t98a05_E3 // x 0 ^ 2 + x 1 ^ 2 = 1 ∧ x 2 = 0}

abbrev apm_t98a05_CircleForm1 :=
  apm_t98a05_circle → apm_t98a05_E3 →L[ℝ] ℝ

abbrev apm_t98a05_CircleForm2 :=
  apm_t98a05_circle → apm_t98a05_E3 [⋀^Fin 2]→L[ℝ] ℝ

def apm_t98a05_isRestriction
    (alpha : apm_t98a05_Form 1) (alpha' : apm_t98a05_CircleForm1) : Prop :=
  ∀ (x : apm_t98a05_circle) (v : apm_t98a05_E3),
    alpha' x v = alpha x (fun _ ↦ v)

opaque apm_t98a05_wedge
    (alpha : apm_t98a05_Form 1) (beta : apm_t98a05_Form 2) :
    apm_t98a05_Form 3

opaque apm_t98a05_orientedIntegral
    (omega : apm_t98a05_Form 2) (surface : Set apm_t98a05_E3)
    (positiveNormal : apm_t98a05_E3) : ℝ

opaque apm_t98a05_circleExtDeriv
    (alpha' : apm_t98a05_CircleForm1) : apm_t98a05_CircleForm2

opaque apm_t98a05_IsDifferential
    (f : apm_t98a05_circle → ℝ) (alpha' : apm_t98a05_CircleForm1) : Prop

theorem apm_t98a05
    (alpha : apm_t98a05_Form 1) (halpha : apm_t98a05_isAlpha alpha)
    (beta : apm_t98a05_Form 2) (hbeta : apm_t98a05_isBeta beta)
    (gamma : apm_t98a05_Form 3) (hgamma : apm_t98a05_isGamma gamma)
    (alpha' : apm_t98a05_CircleForm1)
    (halpha' : apm_t98a05_isRestriction alpha alpha') :
    (∀ (x : apm_t98a05_E3) (v : Fin 2 → apm_t98a05_E3),
      extDeriv alpha x v =
        2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0)) ∧
    extDeriv beta = 3 • gamma ∧
    extDeriv gamma = 0 ∧
    apm_t98a05_wedge alpha beta = 0 ∧
    apm_t98a05_orientedIntegral
      (extDeriv alpha) apm_t98a05_simplex apm_t98a05_simplexNormal = 1 ∧
    apm_t98a05_circleExtDeriv alpha' = 0 ∧
    ¬∃ f : apm_t98a05_circle → ℝ,
      apm_t98a05_IsDifferential f alpha' := by
  sorry
