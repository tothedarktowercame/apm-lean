import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# APM t98A05 — differential forms in three-dimensional Euclidean space

## Statement repairs

Since `dα` is a two-form, `Γ` must be two-dimensional. The phrase “region
that lies between the coordinate planes and the standard 2-simplex” is read
as the standard triangular 2-simplex itself:
`x,y,z ≥ 0` and `x+y+z=1`. It is oriented by the normal `(1,1,1)`.

The former opaque form operations are replaced by explicit definitions:
wedge evaluation uses the alternating shuffle formula, the simplex integral
is the Lebesgue integral of the pulled-back form under its affine
parameterization, circle closedness restricts the genuine ambient `extDeriv`
to tangent vectors, and exactness is equality with derivatives along every
differentiable circle-valued curve.

## Encoding questions

The three original forms, their exterior derivatives, the simplex and its
orientation, the actual unit circle, and the restricted one-form are explicit.
-/

open MeasureTheory Set

noncomputable section

abbrev apm_t98a05_E3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t98a05_E2 := EuclideanSpace ℝ (Fin 2)
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

def apm_t98a05_isRestriction
    (alpha : apm_t98a05_Form 1) (alpha' : apm_t98a05_CircleForm1) : Prop :=
  ∀ (x : apm_t98a05_circle) (v : apm_t98a05_E3),
    alpha' x v = alpha x (fun _ ↦ v)

def apm_t98a05_wedgeEval
    (alpha : apm_t98a05_Form 1) (beta : apm_t98a05_Form 2)
    (x : apm_t98a05_E3) (v : Fin 3 → apm_t98a05_E3) : ℝ :=
  alpha x ![v 0] * beta x ![v 1, v 2] -
    alpha x ![v 1] * beta x ![v 0, v 2] +
    alpha x ![v 2] * beta x ![v 0, v 1]

def apm_t98a05_simplexParameterDomain : Set apm_t98a05_E2 :=
  {u | 0 ≤ u 0 ∧ 0 ≤ u 1 ∧ u 0 + u 1 ≤ 1}

def apm_t98a05_simplexParameter (u : apm_t98a05_E2) : apm_t98a05_E3 :=
  WithLp.toLp 2 ![u 0, u 1, 1 - u 0 - u 1]

def apm_t98a05_simplexTangent0 : apm_t98a05_E3 :=
  WithLp.toLp 2 ![(1 : ℝ), 0, -1]

def apm_t98a05_simplexTangent1 : apm_t98a05_E3 :=
  WithLp.toLp 2 ![(0 : ℝ), 1, -1]

def apm_t98a05_orientedSimplexIntegral
    (omega : apm_t98a05_Form 2) : ℝ :=
  ∫ u in apm_t98a05_simplexParameterDomain,
    omega (apm_t98a05_simplexParameter u)
      ![apm_t98a05_simplexTangent0, apm_t98a05_simplexTangent1]

def apm_t98a05_isCircleTangent
    (x : apm_t98a05_circle) (v : apm_t98a05_E3) : Prop :=
  (x : apm_t98a05_E3) 0 * v 0 + (x : apm_t98a05_E3) 1 * v 1 = 0 ∧
    v 2 = 0

def apm_t98a05_isCircleClosed (alpha : apm_t98a05_Form 1) : Prop :=
  ∀ (x : apm_t98a05_circle) (v : Fin 2 → apm_t98a05_E3),
    (∀ i, apm_t98a05_isCircleTangent x (v i)) →
      extDeriv alpha x v = 0

def apm_t98a05_IsDifferential
    (f : apm_t98a05_circle → ℝ) (alpha' : apm_t98a05_CircleForm1) : Prop :=
  ∀ c : ℝ → apm_t98a05_circle,
    Differentiable ℝ (fun t => (c t : apm_t98a05_E3)) →
    Differentiable ℝ (fun t => f (c t)) ∧
      ∀ t : ℝ,
        deriv (fun s => f (c s)) t =
          alpha' (c t) (deriv (fun s => (c s : apm_t98a05_E3)) t)

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
    (∀ (x : apm_t98a05_E3) (v : Fin 3 → apm_t98a05_E3),
      apm_t98a05_wedgeEval alpha beta x v = 0) ∧
    apm_t98a05_orientedSimplexIntegral (extDeriv alpha) = 1 ∧
    apm_t98a05_isCircleClosed alpha ∧
    ¬∃ f : apm_t98a05_circle → ℝ,
      apm_t98a05_IsDifferential f alpha' := by
  sorry
