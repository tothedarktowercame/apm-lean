import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import ConstructionTargets.T98A05FinalAdapter

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

lemma apm_t98a05_wedgeEval_eq_zero
    (alpha : apm_t98a05_Form 1) (halpha : apm_t98a05_isAlpha alpha)
    (beta : apm_t98a05_Form 2) (hbeta : apm_t98a05_isBeta beta)
    (x : apm_t98a05_E3) (v : Fin 3 → apm_t98a05_E3) :
    apm_t98a05_wedgeEval alpha beta x v = 0 := by
  simp only [apm_t98a05_wedgeEval]
  rw [halpha x ![v 0], halpha x ![v 1], halpha x ![v 2],
    hbeta x ![v 1, v 2], hbeta x ![v 0, v 2], hbeta x ![v 0, v 1]]
  simp
  ring

/-- Once the displayed ambient exterior-derivative formula is known, its
restriction to two circle-tangent vectors vanishes by a two-dimensional
determinant calculation. -/
lemma apm_t98a05_circleClosed_of_extDeriv_formula
    (alpha : apm_t98a05_Form 1)
    (hd : ∀ (x : apm_t98a05_E3) (v : Fin 2 → apm_t98a05_E3),
      extDeriv alpha x v =
        2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0)) :
    apm_t98a05_isCircleClosed alpha := by
  intro x v hv
  rw [hd]
  have ht0 := (hv 0).1
  have ht1 := (hv 1).1
  have hx := x.2.1
  have hA := congrArg (fun z : ℝ ↦ z * v 1 1) ht0
  have hB := congrArg (fun z : ℝ ↦ z * v 0 1) ht1
  have hC := congrArg (fun z : ℝ ↦ z * v 1 0) ht0
  have hD := congrArg (fun z : ℝ ↦ z * v 0 0) ht1
  have ha : (x : apm_t98a05_E3) 0 *
      (v 0 0 * v 1 1 - v 0 1 * v 1 0) = 0 := by
    nlinarith
  have hb : (x : apm_t98a05_E3) 1 *
      (v 0 0 * v 1 1 - v 0 1 * v 1 0) = 0 := by
    nlinarith
  nlinarith [sq_nonneg
    (v 0 0 * v 1 1 - v 0 1 * v 1 0)]

/-- Why this unblocks `apm_t98a05`: it packages the three missing coordinate
Fréchet-derivative calculations in exactly the exterior-derivative forms used
by the first three conjuncts of the main theorem. -/
theorem apm_t98A05_bridge_extDerivs
    (alpha : apm_t98a05_Form 1) (halpha : apm_t98a05_isAlpha alpha)
    (beta : apm_t98a05_Form 2) (hbeta : apm_t98a05_isBeta beta)
    (gamma : apm_t98a05_Form 3) (hgamma : apm_t98a05_isGamma gamma) :
    (∀ (x : apm_t98a05_E3) (v : Fin 2 → apm_t98a05_E3),
      extDeriv alpha x v =
        2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0)) ∧
    extDeriv beta = 3 • gamma ∧
    extDeriv gamma = 0 := by
  exact ConstructionTargets.T98A05FinalAdapter.bridge_extDerivs
    alpha halpha beta hbeta gamma hgamma

/-- Why this unblocks `apm_t98a05`: after the first bridge identifies
`d alpha`, this is precisely the remaining change-of-variables and elementary
area calculation on the standard oriented triangular parameter domain. -/
theorem apm_t98A05_bridge_simplexIntegral
    (alpha : apm_t98a05_Form 1) (halpha : apm_t98a05_isAlpha alpha) :
    apm_t98a05_orientedSimplexIntegral (extDeriv alpha) = 1 := by
  exact ConstructionTargets.T98A05FinalAdapter.bridge_simplexIntegral
    alpha halpha

/-- Why this unblocks `apm_t98a05`: this is the global period obstruction for
the angle form on the unit circle; it supplies exactly the final nonexactness
conjunct for every restriction satisfying the displayed pointwise formula. -/
theorem apm_t98A05_bridge_circle_not_differential
    (alpha : apm_t98a05_Form 1) (halpha : apm_t98a05_isAlpha alpha)
    (alpha' : apm_t98a05_CircleForm1)
    (halpha' : apm_t98a05_isRestriction alpha alpha') :
    ¬∃ f : apm_t98a05_circle → ℝ,
      apm_t98a05_IsDifferential f alpha' := by
  exact ConstructionTargets.T98A05FinalAdapter.bridge_circle_not_differential
    alpha halpha alpha' halpha'

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
  /-
  CLOSER HOP 3 goes beyond the previous statement-only artifact in two
  independent directions.  `apm_t98a05_wedgeEval_eq_zero` expands the frozen
  representatives of `alpha` and `beta` and proves the full fourth conjunct
  by polynomial normalization.  The lemma
  `apm_t98a05_circleClosed_of_extDeriv_formula` proves that the first frozen
  conjunct implies the sixth: two vectors tangent to the unit circle have
  zero determinant.  Thus neither the wedge cancellation nor the tangency
  argument remains open.

  Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, the related
  differential-form artifacts `t94J07`, `t03J06`, and `t02A05`, Mathlib's
  `DifferentialForm.Basic` and `DifferentialForm.VectorField` sources, and
  this bundle's git history found no theorem computing `extDeriv` directly
  from the pointwise coordinate specifications `isAlpha`, `isBeta`, and
  `isGamma`.  `extDeriv_apply` is the appropriate low-level route, but it
  still requires locally bundling and proving the Frechet derivatives of the
  alternating-map-valued coordinate formulas.  After those computations,
  the remaining bridges are the two-dimensional simplex integral and the
  nonexactness argument via a differentiable parametrization of the circle
  and its nonzero period.  The frozen statement is unchanged.
  -/
  obtain ⟨hda, hdb, hdg⟩ :=
    apm_t98A05_bridge_extDerivs alpha halpha beta hbeta gamma hgamma
  exact ⟨hda, hdb, hdg,
    apm_t98a05_wedgeEval_eq_zero alpha halpha beta hbeta,
    apm_t98A05_bridge_simplexIntegral alpha halpha,
    apm_t98a05_circleClosed_of_extDeriv_formula alpha hda,
    apm_t98A05_bridge_circle_not_differential alpha halpha alpha' halpha'⟩
