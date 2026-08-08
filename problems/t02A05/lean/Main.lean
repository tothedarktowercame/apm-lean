import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# APM t02A05

## Statement repairs

None.

## Encoding questions

The outward-oriented integral is encoded concretely: coordinate basis vectors
are orthogonally projected to each tangent plane, the form's coefficient
relative to the outward unit normal is extracted, and that coefficient is
integrated against two-dimensional Hausdorff measure on the actual sphere.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

abbrev apm_t02a05_E3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t02a05_Form2 :=
  apm_t02a05_E3 → apm_t02a05_E3 [⋀^Fin 2]→L[ℝ] ℝ

def apm_t02a05_isOmega (omega : apm_t02a05_Form2) : Prop :=
  ∀ (x : apm_t02a05_E3) (v : Fin 2 → apm_t02a05_E3),
    omega x v =
      (x 0 - 1) ^ 3 * (v 0 1 * v 1 2 - v 0 2 * v 1 1) +
      (x 1 - 2) ^ 3 * (v 0 2 * v 1 0 - v 0 0 * v 1 2) +
      (x 2 - 3) * (v 0 0 * v 1 1 - v 0 1 * v 1 0)

def apm_t02a05_unitSphere (c : apm_t02a05_E3) : Set apm_t02a05_E3 :=
  Metric.sphere c 1

def apm_t02a05_sphereTangent (c : apm_t02a05_E3)
    (q : Metric.sphere c 1) : Submodule ℝ apm_t02a05_E3 :=
  (Submodule.span ℝ ({(q : apm_t02a05_E3) - c} : Set apm_t02a05_E3)).orthogonal

def apm_t02a05_tangentProjection (c : apm_t02a05_E3)
    (q : Metric.sphere c 1) (i : Fin 3) : apm_t02a05_sphereTangent c q :=
  (apm_t02a05_sphereTangent c q).orthogonalProjection
    (EuclideanSpace.single i 1)

/-- A point of the unit sphere has a unit radial normal. -/
lemma apm_t02a05_sphere_normal_norm (c : apm_t02a05_E3)
    (q : Metric.sphere c 1) :
    ‖(q : apm_t02a05_E3) - c‖ = 1 := by
  simpa [Metric.mem_sphere, dist_eq_norm] using q.property

/-- The projected coordinate vectors are orthogonal to the radial normal.
This is the pointwise tangent-plane fact needed before expanding the flux
coefficient into coordinate moments. -/
lemma apm_t02a05_inner_normal_tangentProjection (c : apm_t02a05_E3)
    (q : Metric.sphere c 1) (i : Fin 3) :
    @inner ℝ apm_t02a05_E3 _ ((q : apm_t02a05_E3) - c)
        (apm_t02a05_tangentProjection c q i) = 0 := by
  have hn : (q : apm_t02a05_E3) - c ∈
      Submodule.span ℝ ({(q : apm_t02a05_E3) - c} : Set apm_t02a05_E3) :=
    Submodule.subset_span (Set.mem_singleton _)
  exact Submodule.inner_right_of_mem_orthogonal hn
    (apm_t02a05_tangentProjection c q i).property

def apm_t02a05_orientedCoefficient (omega : apm_t02a05_Form2)
    (c : apm_t02a05_E3) (q : Metric.sphere c 1) : ℝ :=
  ((q : apm_t02a05_E3) - c) 0 * omega q
      ![apm_t02a05_tangentProjection c q 1, apm_t02a05_tangentProjection c q 2] -
  ((q : apm_t02a05_E3) - c) 1 * omega q
      ![apm_t02a05_tangentProjection c q 0, apm_t02a05_tangentProjection c q 2] +
  ((q : apm_t02a05_E3) - c) 2 * omega q
      ![apm_t02a05_tangentProjection c q 0, apm_t02a05_tangentProjection c q 1]

def apm_t02a05_outwardSphereIntegral
    (omega : apm_t02a05_Form2) (c : apm_t02a05_E3) : ℝ :=
  ∫ q : Metric.sphere c 1, apm_t02a05_orientedCoefficient omega c q ∂μH[2]

/-- The purely algebraic optimization step after the flux has been reduced to
its explicit quadratic expression in the center. -/
lemma apm_t02a05_quadratic_minimum (a b : ℝ) :
    44 * Real.pi / 15 ≤
        44 * Real.pi / 15 +
          4 * Real.pi * ((a - 1) ^ 2 + (b - 2) ^ 2) ∧
    (44 * Real.pi / 15 +
          4 * Real.pi * ((a - 1) ^ 2 + (b - 2) ^ 2) =
        44 * Real.pi / 15 ↔ a = 1 ∧ b = 2) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have ha : 0 ≤ (a - 1) ^ 2 := sq_nonneg _
  have hb : 0 ≤ (b - 2) ^ 2 := sq_nonneg _
  constructor
  · nlinarith
  · constructor
    · intro h
      have hmul : 4 * Real.pi * ((a - 1) ^ 2 + (b - 2) ^ 2) = 0 := by
        linarith
      have hcoeff : 4 * Real.pi ≠ 0 :=
        mul_ne_zero (by norm_num) (ne_of_gt hpi)
      have hsum : (a - 1) ^ 2 + (b - 2) ^ 2 = 0 :=
        (mul_eq_zero.mp hmul).resolve_left hcoeff
      constructor <;> nlinarith
    · rintro ⟨rfl, rfl⟩
      ring

/-- Reused from closed artifact `t92J09`: the unit three-ball volume. -/
lemma apm_t02a05_volume_unit_ball :
    (volume (Metric.ball (0 : apm_t02a05_E3) 1)).toReal =
      (4 / 3 : ℝ) * Real.pi := by
  have hvol :=
    EuclideanSpace.volume_ball_fin_three (0 : apm_t02a05_E3) (1 : ℝ)
  have hone : (ENNReal.ofReal (1 : ℝ)) ^ (3 : ℕ) = (1 : ENNReal) := by norm_num
  have hπ : Real.pi * 4 / 3 = (4 / 3 : ℝ) * Real.pi := by ring
  have hvol' : volume (Metric.ball (0 : apm_t02a05_E3) 1) =
      ENNReal.ofReal ((4 / 3 : ℝ) * Real.pi) := by
    simpa [hone, hπ] using hvol
  have hpos : 0 ≤ (4 / 3 : ℝ) * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_nonneg
  have := congrArg ENNReal.toReal hvol'
  simpa [ENNReal.toReal_ofReal, hpos] using this

theorem apm_t02a05
    (omega : apm_t02a05_Form2) (homega : apm_t02a05_isOmega omega) :
    (∀ c : apm_t02a05_E3,
      44 * Real.pi / 15 ≤
        apm_t02a05_outwardSphereIntegral omega c) ∧
    (∀ c : apm_t02a05_E3,
      apm_t02a05_outwardSphereIntegral omega c = 44 * Real.pi / 15 ↔
        c 0 = 1 ∧ c 1 = 2) := by
  /-
  Boundary (closer hop 1): the optimization layer is now completely compiled
  in `apm_t02a05_quadratic_minimum`. Once the geometric integral is shown to
  equal
  `44 * pi / 15 + 4 * pi * ((c 0 - 1)^2 + (c 1 - 2)^2)`, positivity of `pi`
  and the sum-of-squares equality give both the lower bound and the exact
  minimizing line, with no condition on `c 2`.

  The remaining bridge is that exact flux formula. The informal proof uses
  Stokes/divergence to replace the custom Hausdorff-measure boundary integral
  by the integral of
  `3*(x₀-1)^2 + 3*(x₁-2)^2 + 1` on the translated unit ball, followed by
  the ball volume and second-coordinate moments. Mathlib's differential-form
  API has `extDeriv`, and `ConstructionTargets.RadialIntegrationR3` handles
  radial volume integrals, but neither connects `extDeriv` to this custom
  tangent-projection coefficient integral over `μH[2]`. Direct evaluation
  requires proving the orthogonal-projection coordinate identity, translation
  invariance of Hausdorff surface measure, and the needed sphere moments.
  Searches of `LEMMA-INDEX.md`, all construction modules, related artifacts
  `t92J09` and `t01J06`, git history, and Mathlib's Stokes, divergence,
  Hausdorff-measure, sphere-integral, and Euclidean moment APIs found no
  packaged route; both related artifacts retain the same unresolved bridge.

  Closer hop 2 goes beyond the Stokes-only route by investigating direct
  moments. The closed `t92J09` unit-ball volume result is now compiled locally
  as `apm_t02a05_volume_unit_ball`, and Mathlib provides translation invariance
  of ambient Hausdorff measure through `IsometryEquiv.vaddConst`. However, the
  frozen integral is over a sphere subtype and evaluates orthogonal projections
  into point-dependent tangent submodules. No theorem identifies that subtype
  measure/integrand with `Measure.toSphere` or a translated ambient surface
  measure. The remaining expansion also needs the coordinate moment
  `∫ x in ball 0 1, (x i)^2 = 4*pi/15`; renewed searches of `HaarToSphere`,
  rotational invariance, Euclidean volume, and polynomial moment APIs found no
  packaged result. The direct route is thus narrowed to the projected-flux
  identity, surface-measure transport, and this second-moment calculation.

  Closer hop 3 completes the first pointwise layer of that direct route.
  `apm_t02a05_sphere_normal_norm` proves that the encoded radial normal is
  unit, and `apm_t02a05_inner_normal_tangentProjection` proves directly from
  `Submodule.inner_right_of_mem_orthogonal` that every projected coordinate
  vector is tangent. A targeted inspection of the orthogonal-projection API
  found membership/self/zero lemmas but no formula for projection onto the
  orthogonal complement of a singleton span, so deriving
  `P(eᵢ) = eᵢ - nᵢ n` remains local algebra. Searches of `LEMMA-INDEX.md`,
  `ConstructionTargets/`, and Mathlib's sphere/Hausdorff sources again found
  no bridge between the frozen subtype `μH[2]` integral and `Measure.toSphere`,
  and no coordinate second-moment theorem. The bridge therefore remains open
  at the explicit projection formula, surface-measure identification, and
  moment evaluation; the new lemmas discharge the radial/tangency premises.
  -/
  sorry
