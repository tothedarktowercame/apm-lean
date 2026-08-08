import Mathlib

/-!
# APM t02A07

## Statement repairs

The defining equation for `X` repeats `(x²)²` and omits `(x¹)²`. It is
repaired to the standard unit-sphere equation
`(x¹)² + (x²)² + (x³)² + (x⁴)² = 1`, as required by the phrase “unit sphere”.

## Encoding questions

The submanifold claim is encoded by the regular-value criterion for the two
actual constraint functions in `ℝ⁴`, giving dimension `4 - 2 = 2`.
Transversality is the concrete tangent-space condition: at every intersection,
the image of the derivative of the displayed family plus the kernel of the
constraint derivative is the full ambient space.
-/

noncomputable section

abbrev apm_t02a07_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t02a07_E3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t02a07_E4 := EuclideanSpace ℝ (Fin 4)

def apm_t02a07_X : Set apm_t02a07_E4 :=
  Metric.sphere 0 1

def apm_t02a07_Z : Set apm_t02a07_E4 :=
  {x | x ∈ apm_t02a07_X ∧ x 2 * x 3 = (1 : ℝ) / 4}

abbrev apm_t02a07_S2 := Metric.sphere (0 : apm_t02a07_E3) 1
abbrev apm_t02a07_parameterCircle := Metric.sphere (0 : apm_t02a07_E2) 1

def apm_t02a07_family
    (parameter : apm_t02a07_parameterCircle) (y : apm_t02a07_S2) :
    apm_t02a07_E4 :=
  WithLp.toLp 2
    ![y.1 0 * parameter.1 0, parameter.1 1, y.1 1 * parameter.1 0,
      y.1 2 * parameter.1 0]

def apm_t02a07_constraints (x : apm_t02a07_E4) : apm_t02a07_E2 :=
  WithLp.toLp 2
    ![‖x‖ ^ 2 - 1, x 2 * x 3 - (1 : ℝ) / 4]

def apm_t02a07_IsRegularDimensionTwo : Prop :=
  ∀ x ∈ apm_t02a07_Z,
    Function.Surjective (fderiv ℝ apm_t02a07_constraints x)

def apm_t02a07_sphereTangent (y : apm_t02a07_S2) : Submodule ℝ apm_t02a07_E3 :=
  (Submodule.span ℝ ({(y : apm_t02a07_E3)} : Set apm_t02a07_E3)).orthogonal

def apm_t02a07_familyAmbient
    (parameter : apm_t02a07_parameterCircle) (y : apm_t02a07_E3) :
    apm_t02a07_E4 :=
  WithLp.toLp 2
    ![y 0 * parameter.1 0, parameter.1 1, y 1 * parameter.1 0,
      y 2 * parameter.1 0]

@[simp] lemma apm_t02a07_family_eq_familyAmbient
    (parameter : apm_t02a07_parameterCircle) (y : apm_t02a07_S2) :
    apm_t02a07_family parameter y =
      apm_t02a07_familyAmbient parameter y := rfl

/-- The displayed family lands in the unit sphere. This discharges the finite
coordinate normalization independently of the transversality argument. -/
lemma apm_t02a07_family_mem_X
    (parameter : apm_t02a07_parameterCircle) (y : apm_t02a07_S2) :
    apm_t02a07_family parameter y ∈ apm_t02a07_X := by
  have hp : ‖(parameter : apm_t02a07_E2)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using parameter.property
  have hy : ‖(y : apm_t02a07_E3)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using y.property
  have hp2 := congrArg (fun z : ℝ => z ^ 2) hp
  have hy2 := congrArg (fun z : ℝ => z ^ 2) hy
  dsimp only at hp2 hy2
  rw [EuclideanSpace.norm_sq_eq] at hp2 hy2
  simp [Fin.sum_univ_succ] at hp2 hy2
  rw [apm_t02a07_X, Metric.mem_sphere, dist_zero_right]
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
  rw [EuclideanSpace.norm_sq_eq]
  simp [apm_t02a07_family, Fin.sum_univ_succ]
  nlinarith

def apm_t02a07_tangentZ (x : apm_t02a07_E4) : Submodule ℝ apm_t02a07_E4 :=
  LinearMap.ker (fderiv ℝ apm_t02a07_constraints x).toLinearMap

def apm_t02a07_IsTransverse (parameter : apm_t02a07_parameterCircle) : Prop :=
  ∀ y : apm_t02a07_S2, apm_t02a07_family parameter y ∈ apm_t02a07_Z →
    Submodule.map
        (fderiv ℝ (apm_t02a07_familyAmbient parameter) y).toLinearMap
        (apm_t02a07_sphereTangent y) ⊔
      apm_t02a07_tangentZ (apm_t02a07_family parameter y) = ⊤

theorem apm_t02a07 :
    apm_t02a07_IsRegularDimensionTwo ∧
    (∀ parameter : apm_t02a07_parameterCircle,
      Set.range (apm_t02a07_family parameter) ⊆ apm_t02a07_X) ∧
    Dense {parameter : apm_t02a07_parameterCircle |
      apm_t02a07_IsTransverse parameter} := by
  /-
  CLOSER HOP 1 boundary. The restricted family is now explicitly connected to
  its ambient differentiable extension by
  `apm_t02a07_family_eq_familyAmbient`, eliminating a later coercion bridge.

  The range-in-sphere conjunct is an explicit norm calculation: using
  `EuclideanSpace.norm_sq_eq`, the squared norm of the four displayed
  coordinates factors as
  `parameter₀² * ‖y‖² + parameter₁² = 1`. Mathlib supplies the norm identity,
  but the required `Fin 3`/`Fin 4` sum normalization and `WithLp.toLp`
  coordinate simplification remain to be assembled locally.

  Regularity requires computing the derivative of both constraints. At a
  point with `x₂*x₃ = 1/4`, the second constraint forces `x₂,x₃ ≠ 0`; the norm
  gradient and product gradient are then linearly independent, yielding
  surjectivity onto `ℝ²`. No searched lemma packages this coordinate Jacobian
  argument for the frozen `fderiv` expression.

  Finally, the density statement is the parametric transversality theorem.
  Mathlib contains Sard's theorem and elementary tangent/submodule machinery,
  but searches found no Thom/parametric-transversality theorem. A direct route
  would have to classify the exceptional parameters by solving the displayed
  derivative-rank equations and prove their complement dense in the circle.
  Searches covered `LEMMA-INDEX.md`, all `ConstructionTargets/`, sibling
  `t94A06`, all closed transversality artifacts, Mathlib's Sard, fderiv,
  Euclidean norm, submodule, and density APIs, and git history. None supplies
  the parameter-density assembly, so the statement remains open.

  CLOSER HOP 2 goes beyond that search boundary by completing the entire
  range-in-sphere conjunct as `apm_t02a07_family_mem_X`. The proof extracts
  the two unit-norm equations from the sphere subtypes, expands them with
  `EuclideanSpace.norm_sq_eq`, normalizes the `Fin 2`, `Fin 3`, and `Fin 4`
  sums, and finishes the displayed coordinate identity by `nlinarith`.
  Thus neither `WithLp.toLp` simplification nor the finite-coordinate norm
  calculation remains open. Targeted reinspection of `t94A06`, the repository
  transversality users, `LEMMA-INDEX.md`, `ConstructionTargets/`, and Mathlib's
  Sard/density APIs still found no parametric-transversality theorem. The live
  bridge is now only the explicit constraint-Jacobian surjectivity proof and
  the exceptional-parameter classification/density argument.
  -/
  sorry
