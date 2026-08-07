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
  sorry
