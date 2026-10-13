import Mathlib
import ConstructionTargets.CoordinateSurfaceForms

/-! # Blueprint for t99J06

The literal `dz wedge dz` term is retained (and vanishes by alternation).
The auxiliary formulas below are shared interfaces for the immersion and
integration packets.
-/

open ConstructionTargets.CoordinateSurfaceForms Set
noncomputable section
namespace T99J06

def alpha (p : V) : V [⋀^Fin 2]→L[ℝ] ℝ :=
  (p 2 ^ 2 + 2 * p 0 * p 2 + 4) • coordinateWedge 0 1 +
    (p 0 - p 0 ^ 2) • coordinateWedge 1 2 +
    (2 * p 1 * p 2) • coordinateWedge 2 2

def cone : Set V := {p | p 0 ^ 2 + p 1 ^ 2 - (p 2 - 1)^2 = 0 ∧
  0 ≤ p 2 ∧ p 2 ≤ 1}

def parameters : Set Parameters := {p | 0 ≤ p 0 ∧ p 0 ≤ 2 * Real.pi ∧
  0 ≤ p 1 ∧ p 1 ≤ 1}

def interiorParameters : Set Parameters := {p | 0 < p 0 ∧ p 0 < 2 * Real.pi ∧
  0 < p 1 ∧ p 1 < 1}

def parametrization (p : Parameters) : V :=
  ![(1 - p 1) * Real.cos (p 0), (1 - p 1) * Real.sin (p 0), p 1]

/-- The expected derivative of the cone parametrization, written without
bundled derivatives so that both later consumers can rewrite by it. -/
def parameterDerivative (p q : Parameters) : V :=
  ![-q 1 * Real.cos (p 0) - (1 - p 1) * Real.sin (p 0) * q 0,
    -q 1 * Real.sin (p 0) + (1 - p 1) * Real.cos (p 0) * q 0,
    q 1]

/-- The scalar coefficient obtained by pulling `alpha` back to the ordered
parameter basis `(d/dθ, d/dz)`. -/
def alphaPullbackFormula (p : Parameters) : ℝ :=
  (p 1 ^ 2 + 2 * ((1 - p 1) * Real.cos (p 0)) * p 1 + 4) * (1 - p 1) +
    (((1 - p 1) * Real.cos (p 0)) -
      ((1 - p 1) * Real.cos (p 0)) ^ 2) *
      ((1 - p 1) * Real.cos (p 0))

theorem extDeriv_alpha :
    extDeriv alpha = fun p => (2 * p 2 + 1) • volumeForm := by
  sorry

theorem image_parametrization_eq_cone :
    parametrization '' parameters = cone := by
  sorry

theorem injOn_parametrization_interior :
    Set.InjOn parametrization interiorParameters := by
  sorry

theorem fderiv_parametrization_formula :
    ∀ p q, fderiv ℝ parametrization p q = parameterDerivative p q := by
  sorry

theorem fderiv_parametrization_injective_on_interior
    (hderiv : ∀ p q, fderiv ℝ parametrization p q = parameterDerivative p q) :
    ∀ p ∈ interiorParameters, Function.Injective (fderiv ℝ parametrization p) := by
  sorry

theorem pullback_coefficients
    (hderiv : ∀ p q, fderiv ℝ parametrization p q = parameterDerivative p q) :
    (∀ p, pullbackCoefficient (fun _ => coordinateWedge 0 1) parametrization p =
      1 - p 1) ∧
    (∀ p, pullbackCoefficient alpha parametrization p = alphaPullbackFormula p) := by
  sorry

theorem rectangle_integrals
    (hxy : ∀ p, pullbackCoefficient (fun _ => coordinateWedge 0 1) parametrization p =
      1 - p 1)
    (halpha : ∀ p, pullbackCoefficient alpha parametrization p = alphaPullbackFormula p) :
    0 < rectangleIntegral (fun _ => coordinateWedge 0 1) parametrization
      0 (2 * Real.pi) 0 1 ∧
    rectangleIntegral alpha parametrization 0 (2 * Real.pi) 0 1 = 9 * Real.pi / 2 := by
  sorry

end T99J06
open T99J06

theorem apm_t99j06 :
    (extDeriv alpha = fun p => (2 * p 2 + 1) • volumeForm) ∧
    parametrization '' parameters = cone ∧
    Set.InjOn parametrization interiorParameters ∧
    (∀ p ∈ interiorParameters, Function.Injective (fderiv ℝ parametrization p)) ∧
    0 < rectangleIntegral (fun _ => coordinateWedge 0 1) parametrization
      0 (2 * Real.pi) 0 1 ∧
    rectangleIntegral alpha parametrization 0 (2 * Real.pi) 0 1 = 9 * Real.pi / 2 := by
  have hderiv := fderiv_parametrization_formula
  have himmersion := fderiv_parametrization_injective_on_interior hderiv
  obtain ⟨hxy, halpha⟩ := pullback_coefficients hderiv
  obtain ⟨hpositive, hintegral⟩ := rectangle_integrals hxy halpha
  exact ⟨extDeriv_alpha, image_parametrization_eq_cone,
    injOn_parametrization_interior, himmersion, hpositive, hintegral⟩

#print axioms apm_t99j06
