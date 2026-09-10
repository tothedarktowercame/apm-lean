import Mathlib
import ConstructionTargets.CoordinateSurfaceForms

/-! # t99J06: the literal 2-form and its integral on the oriented cone

The source's last term is dz wedge dz. It is retained literally as a genuine
alternating form, hence vanishes; no silent typo repair is made. The derivative
is Mathlib's exterior derivative. The integral evaluates the form on the two
actual parameter derivatives with orientation dθ wedge dz. The conclusion also
certifies the printed cone as the parameter image, single coverage and immersion
away from the seam/apex, and positivity of the dx wedge dy integral. These are
explicit construction obligations for the parametrized integration, not an
assumed scalar standing in for a surface integral.
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
  sorry
