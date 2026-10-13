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

-- BEGIN SEAT AREA
lemma extDeriv_alpha_aux_fderiv (a b c : ℝ) (x w : V) :
    fderiv ℝ (fun y : V =>
      (y 2 ^ 2 + 2 * y 0 * y 2 + 4) * a +
      (y 0 - y 0 ^ 2) * b + (2 * y 1 * y 2) * c) x w =
      (2 * x 2 * w 2 + 2 * w 0 * x 2 + 2 * x 0 * w 2) * a +
      (w 0 - 2 * x 0 * w 0) * b +
      (2 * w 1 * x 2 + 2 * x 1 * w 2) * c := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) x
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) x
  have ha := (((h2.pow 2).add ((h0.const_mul 2).mul h2)).add_const 4).mul_const a
  have hb := (h0.sub (h0.pow 2)).mul_const b
  have hc := ((h1.const_mul 2).mul h2).mul_const c
  have h := (ha.add hb).add hc
  have hf := congrArg (fun L : V →L[ℝ] ℝ => L w) h.fderiv
  convert hf using 1 <;> simp [ContinuousLinearMap.proj_apply] <;> ring

lemma extDeriv_alpha_aux_wedge (i j : Fin 3) (v : Fin 2 → V) :
    coordinateWedge i j v = v 0 i * v 1 j - v 0 j * v 1 i := by
  change Matrix.det (fun k => ![v k i, v k j]) = _
  rw [Matrix.det_fin_two]
  rfl

lemma extDeriv_alpha_aux_volume (v : Fin 3 → V) :
    volumeForm v =
      v 0 0 * (v 1 1 * v 2 2 - v 1 2 * v 2 1) -
      v 0 1 * (v 1 0 * v 2 2 - v 1 2 * v 2 0) +
      v 0 2 * (v 1 0 * v 2 1 - v 1 1 * v 2 0) := by
  change Matrix.det v = _
  rw [Matrix.det_fin_three]
  ring

theorem extDeriv_alpha :
    extDeriv alpha = fun p => (2 * p 2 + 1) • volumeForm := by
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  have hd : Differentiable ℝ alpha := by
    unfold alpha
    fun_prop
  rw [extDeriv_apply (hd x)]
  rw [Fin.sum_univ_three]
  simp_rw [show ∀ i : Fin 3, (fun y => alpha y (i.removeNth v)) = fun y =>
      (y 2 ^ 2 + 2 * y 0 * y 2 + 4) * (coordinateWedge 0 1 (i.removeNth v)) +
      (y 0 - y 0 ^ 2) * (coordinateWedge 1 2 (i.removeNth v)) +
      (2 * y 1 * y 2) * (coordinateWedge 2 2 (i.removeNth v)) by
    intro i
    funext y
    simp [alpha]]
  simp_rw [extDeriv_alpha_aux_fderiv]
  simp_rw [extDeriv_alpha_aux_wedge]
  change _ = (2 * x 2 + 1) * volumeForm v
  rw [extDeriv_alpha_aux_volume]
  simp [Fin.removeNth, Fin.tail]
  have hs : v (Fin.succAbove (2 : Fin 3) (1 : Fin 2)) = v 1 := by congr 1
  rw [hs]
  ring
-- END SEAT AREA

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
