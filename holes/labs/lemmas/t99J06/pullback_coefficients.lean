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
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases hq with ⟨hθ0, hθ2π, hz0, hz1⟩
    refine ⟨?_, hz0, hz1⟩
    simp only [parametrization, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]
    have htrig : Real.cos (q 0) ^ 2 + Real.sin (q 0) ^ 2 = 1 := by
      simpa [add_comm] using Real.sin_sq_add_cos_sq (q 0)
    change ((1 - q 1) * Real.cos (q 0)) ^ 2 +
      ((1 - q 1) * Real.sin (q 0)) ^ 2 - (q 1 - 1) ^ 2 = 0
    nlinarith
  · rintro ⟨heq, hz0, hz1⟩
    by_cases hapex : p 2 = 1
    · have hxy : p 0 ^ 2 + p 1 ^ 2 = 0 := by
        rw [hapex] at heq
        norm_num at heq ⊢
        linarith
      have hx : p 0 = 0 := by nlinarith [sq_nonneg (p 1)]
      have hy : p 1 = 0 := by nlinarith [sq_nonneg (p 0)]
      let q : Parameters := ![0, 1]
      refine ⟨q, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_⟩
        · simp [q]
        · simp [q, Real.pi_pos.le]
        · simp [q]
        · simp [q]
      · funext i
        fin_cases i <;> simp [parametrization, q, hx, hy, hapex]
    · have hr : 0 < 1 - p 2 := lt_of_le_of_ne (sub_nonneg.mpr hz1) (by
        intro h
        apply hapex
        linarith)
      let z : ℂ := ⟨p 0 / (1 - p 2), p 1 / (1 - p 2)⟩
      have hnormsq : p 0 ^ 2 + p 1 ^ 2 = (1 - p 2) ^ 2 := by
        nlinarith
      have hznorm : ‖z‖ = 1 := by
        have hsquare : ‖z‖ * ‖z‖ = 1 := by
          rw [Complex.norm_mul_self_eq_normSq]
          simp only [Complex.normSq_apply, z]
          field_simp [ne_of_gt hr]
          nlinarith
        nlinarith [norm_nonneg z]
      have hz_ne : z ≠ 0 := by
        intro hz
        rw [hz, norm_zero] at hznorm
        norm_num at hznorm
      let θ : ℝ := if 0 ≤ Complex.arg z then Complex.arg z else Complex.arg z + 2 * Real.pi
      have hθ0 : 0 ≤ θ := by
        dsimp [θ]
        split_ifs with h
        · exact h
        · have ha := Complex.neg_pi_lt_arg z
          linarith [Real.pi_pos]
      have hθ2π : θ ≤ 2 * Real.pi := by
        dsimp [θ]
        split_ifs with h
        · exact le_trans (Complex.arg_le_pi z) (by linarith [Real.pi_pos])
        · linarith
      have hcos : Real.cos θ = p 0 / (1 - p 2) := by
        dsimp [θ]
        split_ifs with h
        · simpa [z, hznorm] using Complex.cos_arg hz_ne
        · rw [Real.cos_add_two_pi]
          simpa [z, hznorm] using Complex.cos_arg hz_ne
      have hsin : Real.sin θ = p 1 / (1 - p 2) := by
        dsimp [θ]
        split_ifs with h
        · simpa [z, hznorm] using Complex.sin_arg z
        · rw [Real.sin_add_two_pi]
          simpa [z, hznorm] using Complex.sin_arg z
      let q : Parameters := ![θ, p 2]
      refine ⟨q, ⟨hθ0, hθ2π, hz0, hz1⟩, ?_⟩
      funext i
      fin_cases i
      · simp [parametrization, q, hcos]
        field_simp
      · simp [parametrization, q, hsin]
        field_simp
      · simp [parametrization, q]

theorem injOn_parametrization_interior :
    Set.InjOn parametrization interiorParameters := by
  intro p hp q hq hpq
  have hz : p 1 = q 1 := by
    have h := congrFun hpq 2
    simpa [parametrization] using h
  have hr : 1 - p 1 ≠ 0 := by
    have hpz : p 1 < 1 := hp.2.2.2
    linarith
  have hrq : 1 - q 1 ≠ 0 := by simpa [hz] using hr
  have hcos : Real.cos (p 0) = Real.cos (q 0) := by
    have h := congrFun hpq 0
    simp only [parametrization, Matrix.cons_val_zero] at h
    rw [hz] at h
    exact (mul_left_cancel₀ hrq h)
  have hsin : Real.sin (p 0) = Real.sin (q 0) := by
    have h := congrFun hpq 1
    simp only [parametrization, Matrix.cons_val_one, Matrix.cons_val_zero] at h
    rw [hz] at h
    exact (mul_left_cancel₀ hrq h)
  have hcos_sub : Real.cos (p 0 - q 0) = 1 := by
    rw [Real.cos_sub, hcos, hsin]
    simpa [pow_two] using Real.cos_sq_add_sin_sq (q 0)
  have hdiff : p 0 - q 0 = 0 := by
    rw [Real.cos_eq_one_iff_of_lt_of_lt] at hcos_sub
    · exact hcos_sub
    · have hqθ : q 0 < 2 * Real.pi := hq.2.1
      have hpθ : 0 < p 0 := hp.1
      linarith
    · have hpθ : p 0 < 2 * Real.pi := hp.2.1
      have hqθ : 0 < q 0 := hq.1
      linarith
  funext i
  fin_cases i
  · exact sub_eq_zero.mp hdiff
  · exact hz

theorem fderiv_parametrization_formula :
    ∀ p q, fderiv ℝ parametrization p q = parameterDerivative p q := by
  sorry

theorem fderiv_parametrization_injective_on_interior
    (hderiv : ∀ p q, fderiv ℝ parametrization p q = parameterDerivative p q) :
    ∀ p ∈ interiorParameters, Function.Injective (fderiv ℝ parametrization p) := by
  sorry

-- BEGIN SEAT AREA
lemma pullback_coefficients_aux_wedge (i j : Fin 3) (u v : V) :
    coordinateWedge i j ![u, v] = u 0 * 0 + (u i * v j - u j * v i) := by
  change Matrix.det ![![u i, u j], ![v i, v j]] = _
  simp [Matrix.det_fin_two]

theorem pullback_coefficients
    (hderiv : ∀ p q, fderiv ℝ parametrization p q = parameterDerivative p q) :
    (∀ p, pullbackCoefficient (fun _ => coordinateWedge 0 1) parametrization p =
      1 - p 1) ∧
    (∀ p, pullbackCoefficient alpha parametrization p = alphaPullbackFormula p) := by
  constructor
  · intro p
    unfold pullbackCoefficient
    rw [hderiv, hderiv]
    rw [pullback_coefficients_aux_wedge]
    simp [parameterDerivative]
    calc
      (1 - p 1) * Real.sin (p 0) * Real.sin (p 0) +
          (1 - p 1) * Real.cos (p 0) * Real.cos (p 0) =
          (1 - p 1) * (Real.sin (p 0) ^ 2 + Real.cos (p 0) ^ 2) := by ring
      _ = 1 - p 1 := by rw [Real.sin_sq_add_cos_sq]; ring
  · intro p
    unfold pullbackCoefficient
    rw [hderiv, hderiv]
    simp only [alpha, parametrization, parameterDerivative, alphaPullbackFormula,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul]
    rw [pullback_coefficients_aux_wedge, pullback_coefficients_aux_wedge,
      pullback_coefficients_aux_wedge]
    simp
    have htrig := Real.sin_sq_add_cos_sq (p 0)
    ring_nf at htrig ⊢
    left
    linear_combination (1 - p 1) * htrig
-- END SEAT AREA

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
