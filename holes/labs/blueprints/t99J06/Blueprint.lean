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
  intro p hp q r hqr
  rw [hderiv p q, hderiv p r] at hqr
  have h1 : q 1 = r 1 := by
    have h := congrFun hqr 2
    simpa [parameterDerivative] using h
  have hsin : (1 - p 1) * Real.sin (p 0) * q 0 =
      (1 - p 1) * Real.sin (p 0) * r 0 := by
    have h := congrFun hqr 0
    simp only [parameterDerivative, Matrix.cons_val_zero] at h
    rw [h1] at h
    linarith
  have hcos : (1 - p 1) * Real.cos (p 0) * q 0 =
      (1 - p 1) * Real.cos (p 0) * r 0 := by
    have h := congrFun hqr 1
    simp only [parameterDerivative, Matrix.cons_val_one, Matrix.cons_val_zero] at h
    rw [h1] at h
    linarith
  have hradius : 1 - p 1 ≠ 0 := by
    have := hp.2.2.2
    linarith
  have h0 : q 0 = r 0 := by
    by_cases hs : Real.sin (p 0) = 0
    · have hc : Real.cos (p 0) ≠ 0 := by
        intro hc
        have ht := Real.sin_sq_add_cos_sq (p 0)
        rw [hs, hc] at ht
        norm_num at ht
      exact mul_left_cancel₀ (mul_ne_zero hradius hc) hcos
    · exact mul_left_cancel₀ (mul_ne_zero hradius hs) hsin
  funext i
  fin_cases i
  · exact h0
  · exact h1

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
