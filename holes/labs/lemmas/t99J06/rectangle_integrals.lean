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

theorem pullback_coefficients
    (hderiv : ∀ p q, fderiv ℝ parametrization p q = parameterDerivative p q) :
    (∀ p, pullbackCoefficient (fun _ => coordinateWedge 0 1) parametrization p =
      1 - p 1) ∧
    (∀ p, pullbackCoefficient alpha parametrization p = alphaPullbackFormula p) := by
  sorry

-- BEGIN SEAT AREA
lemma rectangle_integrals_aux_cos :
    (∫ x in (0 : ℝ)..2 * Real.pi, Real.cos x) = 0 := by
  simp

lemma rectangle_integrals_aux_cos_sq :
    (∫ x in (0 : ℝ)..2 * Real.pi, (Real.cos x) ^ 2) = Real.pi := by
  rw [integral_cos_sq]
  simp

lemma rectangle_integrals_aux_cos_cube :
    (∫ x in (0 : ℝ)..2 * Real.pi, (Real.cos x) ^ 3) = 0 := by
  have hderiv : ∀ x : ℝ, HasDerivAt
      (fun x : ℝ => Real.sin x - Real.sin x ^ 3 / 3)
      (Real.cos x ^ 3) x := by
    intro x
    convert (Real.hasDerivAt_sin x).sub
      (((Real.hasDerivAt_sin x).pow 3).div_const 3) using 1 <;>
      ring_nf
    rw [Real.sin_sq]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
    ((Real.continuous_cos.pow 3).intervalIntegrable 0 (2 * Real.pi))]
  simp

lemma rectangle_integrals_aux_trig (a b c d : ℝ) :
    (∫ x in (0 : ℝ)..2 * Real.pi,
      a + b * Real.cos x + c * Real.cos x ^ 2 + d * Real.cos x ^ 3) =
      2 * Real.pi * a + Real.pi * c := by
  have hd : ∀ x : ℝ, HasDerivAt
      (fun x : ℝ => a * x + b * Real.sin x +
        c * (x / 2 + Real.sin x * Real.cos x / 2) +
        d * (Real.sin x - Real.sin x ^ 3 / 3))
      (a + b * Real.cos x + c * Real.cos x ^ 2 + d * Real.cos x ^ 3) x := by
    intro x
    have h1 := (hasDerivAt_id x).const_mul a
    have h2 := (Real.hasDerivAt_sin x).const_mul b
    have h3 := (((hasDerivAt_id x).div_const 2).add
      (((Real.hasDerivAt_sin x).mul (Real.hasDerivAt_cos x)).div_const 2)).const_mul c
    have h4 := ((Real.hasDerivAt_sin x).sub
      (((Real.hasDerivAt_sin x).pow 3).div_const 3)).const_mul d
    convert ((h1.add h2).add h3).add h4 using 1 <;> ring_nf
    rw [Real.sin_sq]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((by fun_prop : Continuous (fun x : ℝ =>
      a + b * Real.cos x + c * Real.cos x ^ 2 + d * Real.cos x ^ 3)).intervalIntegrable
      0 (2 * Real.pi))]
  simp
  ring

theorem rectangle_integrals
    (hxy : ∀ p, pullbackCoefficient (fun _ => coordinateWedge 0 1) parametrization p =
      1 - p 1)
    (halpha : ∀ p, pullbackCoefficient alpha parametrization p = alphaPullbackFormula p) :
    0 < rectangleIntegral (fun _ => coordinateWedge 0 1) parametrization
      0 (2 * Real.pi) 0 1 ∧
    rectangleIntegral alpha parametrization 0 (2 * Real.pi) 0 1 = 9 * Real.pi / 2 := by
  unfold rectangleIntegral
  simp_rw [hxy, halpha]
  constructor
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    have h : (∫ z in (0 : ℝ)..1, ∫ _ in (0 : ℝ)..2 * Real.pi, 1 - z) =
        Real.pi := by
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => by
          convert (hasDerivAt_const x (2 * Real.pi)).mul
            ((hasDerivAt_id x).sub (((hasDerivAt_id x).pow 2).div_const 2)) using 1 <;>
            simp [id] <;> ring)
        ((by fun_prop : Continuous (fun z : ℝ => 2 * Real.pi * (1 - z))).intervalIntegrable 0 1)]
      simp [id]
      ring
    rw [h]
    exact Real.pi_pos
  · simp only [alphaPullbackFormula, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hexpand : ∀ z θ : ℝ,
        (z ^ 2 + 2 * ((1 - z) * Real.cos θ) * z + 4) * (1 - z) +
          (((1 - z) * Real.cos θ) - ((1 - z) * Real.cos θ) ^ 2) *
            ((1 - z) * Real.cos θ) =
        (z ^ 2 + 4) * (1 - z) +
          (2 * z * (1 - z) ^ 2) * Real.cos θ +
          (1 - z) ^ 2 * Real.cos θ ^ 2 -
          (1 - z) ^ 3 * Real.cos θ ^ 3 := by
      intros
      ring
    simp_rw [hexpand]
    have hinner : ∀ z : ℝ,
        (∫ θ in (0 : ℝ)..2 * Real.pi,
          (z ^ 2 + 4) * (1 - z) +
            (2 * z * (1 - z) ^ 2) * Real.cos θ +
            (1 - z) ^ 2 * Real.cos θ ^ 2 -
            (1 - z) ^ 3 * Real.cos θ ^ 3) =
          2 * Real.pi * ((z ^ 2 + 4) * (1 - z)) + Real.pi * (1 - z) ^ 2 := by
      intro z
      convert rectangle_integrals_aux_trig ((z ^ 2 + 4) * (1 - z))
        (2 * z * (1 - z) ^ 2) ((1 - z) ^ 2) (-(1 - z) ^ 3) using 1 <;> ring
    simp_rw [hinner]
    ring_nf
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun z _ => by
        convert (((((hasDerivAt_id z).const_mul (Real.pi * 9)).sub
          (((hasDerivAt_id z).pow 2).const_mul (Real.pi * 5))).add
          (((hasDerivAt_id z).pow 3).const_mul Real.pi)).sub
          (((hasDerivAt_id z).pow 4).const_mul (Real.pi / 2))) using 1 <;>
          simp [id] <;> ring)
      ((by fun_prop : Continuous (fun z : ℝ =>
        Real.pi * 9 - Real.pi * z * 10 + Real.pi * z ^ 2 * 3 -
          Real.pi * z ^ 3 * 2)).intervalIntegrable 0 1)]
    norm_num
    ring
-- END SEAT AREA

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
