import Mathlib
import ConstructionTargets.TorusFormTargets

/-! # t93A06: descent, primitive and periods of the printed torus form

The large quotient-atlas construction is isolated from the coordinate
calculations.  Downstream lemmas receive the conclusions they need as explicit
hypotheses, so their seats can be worked independently.
-/
open scoped Manifold ContDiff
open ConstructionTargets.ManifoldFormTargets ConstructionTargets.TorusFormTargets
noncomputable section

/-- LIBRARY: the coordinatewise quotient by `ℤ²` has a smooth atlas for which
the actual projection is a local diffeomorphism. -/
theorem t93A06_torusAtlas : Nonempty SmoothAtlas := by
  sorry

/-- The fibres of the printed quotient projection are precisely integer
translates. -/
theorem t93A06_projection_fibers (x y : Plane) :
    projection x = projection y ↔
      ∃ k : Fin 2 → ℤ, ∀ i, y i = x i + (k i : ℝ) := by
  constructor
  · intro h
    have hcoord (i : Fin 2) : (x i : AddCircle (1 : ℝ)) = (y i : AddCircle (1 : ℝ)) :=
      congrFun h i
    choose n hn using fun i =>
      (AddCircle.coe_eq_zero_iff (p := (1 : ℝ)) (x := x i - y i)).mp (by
        rw [AddCircle.coe_sub, hcoord i, sub_self])
    refine ⟨fun i => -n i, fun i => ?_⟩
    have hd : (n i : ℝ) = x i - y i := by
      simpa using hn i
    rw [Int.cast_neg]
    linarith
  · rintro ⟨k, hk⟩
    funext i
    change (x i : AddCircle (1 : ℝ)) = (y i : AddCircle (1 : ℝ))
    rw [hk i, AddCircle.coe_add]
    simp

/-- A smooth invariant form descends uniquely through the quotient atlas.
The fibre characterization is supplied as a hypothesis to keep this seat
independent of the atlas and fibre seats. -/
theorem t93A06_periodic_form_descent (atlas : SmoothAtlas)
    (hfib : ∀ x y : Plane, projection x = projection y ↔
      ∃ k : Fin 2 → ℤ, ∀ i, y i = x i + (k i : ℝ)) :
    letI := atlas.charts
    ∃ form : Form Plane Torus 2,
      IsSmooth form ∧ pullback projection form = sourceForm ∧
      (∀ other : Form Plane Torus 2, IsSmooth other →
        pullback projection other = sourceForm → other = form) := by
  sorry

/-- The fundamental-square integral is `1/4` for any form whose pullback is
the printed periodic form. -/
-- BEGIN SEAT AREA
lemma t93A06_torusIntegral_quarter_aux_sin :
    (∫ x : ℝ in 0..1, Real.sin (2 * Real.pi * x) ^ 2) = 1 / 2 := by
  have hd : deriv (fun x : ℝ => x / 2 - Real.sin (4 * Real.pi * x) / (8 * Real.pi)) =
      fun x => Real.sin (2 * Real.pi * x) ^ 2 := by
    funext x
    have h := ((hasDerivAt_id x).div_const 2 |>.sub
      (((Real.hasDerivAt_sin (4 * Real.pi * x)).comp x
        (((hasDerivAt_const x (4 * Real.pi)).mul (hasDerivAt_id x)))).div_const
          (8 * Real.pi)))
    rw [show deriv (fun x : ℝ => x / 2 - Real.sin (4 * Real.pi * x) /
      (8 * Real.pi)) x = _ by simpa only [Function.comp_apply, id_eq] using h.deriv]
    rw [Real.sin_sq_eq_half_sub]
    field_simp [Real.pi_ne_zero]
    <;> ring
  rw [intervalIntegral.integral_deriv_eq_sub'
    (fun x : ℝ => x / 2 - Real.sin (4 * Real.pi * x) / (8 * Real.pi)) hd]
  · norm_num
    rw [show 4 * Real.pi = (4 : ℕ) * Real.pi by norm_num,
      Real.sin_nat_mul_pi]
  · intro x hx
    fun_prop
  · fun_prop

lemma t93A06_torusIntegral_quarter_aux_cos :
    (∫ x : ℝ in 0..1, Real.cos (2 * Real.pi * x) ^ 2) = 1 / 2 := by
  have hd : deriv (fun x : ℝ => x / 2 + Real.sin (4 * Real.pi * x) / (8 * Real.pi)) =
      fun x => Real.cos (2 * Real.pi * x) ^ 2 := by
    funext x
    have h := ((hasDerivAt_id x).div_const 2 |>.add
      (((Real.hasDerivAt_sin (4 * Real.pi * x)).comp x
        (((hasDerivAt_const x (4 * Real.pi)).mul (hasDerivAt_id x)))).div_const
          (8 * Real.pi)))
    rw [show deriv (fun x : ℝ => x / 2 + Real.sin (4 * Real.pi * x) /
      (8 * Real.pi)) x = _ by simpa only [Function.comp_apply, id_eq] using h.deriv]
    rw [Real.cos_sq]
    field_simp [Real.pi_ne_zero]
    <;> ring
  rw [intervalIntegral.integral_deriv_eq_sub'
    (fun x : ℝ => x / 2 + Real.sin (4 * Real.pi * x) / (8 * Real.pi)) hd]
  · norm_num
    rw [show 4 * Real.pi = (4 : ℕ) * Real.pi by norm_num,
      Real.sin_nat_mul_pi]
  · intro x hx
    fun_prop
  · fun_prop

theorem t93A06_torusIntegral_quarter (atlas : SmoothAtlas)
    (form : let _ := atlas.charts; Form Plane Torus 2)
    (hpull : letI := atlas.charts
      pullback projection form = sourceForm) :
    letI := atlas.charts
    torusIntegral form = 1 / 4 := by
  letI := atlas.charts
  unfold ConstructionTargets.TorusFormTargets.torusIntegral
  rw [hpull]
  simp [sourceForm, pullback, areaForm]
  rw [t93A06_torusIntegral_quarter_aux_sin,
    t93A06_torusIntegral_quarter_aux_cos]
  norm_num
  change Matrix.det ![Pi.single 0 (1 : ℝ), Pi.single 1 (1 : ℝ)] = 1
  norm_num [Matrix.det_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
-- END SEAT AREA

/-- LIBRARY: on this closed quotient torus, a smooth exact top form has zero
fundamental-square integral.  Hence the descended form with integral `1/4`
is not exact. -/
theorem t93A06_not_exact_of_integral_quarter (atlas : SmoothAtlas)
    (form : let _ := atlas.charts; Form Plane Torus 2)
    (hsmooth : letI := atlas.charts; IsSmooth form)
    (hint : letI := atlas.charts; torusIntegral form = 1 / 4) :
    letI := atlas.charts
    ¬ IsExact form := by
  sorry

/-- Coordinate calculus for the explicit primitive: it is smooth and its
exterior derivative is the source form. -/
theorem t93A06_primitive_calculus :
    IsSmooth primitive ∧ exteriorDerivative primitive = sourceForm := by
  sorry

/-- Direct evaluation of the explicit primitive on the four oriented edges of
the parallelogram. -/
theorem t93A06_primitive_parallelogramIntegral :
    parallelogramIntegral primitive = 1 / 4 := by
  sorry

theorem apm_t93a06 : ∃ atlas : SmoothAtlas,
    letI := atlas.charts
    (∀ x y : Plane, projection x = projection y ↔
      ∃ k : Fin 2 → ℤ, ∀ i, y i = x i + (k i : ℝ)) ∧
    (∃ form : Form Plane Torus 2,
      IsSmooth form ∧ pullback projection form = sourceForm ∧
      (∀ other : Form Plane Torus 2, IsSmooth other →
        pullback projection other = sourceForm → other = form) ∧
      torusIntegral form = 1 / 4 ∧ ¬ IsExact form) ∧
    IsSmooth primitive ∧ exteriorDerivative primitive = sourceForm ∧
    parallelogramIntegral primitive = 1 / 4 := by
  obtain ⟨atlas⟩ := t93A06_torusAtlas
  refine ⟨atlas, ?_⟩
  letI := atlas.charts
  have hfib : ∀ x y : Plane, projection x = projection y ↔
      ∃ k : Fin 2 → ℤ, ∀ i, y i = x i + (k i : ℝ) :=
    t93A06_projection_fibers
  refine ⟨hfib, ?_, t93A06_primitive_calculus.1,
    t93A06_primitive_calculus.2,
    t93A06_primitive_parallelogramIntegral⟩
  obtain ⟨form, hsmooth, hpull, hunique⟩ :=
    t93A06_periodic_form_descent atlas hfib
  have hint : torusIntegral form = 1 / 4 :=
    t93A06_torusIntegral_quarter atlas form hpull
  exact ⟨form, hsmooth, hpull, hunique, hint,
    t93A06_not_exact_of_integral_quarter atlas form hsmooth hint⟩

#print axioms apm_t93a06
