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

/-- LIBRARY (chart construction): construct quotient charts for which the
actual coordinate projection is locally a diffeomorphism.  This is separated
from the manifold-coverage argument below. -/
theorem t93A06_torusAtlas_aux_quotient_charts :
    ∃ charts : ChartedSpace Plane Torus,
      letI := charts
      IsLocalDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ projection := by
  sorry

/-- LIBRARY (atlas coverage): a charted structure on the quotient for which
the surjective projection from the plane is locally a diffeomorphism is a
smooth two-manifold.  Its input is explicit, so this seat does not depend on
the sorry proving `t93A06_torusAtlas_aux_quotient_charts`. -/
theorem t93A06_torusAtlas_aux_manifold_of_localDiffeomorph
    (charts : ChartedSpace Plane Torus)
    (hlocal : letI := charts
      IsLocalDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ projection) :
    letI := charts
    IsManifold 𝓘(ℝ,Plane) ∞ Torus := by
  sorry

/-- The two independent quotient-chart conclusions assemble into the target
atlas structure. -/
theorem t93A06_torusAtlas : Nonempty SmoothAtlas := by
  obtain ⟨charts, hlocal⟩ := t93A06_torusAtlas_aux_quotient_charts
  letI := charts
  exact ⟨⟨charts,
    t93A06_torusAtlas_aux_manifold_of_localDiffeomorph charts hlocal,
    hlocal⟩⟩

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

lemma t93A06_periodic_form_descent_aux_source_periodic
    (x : Plane) (k : Fin 2 → ℤ) :
    sourceForm (fun i ↦ x i + (k i : ℝ)) = sourceForm x := by
  unfold sourceForm
  have hs : Real.sin (2 * Real.pi * (x 0 + (k 0 : ℝ))) =
      Real.sin (2 * Real.pi * x 0) := by
    rw [show 2 * Real.pi * (x 0 + (k 0 : ℝ)) =
      2 * Real.pi * x 0 + (k 0 : ℝ) * (2 * Real.pi) by ring]
    exact Real.sin_add_int_mul_two_pi _ _
  have hc : Real.cos (2 * Real.pi * (x 1 + (k 1 : ℝ))) =
      Real.cos (2 * Real.pi * x 1) := by
    rw [show 2 * Real.pi * (x 1 + (k 1 : ℝ)) =
      2 * Real.pi * x 1 + (k 1 : ℝ) * (2 * Real.pi) by ring]
    exact Real.cos_add_int_mul_two_pi _ _
  rw [hs, hc]

lemma t93A06_periodic_form_descent_aux_projection_surjective :
    Function.Surjective projection := by
  intro z
  choose x hx using fun i ↦ QuotientAddGroup.mk_surjective (z i)
  refine ⟨x, funext fun i ↦ ?_⟩
  exact hx i

lemma t93A06_periodic_form_descent_aux_pullback_injective
    (atlas : SmoothAtlas) :
    letI := atlas.charts
    Function.Injective
      (pullback (k := 2) projection : Form Plane Torus 2 → Form Plane Plane 2) := by
  letI := atlas.charts
  intro a b hab
  funext z
  obtain ⟨x, rfl⟩ := t93A06_periodic_form_descent_aux_projection_surjective z
  let L : Plane ≃L[ℝ] Plane :=
    atlas.quotient_localDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x
  apply ContinuousAlternatingMap.ext
  intro v
  have hpoint := congr_fun hab x
  have happ := congrArg (fun q ↦ q (fun i ↦ L.symm (v i))) hpoint
  change a (projection x) (fun i ↦ L (L.symm (v i))) =
    b (projection x) (fun i ↦ L (L.symm (v i))) at happ
  have hv : (fun i ↦ L (L.symm (v i))) = v := by
    funext i
    exact L.apply_symm_apply (v i)
  simpa [hv] using happ

lemma t93A06_periodic_form_descent_aux_source_smooth :
    ContDiff ℝ ∞ sourceForm := by
  unfold sourceForm areaForm
  fun_prop

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
  simp [parallelogramIntegral, segmentIntegral, primitive]
  let f : ℝ → ℝ := fun x ↦
    (x / 2 - Real.sin (4 * Real.pi * x) / (8 * Real.pi)) *
      Real.cos (2 * Real.pi * x) ^ 2
  have hf : Continuous f := by
    unfold f
    fun_prop
  have hreflect : (∫ x : ℝ in 0..1, f (1 - x)) = ∫ x : ℝ in 0..1, f x := by
    simpa using (intervalIntegral.integral_comp_sub_left f (a := (0 : ℝ)) (b := 1) 1)
  have hshift (x : ℝ) :
      ((1 - x + x * 2) / 2 -
          Real.sin (4 * Real.pi * (1 - x + x * 2)) / (8 * Real.pi)) *
          Real.cos (2 * Real.pi * x) ^ 2 =
        f x + (1 / 2 : ℝ) * Real.cos (2 * Real.pi * x) ^ 2 := by
    have hs : Real.sin (4 * Real.pi * (1 - x + x * 2)) =
        Real.sin (4 * Real.pi * x) := by
      rw [show 4 * Real.pi * (1 - x + x * 2) =
        4 * Real.pi * x + (2 : ℤ) * (2 * Real.pi) by push_cast; ring]
      exact Real.sin_add_int_mul_two_pi _ _
    rw [hs]
    unfold f
    ring
  rw [intervalIntegral.integral_congr (fun x _ ↦ hshift x)]
  change (∫ x : ℝ in 0..1, (f x + (1 / 2 : ℝ) * Real.cos (2 * Real.pi * x) ^ 2)) -
      (∫ x : ℝ in 0..1, f (1 - x)) = 4⁻¹
  have hg : Continuous (fun x : ℝ ↦
      (1 / 2 : ℝ) * Real.cos (2 * Real.pi * x) ^ 2) := by fun_prop
  rw [hreflect, intervalIntegral.integral_add (hf.intervalIntegrable 0 1)
    (hg.intervalIntegrable 0 1)]
  ring_nf
  have hder (x : ℝ) : HasDerivAt
      (fun y : ℝ ↦ y / 4 + Real.sin (4 * Real.pi * y) / (16 * Real.pi))
      (Real.cos (Real.pi * x * 2) ^ 2 * (1 / 2)) x := by
    have h := (hasDerivAt_id x).div_const 4 |>.add
      ((((hasDerivAt_const x (4 * Real.pi)).mul (hasDerivAt_id x)).sin).div_const
        (16 * Real.pi))
    convert h using 1
    · simp only [Pi.mul_apply, id_eq, zero_mul, zero_add, one_mul]
      rw [show Real.pi * x * 2 = 2 * Real.pi * x by ring, Real.cos_sq]
      rw [show 4 * Real.pi * x = 2 * (2 * Real.pi * x) by ring,
        Real.cos_two_mul]
      field_simp [Real.pi_ne_zero]
      ring_nf
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ ↦ hder x)
    ((by fun_prop : Continuous (fun x : ℝ ↦
      Real.cos (Real.pi * x * 2) ^ 2 * (1 / 2))).intervalIntegrable 0 1)]
  have hs : Real.sin (4 * Real.pi) = 0 := by
    rw [show 4 * Real.pi = 0 + (2 : ℤ) * (2 * Real.pi) by push_cast; ring,
      Real.sin_add_int_mul_two_pi, Real.sin_zero]
  simp [hs]

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
