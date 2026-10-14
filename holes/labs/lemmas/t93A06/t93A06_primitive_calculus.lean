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
theorem t93A06_torusIntegral_quarter (atlas : SmoothAtlas)
    (form : let _ := atlas.charts; Form Plane Torus 2)
    (hpull : letI := atlas.charts
      pullback projection form = sourceForm) :
    letI := atlas.charts
    torusIntegral form = 1 / 4 := by
  sorry

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
-- BEGIN SEAT AREA
lemma t93A06_primitive_calculus_aux_fderiv (w : Fin 1 → Plane) (x u : Plane) :
    fderiv ℝ (fun y ↦ primitive y w) x u =
      (Real.sin (2 * Real.pi * x 0) ^ 2 * u 0 * Real.cos (2 * Real.pi * x 1) ^ 2 -
       (x 0 / 2 - Real.sin (4 * Real.pi * x 0) / (8 * Real.pi)) *
         (4 * Real.pi * Real.cos (2 * Real.pi * x 1) *
           Real.sin (2 * Real.pi * x 1) * u 1)) * (w 0 1) := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) x
  have hA := (h0.mul_const (1 / 2)).sub
    (((h0.const_mul (4 * Real.pi)).sin).mul_const (1 / (8 * Real.pi)))
  have hC := ((h1.const_mul (2 * Real.pi)).cos).pow 2
  have h := (hA.mul hC).mul_const (w 0 1)
  have hf := congrArg (fun L : Plane →L[ℝ] ℝ ↦ L u) h.fderiv
  calc
    fderiv ℝ (fun y ↦ primitive y w) x u =
        fderiv ℝ (fun y ↦
          (y 0 * (1 / 2) - Real.sin (4 * Real.pi * y 0) * (1 / (8 * Real.pi))) *
            Real.cos (2 * Real.pi * y 1) ^ 2 * (w 0 1)) x u := by
      apply congrArg (fun f : Plane → ℝ ↦ fderiv ℝ f x u)
      funext y
      simp [primitive, div_eq_mul_inv]
    _ = _ := hf
    _ = _ := by
      simp [ContinuousLinearMap.proj_apply]
      have hs : Real.sin (2 * Real.pi * x 0) ^ 2 =
          1 - Real.cos (2 * Real.pi * x 0) ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * x 0)]
      rw [hs]
      field_simp [Real.pi_ne_zero]
      rw [show x 0 * 4 * Real.pi = 2 * (x 0 * 2 * Real.pi) by ring,
        Real.cos_two_mul]
      ring

theorem t93A06_primitive_calculus :
    IsSmooth primitive ∧ exteriorDerivative primitive = sourceForm := by
  constructor
  · intro e he
    rw [chartedSpaceSelf_atlas] at he
    subst e
    unfold inChart primitive
    simp
    convert (show ContDiffOn ℝ ∞ primitive Set.univ by
      unfold primitive
      fun_prop) using 1
  · unfold exteriorDerivative
    funext x
    apply ContinuousAlternatingMap.ext
    intro v
    simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply]
    have hin : inChart primitive (OpenPartialHomeomorph.refl Plane) = primitive := by
      funext y
      apply ContinuousAlternatingMap.ext
      intro w
      unfold inChart
      simp only [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply,
        mfderiv_id]
      congr 1
    rw [hin]
    simp
    change extDeriv primitive x v = sourceForm x v
    have hd : Differentiable ℝ primitive := by
      unfold primitive
      fun_prop
    rw [extDeriv_apply (hd x)]
    simp only [Nat.reduceAdd, Int.reduceNeg, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_one, Fin.sum_univ_two, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      pow_zero, Fin.removeNth_zero, one_mul, Nat.mod_succ, pow_one, neg_mul]
    rw [t93A06_primitive_calculus_aux_fderiv,
      t93A06_primitive_calculus_aux_fderiv]
    simp [sourceForm, Fin.tail, Fin.removeNth]
    change _ = _ * Matrix.det v
    rw [Matrix.det_fin_two]
    ring
-- END SEAT AREA

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
