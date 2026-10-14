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

lemma t93A06_torusAtlas_aux_quotient_charts_aux_fibers (x y : Plane) :
    projection x = projection y ↔
      ∃ k : Fin 2 → ℤ, ∀ i, y i = x i + (k i : ℝ) := by
  constructor
  · intro h
    have hcoord (i : Fin 2) : (x i : AddCircle (1 : ℝ)) =
        (y i : AddCircle (1 : ℝ)) := congrFun h i
    choose n hn using fun i =>
      (AddCircle.coe_eq_zero_iff (p := (1 : ℝ)) (x := x i - y i)).mp (by
        rw [AddCircle.coe_sub, hcoord i, sub_self])
    refine ⟨fun i => -n i, fun i => ?_⟩
    have hd : (n i : ℝ) = x i - y i := by simpa using hn i
    rw [Int.cast_neg]
    linarith
  · rintro ⟨k, hk⟩
    funext i
    change (x i : AddCircle (1 : ℝ)) = (y i : AddCircle (1 : ℝ))
    rw [hk i, AddCircle.coe_add]
    simp

lemma t93A06_torusAtlas_aux_quotient_charts_aux_box_inj (a : Plane) :
    Set.InjOn projection
      (Set.pi Set.univ (fun i : Fin 2 => Set.Ioo (a i - (1 / 4 : ℝ))
        (a i + 1 / 4))) := by
  intro x hx y hy hxy
  obtain ⟨k, hk⟩ :=
    (t93A06_torusAtlas_aux_quotient_charts_aux_fibers x y).mp hxy
  funext i
  have hxi := hx i (Set.mem_univ i)
  have hyi := hy i (Set.mem_univ i)
  change a i - 1 / 4 < x i ∧ x i < a i + 1 / 4 at hxi
  change a i - 1 / 4 < y i ∧ y i < a i + 1 / 4 at hyi
  have hlt : ((k i : ℤ) : ℝ) < 1 := by
    rw [hk i] at hyi
    linarith
  have hgt : (-1 : ℝ) < ((k i : ℤ) : ℝ) := by
    rw [hk i] at hyi
    linarith
  have hk0 : k i = 0 := by
    have hlo : (-1 : ℤ) < k i := by exact_mod_cast hgt
    have hhi : k i < 1 := by exact_mod_cast hlt
    omega
  symm
  simpa [hk0] using hk i

/-- LIBRARY (chart construction): construct quotient charts for which the
actual coordinate projection is locally a diffeomorphism.  This is separated
from the manifold-coverage argument below. -/
theorem t93A06_torusAtlas_aux_quotient_charts :
    ∃ charts : ChartedSpace Plane Torus,
      letI := charts
      (∀ e ∈ atlas Plane Torus, ∃ x : Torus, e = chartAt Plane x) ∧
      (∀ x y : Torus, ∀ z ∈ ((chartAt Plane x).symm.trans (chartAt Plane y)).source, ∃ k : Fin 2 → ℤ, ∀ i, ((chartAt Plane x).symm.trans (chartAt Plane y)) z i = z i + (k i : ℝ)) ∧
      IsLocalDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ projection := by
  sorry

/-- LIBRARY (atlas coverage): a charted structure on the quotient for which
the surjective projection from the plane is locally a diffeomorphism is a
smooth two-manifold.  Its input is explicit, so this seat does not depend on
the sorry proving `t93A06_torusAtlas_aux_quotient_charts`. -/
theorem t93A06_torusAtlas_aux_manifold_of_localDiffeomorph
    (charts : ChartedSpace Plane Torus)
    (hatlas : letI := charts
      (∀ e ∈ atlas Plane Torus, ∃ x : Torus, e = chartAt Plane x))
    (htrans : letI := charts
      (∀ x y : Torus, ∀ z ∈ ((chartAt Plane x).symm.trans (chartAt Plane y)).source, ∃ k : Fin 2 → ℤ, ∀ i, ((chartAt Plane x).symm.trans (chartAt Plane y)) z i = z i + (k i : ℝ))) :
    letI := charts
    IsManifold 𝓘(ℝ,Plane) ∞ Torus := by
  letI := charts
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨x, rfl⟩ := hatlas e he
  obtain ⟨y, rfl⟩ := hatlas e' he'
  let t := (chartAt Plane x).symm.trans (chartAt Plane y)
  have ht : ContDiffOn ℝ ∞ (↑t) t.source := by
    intro z hz
    obtain ⟨k, hk⟩ := htrans x y z hz
    have hc : ContinuousWithinAt (fun w ↦ t w - w) t.source z :=
      (t.continuousOn.continuousWithinAt hz).sub continuousWithinAt_id
    have hev : ∀ᶠ w in nhdsWithin z t.source,
        dist (t w - w) (t z - z) < 1 :=
      (Metric.tendsto_nhds.mp hc) 1 zero_lt_one
    have heq : ∀ᶠ w in nhdsWithin z t.source, t w = w + fun i ↦ (k i : ℝ) := by
      filter_upwards [hev, self_mem_nhdsWithin] with w hw hws
      obtain ⟨l, hl⟩ := htrans x y w hws
      change ∀ i, t w i = w i + (l i : ℝ) at hl
      change ∀ i, t z i = z i + (k i : ℝ) at hk
      have hlk : l = k := by
        funext i
        have hcoord : |((l i - k i : ℤ) : ℝ)| < 1 := by
          calc
            |((l i - k i : ℤ) : ℝ)| = |(t w - w) i - (t z - z) i| := by
              rw [Int.cast_sub]
              simp only [Pi.sub_apply]
              rw [hl i, hk i]
              ring
            _ ≤ ‖(t w - w) - (t z - z)‖ :=
              norm_le_pi_norm ((t w - w) - (t z - z)) i
            _ = dist (t w - w) (t z - z) := by rw [dist_eq_norm]
            _ < 1 := hw
        have hlo : (-1 : ℤ) < l i - k i := by
          exact_mod_cast (abs_lt.mp hcoord).1
        have hhi : l i - k i < 1 := by
          exact_mod_cast (abs_lt.mp hcoord).2
        omega
      simpa [hlk] using funext hl
    apply (contDiff_id.add
      (contDiff_const : ContDiff ℝ ∞
        (fun _ : Plane ↦ (fun i ↦ (k i : ℝ))))).contDiffWithinAt.congr_of_eventuallyEq
      heq
    exact funext hk
  simpa using ht

/-- The two independent quotient-chart conclusions assemble into the target
atlas structure. -/
theorem t93A06_torusAtlas : Nonempty SmoothAtlas := by
  obtain ⟨charts, hatlas, htrans, hlocal⟩ := t93A06_torusAtlas_aux_quotient_charts
  letI := charts
  exact ⟨⟨charts,
    t93A06_torusAtlas_aux_manifold_of_localDiffeomorph charts hatlas htrans,
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

/-- Set-level descent of the periodic covector field.  Periodicity is an
explicit input so this leaf can be proved independently of the trigonometric
calculation above. -/
theorem t93A06_periodic_form_descent_aux_set_descent
    (atlas : SmoothAtlas)
    (hfib : ∀ x y : Plane, projection x = projection y ↔
      ∃ k : Fin 2 → ℤ, ∀ i, y i = x i + (k i : ℝ))
    (hperiodic : ∀ (x : Plane) (k : Fin 2 → ℤ),
      sourceForm (fun i ↦ x i + (k i : ℝ)) = sourceForm x) :
    letI := atlas.charts
    ∃ form : Form Plane Torus 2,
      pullback projection form = sourceForm := by
  letI := atlas.charts
  classical
  let lift : Torus → Plane := fun z ↦
    Classical.choose (t93A06_periodic_form_descent_aux_projection_surjective z)
  have hlift (z : Torus) : projection (lift z) = z :=
    Classical.choose_spec (t93A06_periodic_form_descent_aux_projection_surjective z)
  let D (x : Plane) : Plane ≃L[ℝ] Plane :=
    atlas.quotient_localDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x
  let form : Form Plane Torus 2 := fun z ↦
    (sourceForm (lift z)).compContinuousLinearMap (D (lift z)).symm
  refine ⟨form, funext fun x ↦ ?_⟩
  obtain ⟨k, hk⟩ :=
    (hfib x (lift (projection x))).mp (hlift (projection x)).symm
  have hproj : (fun y : Plane ↦ projection (fun i ↦ y i + (k i : ℝ))) =
      projection := by
    funext y
    exact ((hfib y (fun i ↦ y i + (k i : ℝ))).mpr
      ⟨k, fun i ↦ rfl⟩).symm
  have htrans : mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane)
      (fun y : Plane ↦ fun i ↦ y i + (k i : ℝ)) x =
      ContinuousLinearMap.id ℝ Plane := by
    rw [mfderiv_eq_fderiv]
    exact ((hasFDerivAt_id x).add_const (fun i ↦ (k i : ℝ))).fderiv
  have hlift_eq : lift (projection x) = (fun i ↦ x i + (k i : ℝ)) := by
    funext i
    exact hk i
  have hd : mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) projection
      (lift (projection x)) =
      mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) projection x := by
    rw [hlift_eq]
    have hc := mfderiv_comp x
      ((atlas.quotient_localDiffeomorph
        (fun i ↦ x i + (k i : ℝ))).mdifferentiableAt (by simp))
      (show MDifferentiableAt 𝓘(ℝ,Plane) 𝓘(ℝ,Plane)
        (fun y : Plane ↦ fun i ↦ y i + (k i : ℝ)) x by
          rw [mdifferentiableAt_iff_differentiableAt]
          exact ((hasFDerivAt_id x).add_const
            (fun i ↦ (k i : ℝ))).differentiableAt)
    rw [show (projection ∘ (fun y : Plane ↦ fun i ↦ y i + (k i : ℝ))) =
      projection by funext y; exact congrFun hproj y,
      htrans] at hc
    simpa using hc.symm
  apply ContinuousAlternatingMap.ext
  intro v
  change sourceForm (lift (projection x))
      (fun i ↦ (D (lift (projection x))).symm
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) projection x (v i))) =
    sourceForm x v
  rw [show sourceForm (lift (projection x)) = sourceForm x by
    rw [hlift_eq, hperiodic x k]]
  have hD : (D (lift (projection x)) : Plane →L[ℝ] Plane) =
      mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) projection x := by
    change mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) projection (lift (projection x)) = _
    exact hd
  rw [← hD]
  congr 1
  funext i
  exact (D (lift (projection x))).symm_apply_apply (v i)

/-- Smoothness descends along the local diffeomorphism `projection`.  Both
the form and the smoothness of its pullback are explicit inputs, making this
leaf independent of set-level descent. -/
theorem t93A06_periodic_form_descent_aux_smooth_of_pullback
    (atlas : SmoothAtlas)
    (form : let _ := atlas.charts; Form Plane Torus 2)
    (hsource : ContDiff ℝ ∞ sourceForm)
    (hpull : letI := atlas.charts
      pullback projection form = sourceForm) :
    letI := atlas.charts
    IsSmooth form := by
  sorry

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
  letI := atlas.charts
  obtain ⟨form, hpull⟩ :=
    t93A06_periodic_form_descent_aux_set_descent atlas hfib
      t93A06_periodic_form_descent_aux_source_periodic
  have hsmooth : IsSmooth form :=
    t93A06_periodic_form_descent_aux_smooth_of_pullback atlas form
      t93A06_periodic_form_descent_aux_source_smooth hpull
  refine ⟨form, hsmooth, hpull, ?_⟩
  intro other _ hother
  exact t93A06_periodic_form_descent_aux_pullback_injective atlas
    (hother.trans hpull.symm)

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

/-- The two coordinate coefficients of the pullback of a torus one-form. -/
def t93A06_pulledCoeff (atlas : SmoothAtlas)
    (η : let _ := atlas.charts; Form Plane Torus 1) (i : Fin 2) (x : Plane) : ℝ := by
  letI := atlas.charts
  exact (pullback projection η x) (fun _ : Fin 1 ↦ (Pi.single i (1 : ℝ) : Plane))

/-- Naturality of `exteriorDerivative` for the quotient local diffeomorphism.
This is isolated from the subsequent coordinate integration. -/
theorem t93A06_exact_integral_aux_pullback_d (atlas : SmoothAtlas)
    (η : let _ := atlas.charts; Form Plane Torus 1)
    (hη : letI := atlas.charts; IsSmooth η) :
    letI := atlas.charts
    pullback projection (exteriorDerivative η) =
      exteriorDerivative (E := Plane) (M := Plane) (pullback projection η) := by
  sorry

lemma t93A06_exact_integral_aux_coeff_smooth_aux_global
    (atlas : SmoothAtlas)
    (η : let _ := atlas.charts; Form Plane Torus 1)
    (hη : letI := atlas.charts; IsSmooth η) (i : Fin 2) :
    ContDiff ℝ 1 (t93A06_pulledCoeff atlas η i) := by
  sorry

theorem t93A06_exact_integral_aux_coeff_smooth (atlas : SmoothAtlas)
    (η : let _ := atlas.charts; Form Plane Torus 1)
    (hη : letI := atlas.charts; IsSmooth η) :
    (∀ y : ℝ, ContDiff ℝ 1
      (fun x ↦ t93A06_pulledCoeff atlas η 1 ![x, y])) ∧
    (∀ x : ℝ, ContDiff ℝ 1
      (fun y ↦ t93A06_pulledCoeff atlas η 0 ![x, y])) := by
  have h0 := t93A06_exact_integral_aux_coeff_smooth_aux_global atlas η hη 0
  have h1 := t93A06_exact_integral_aux_coeff_smooth_aux_global atlas η hη 1
  constructor
  · intro y
    apply h1.comp
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp <;> fun_prop
  · intro x
    apply h0.comp
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp <;> fun_prop

/-- Coordinate formula for the integral of an exterior derivative.  The
naturality equality is an explicit input so this leaf is parallel to it. -/
theorem t93A06_exact_integral_aux_square_formula (atlas : SmoothAtlas)
    (η : let _ := atlas.charts; Form Plane Torus 1)
    (hnat : letI := atlas.charts
      pullback projection (exteriorDerivative η) =
        exteriorDerivative (E := Plane) (M := Plane) (pullback projection η))
    (hC1 : ∀ i : Fin 2, ContDiff ℝ 1 (t93A06_pulledCoeff atlas η i)) :
    letI := atlas.charts
    torusIntegral (exteriorDerivative η) =
      (∫ y : ℝ in 0..1, ∫ x : ℝ in 0..1,
        deriv (fun s ↦ t93A06_pulledCoeff atlas η 1 ![s, y]) x) -
      (∫ y : ℝ in 0..1, ∫ x : ℝ in 0..1,
        deriv (fun t ↦ t93A06_pulledCoeff atlas η 0 ![x, t]) y) := by
  sorry

/-- One-variable FTC for the `x` derivative, already integrated in `y`. -/
theorem t93A06_exact_integral_aux_ftc_x
    (Q : ℝ → ℝ → ℝ) (hQ : ∀ y, ContDiff ℝ 1 (fun x ↦ Q x y)) :
    (∫ y : ℝ in 0..1, ∫ x : ℝ in 0..1, deriv (fun s ↦ Q s y) x) =
      ∫ y : ℝ in 0..1, (Q 1 y - Q 0 y) := by
  sorry

/-- Seat: the pulled-back coefficients are jointly `C¹` in `(x, y)`
(compose `t93A06_exact_integral_aux_coeff_smooth_aux_global` with the
continuous linear map `(x, y) ↦ ![x, y]`). -/
-- BEGIN SEAT AREA
theorem t93A06_exact_integral_aux_joint_C1 (atlas : SmoothAtlas)
    (η : let _ := atlas.charts; Form Plane Torus 1)
    (hη : letI := atlas.charts; IsSmooth η) (i : Fin 2) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ t93A06_pulledCoeff atlas η i ![p.1, p.2]) := by
  sorry
-- END SEAT AREA

/-- One-variable FTC for the `y` derivative, already integrated in `x`. -/
theorem t93A06_exact_integral_aux_ftc_y
    (P : ℝ → ℝ → ℝ) (hP : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ P p.1 p.2)) :
    (∫ y : ℝ in 0..1, ∫ x : ℝ in 0..1, deriv (fun t ↦ P x t) y) =
      ∫ x : ℝ in 0..1, (P x 1 - P x 0) := by
  sorry

/-- Pullback coefficients agree on opposite sides of the unit square. -/
theorem t93A06_exact_integral_aux_periodic (atlas : SmoothAtlas)
    (η : let _ := atlas.charts; Form Plane Torus 1) :
    (∀ y : ℝ, t93A06_pulledCoeff atlas η 1 ![1, y] =
      t93A06_pulledCoeff atlas η 1 ![0, y]) ∧
    (∀ x : ℝ, t93A06_pulledCoeff atlas η 0 ![x, 1] =
      t93A06_pulledCoeff atlas η 0 ![x, 0]) := by
  sorry

/-- The two FTC boundary terms vanish under opposite-edge periodicity. -/
theorem t93A06_exact_integral_aux_boundary_cancel
    (P Q : ℝ → ℝ → ℝ)
    (hQ : ∀ y, Q 1 y = Q 0 y) (hP : ∀ x, P x 1 = P x 0) :
    (∫ y : ℝ in 0..1, (Q 1 y - Q 0 y)) -
      (∫ x : ℝ in 0..1, (P x 1 - P x 0)) = 0 := by
  sorry

/-- On this closed quotient torus, a smooth exact top form has zero
fundamental-square integral.  The proof is now only assembly of naturality,
coordinate FTC, and periodic cancellation. -/
theorem t93A06_not_exact_of_integral_quarter (atlas : SmoothAtlas)
    (form : let _ := atlas.charts; Form Plane Torus 2)
    (hsmooth : letI := atlas.charts; IsSmooth form)
    (hint : letI := atlas.charts; torusIntegral form = 1 / 4) :
    letI := atlas.charts
    ¬ IsExact form := by
  letI := atlas.charts
  rintro ⟨η, hη, rfl⟩
  have hnat := t93A06_exact_integral_aux_pullback_d atlas η hη
  have hsquare := t93A06_exact_integral_aux_square_formula atlas η hnat
    (fun i ↦ t93A06_exact_integral_aux_coeff_smooth_aux_global atlas η hη i)
  let P : ℝ → ℝ → ℝ := fun x y ↦ t93A06_pulledCoeff atlas η 0 ![x, y]
  let Q : ℝ → ℝ → ℝ := fun x y ↦ t93A06_pulledCoeff atlas η 1 ![x, y]
  obtain ⟨hQy, hPx⟩ := t93A06_exact_integral_aux_coeff_smooth atlas η hη
  have hftcx := t93A06_exact_integral_aux_ftc_x Q hQy
  have hftcy := t93A06_exact_integral_aux_ftc_y P
    (t93A06_exact_integral_aux_joint_C1 atlas η hη 0)
  obtain ⟨hQper, hPper⟩ := t93A06_exact_integral_aux_periodic atlas η
  have hcancel := t93A06_exact_integral_aux_boundary_cancel P Q hQper hPper
  have hz : torusIntegral (exteriorDerivative η) = 0 := by
    rw [hsquare]
    rw [hftcx, hftcy]
    exact hcancel
  linarith

/-- Coordinate calculus for the explicit primitive: it is smooth and its
exterior derivative is the source form. -/
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
