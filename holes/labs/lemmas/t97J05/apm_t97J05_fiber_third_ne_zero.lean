import Mathlib

open Set
open scoped ContDiff Manifold
noncomputable section

abbrev apm_t97J05_R3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t97J05_R2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t97J05_R1 := EuclideanSpace ℝ (Fin 1)

def apm_t97J05_f (q : apm_t97J05_R3) : apm_t97J05_R2 :=
  WithLp.toLp 2 ![Real.exp (q 0) * Real.cos (q 1), q 0 * q 2]
def apm_t97J05_p : apm_t97J05_R3 := WithLp.toLp 2 ![(1 : ℝ), Real.pi / 2, 1]
def apm_t97J05_value : apm_t97J05_R2 := WithLp.toLp 2 ![(0 : ℝ), 1]
def apm_t97J05_W : Set apm_t97J05_R3 := apm_t97J05_f ⁻¹' {apm_t97J05_value}
def apm_t97J05_gamma (t : ℝ) : apm_t97J05_R3 :=
  WithLp.toLp 2 ![t, Real.pi / 2, 1 / t]
def apm_t97J05_parameterDomain : Set ℝ := Ioo (1 / 2 : ℝ) (3 / 2 : ℝ)
def apm_t97J05_parameterTarget : Set apm_t97J05_R3 :=
  {q | q ∈ apm_t97J05_W ∧ q 0 ∈ apm_t97J05_parameterDomain ∧ q 1 ∈ Ioo (0 : ℝ) Real.pi}

def apm_t97J05_IsSmoothSubmanifold (s : Set apm_t97J05_R3) : Prop :=
  ∃ charts : ChartedSpace apm_t97J05_R1 s,
    let _ := charts
    IsManifold (𝓘(ℝ, apm_t97J05_R1)) (⊤ : ℕ∞) s ∧
      ContMDiff (𝓘(ℝ, apm_t97J05_R1)) (𝓘(ℝ, apm_t97J05_R3))
        (⊤ : ℕ∞) (Subtype.val : s → apm_t97J05_R3) ∧
      Topology.IsEmbedding (Subtype.val : s → apm_t97J05_R3) ∧
      ∀ x : s, Function.Injective
        (mfderiv (𝓘(ℝ, apm_t97J05_R1)) (𝓘(ℝ, apm_t97J05_R3))
          (Subtype.val : s → apm_t97J05_R3) x)

lemma apm_t97J05_f_gamma_eq_value {t : ℝ} (ht : t ∈ apm_t97J05_parameterDomain) :
    apm_t97J05_f (apm_t97J05_gamma t) = apm_t97J05_value := by
  have ht0 : t ≠ 0 := by dsimp [apm_t97J05_parameterDomain] at ht; linarith [ht.1]
  ext i
  fin_cases i <;> simp [apm_t97J05_f, apm_t97J05_gamma, apm_t97J05_value, ht0,
    Real.cos_pi_div_two]

lemma apm_t97J05_gamma_bijOn :
    Set.BijOn apm_t97J05_gamma apm_t97J05_parameterDomain apm_t97J05_parameterTarget := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact ⟨apm_t97J05_f_gamma_eq_value ht, ht, by simp [apm_t97J05_gamma, Real.pi_pos]⟩
  · intro x hx y hy hxy
    have h := congrArg (fun q : apm_t97J05_R3 ↦ q 0) hxy
    simpa [apm_t97J05_gamma] using h
  · intro q hq
    refine ⟨q 0, hq.2.1, ?_⟩
    have hfirst := congrArg (fun u : apm_t97J05_R2 ↦ u 0) hq.1
    have hsecond := congrArg (fun u : apm_t97J05_R2 ↦ u 1) hq.1
    have hcos : Real.cos (q 1) = 0 := by
      simpa [apm_t97J05_f, apm_t97J05_value, Real.exp_ne_zero] using hfirst
    have hy : q 1 = Real.pi / 2 := by
      apply Real.strictAntiOn_cos.injOn
      · exact ⟨le_of_lt hq.2.2.1, le_of_lt hq.2.2.2⟩
      · constructor <;> linarith [Real.pi_pos]
      · simpa [hcos, Real.cos_pi_div_two]
    have hx0 : q 0 ≠ 0 := ne_of_gt (lt_trans (by norm_num) hq.2.1.1)
    ext i
    fin_cases i
    · simp [apm_t97J05_gamma]
    · simpa [apm_t97J05_gamma] using hy.symm
    · simp [apm_t97J05_gamma]
      rw [inv_eq_one_div]
      apply (div_eq_iff hx0).2
      have hmul : q 0 * q 2 = 1 := by
        simpa [apm_t97J05_f, apm_t97J05_value] using hsecond
      nlinarith [hmul]

theorem apm_t97J05_derivative_and_rank :
    (∀ h : apm_t97J05_R3,
      fderiv ℝ apm_t97J05_f apm_t97J05_p h =
        WithLp.toLp 2 ![-Real.exp 1 * h 1, h 0 + h 2]) ∧
    Function.Surjective (fderiv ℝ apm_t97J05_f apm_t97J05_p) := by
  let g : apm_t97J05_R3 → (Fin 2 → ℝ) := fun q =>
    ![Real.exp (q 0) * Real.cos (q 1), q 0 * q 2]
  have hg : DifferentiableAt ℝ g apm_t97J05_p := by
    apply differentiableAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [g] <;> fun_prop
  have hc := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 (g apm_t97J05_p)).comp
    apm_t97J05_p hg.hasFDerivAt
  have hgv (h : apm_t97J05_R3) :
      fderiv ℝ g apm_t97J05_p h =
        ![-Real.exp 1 * h 1, h 0 + h 2] := by
    have hdj (j : Fin 3) :
        DifferentiableAt ℝ (fun q : apm_t97J05_R3 => q j) apm_t97J05_p := by
      exact (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j).differentiableAt
    have hj (j : Fin 3) :
        fderiv ℝ (fun q : apm_t97J05_R3 => q j) apm_t97J05_p h = h j := by
      let P : apm_t97J05_R3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) j
      have hd := P.hasFDerivAt (x := apm_t97J05_p)
      exact congrArg (fun L : apm_t97J05_R3 →L[ℝ] ℝ => L h) hd.fderiv
    rw [fderiv_pi]
    · ext i
      fin_cases i
      · dsimp [g]
        rw [fderiv_fun_mul]
        · rw [fderiv_exp, fderiv_cos]
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
            smul_eq_mul]
          rw [hj, hj]
          simp [apm_t97J05_p, Real.cos_pi_div_two, Real.sin_pi_div_two]
          all_goals exact hdj _
        · exact (hdj 0).exp
        · exact (hdj 1).cos
      · dsimp [g]
        rw [fderiv_fun_mul]
        · simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
            smul_eq_mul]
          rw [hj, hj]
          simp [apm_t97J05_p]
          ring
        all_goals exact hdj _
    · intro i
      fin_cases i <;> dsimp [g] <;> fun_prop
  have hformula (h : apm_t97J05_R3) :
      fderiv ℝ apm_t97J05_f apm_t97J05_p h =
        WithLp.toLp 2 ![-Real.exp 1 * h 1, h 0 + h 2] := by
    change fderiv ℝ (WithLp.toLp 2 ∘ g) apm_t97J05_p h = _
    rw [hc.fderiv]
    change WithLp.toLp 2 (fderiv ℝ g apm_t97J05_p h) = _
    rw [hgv]
  refine ⟨hformula, ?_⟩
  intro y
  let h : apm_t97J05_R3 :=
    WithLp.toLp 2 ![y 1, -(y 0 / Real.exp 1), 0]
  refine ⟨h, ?_⟩
  rw [hformula]
  ext i
  fin_cases i
  · simp [h]
    field_simp [Real.exp_ne_zero]
  · simp [h]

theorem apm_t97J05_gamma_smooth :
    ContDiffOn ℝ ∞ apm_t97J05_gamma apm_t97J05_parameterDomain := by
  intro t ht
  have ht0 : t ≠ 0 := by
    simp only [apm_t97J05_parameterDomain, mem_Ioo] at ht
    linarith [ht.1]
  unfold apm_t97J05_gamma
  rw [contDiffWithinAt_piLp]
  intro i
  fin_cases i <;> simp
  · exact (contDiffWithinAt_id :
      ContDiffWithinAt ℝ ∞ (fun x : ℝ => x) apm_t97J05_parameterDomain t)
  · exact (contDiffWithinAt_const :
      ContDiffWithinAt ℝ ∞ (fun _ : ℝ => Real.pi / 2) apm_t97J05_parameterDomain t)
  · simpa only [id_eq] using
      (contDiffWithinAt_id.inv ht0 :
        ContDiffWithinAt ℝ ∞ (fun x : ℝ => (id x)⁻¹) apm_t97J05_parameterDomain t)

/-- The equations defining the fiber force the third coordinate to be nonzero
(`q 0 * q 2 = 1`). -/
-- BEGIN SEAT AREA
lemma apm_t97J05_fiber_third_ne_zero (q : apm_t97J05_R3)
    (hq : q ∈ apm_t97J05_W) : q 2 ≠ 0 := by
  sorry
-- END SEAT AREA

/-- At every point of the fiber, the trigonometric factor used in the regularity
calculation is nonzero. -/
lemma apm_t97J05_fiber_sin_ne_zero (q : apm_t97J05_R3)
    (hq : q ∈ apm_t97J05_W) : Real.sin (q 1) ≠ 0 := by
  sorry

/-- The completion of `f` by the last coordinate, used uniformly at every fiber
point. -/
def apm_t97J05_regular_aux_H (q : apm_t97J05_R3) : apm_t97J05_R3 :=
  WithLp.toLp 2 ![Real.exp (q 0) * Real.cos (q 1), q 0 * q 2, q 2]

lemma apm_t97J05_regular_aux_smooth :
    ContDiff ℝ ∞ apm_t97J05_regular_aux_H := by
  sorry

/-- The derivative formula for the completed map at an arbitrary point. -/
lemma apm_t97J05_regular_aux_deriv_apply (q h : apm_t97J05_R3) :
    fderiv ℝ apm_t97J05_regular_aux_H q h =
      WithLp.toLp 2
        ![Real.exp (q 0) * Real.cos (q 1) * h 0 -
            Real.exp (q 0) * Real.sin (q 1) * h 1,
          q 2 * h 0 + q 0 * h 2, h 2] := by
  sorry

/-- The displayed derivative is invertible under precisely the two nonvanishing
conditions available on the fiber (the determinant is `q 2 * exp (q 0) * sin (q 1)`).  The conditions are explicit hypotheses so
this seat is independent of the fiber-equation seats. -/
lemma apm_t97J05_regular_aux_deriv_bijective (q : apm_t97J05_R3)
    (hz : q 2 ≠ 0) (hs : Real.sin (q 1) ≠ 0) :
    Function.Bijective (fderiv ℝ apm_t97J05_regular_aux_H q) := by
  sorry

/-- An inverse-function chart around an arbitrary point where the completed
map has bijective derivative.  Bijectivity is passed explicitly to keep this
seat parallel to the derivative calculation. -/
lemma apm_t97J05_regular_aux_local_inverse (q : apm_t97J05_R3)
    (hb : Function.Bijective (fderiv ℝ apm_t97J05_regular_aux_H q)) :
    ∃ e : OpenPartialHomeomorph apm_t97J05_R3 apm_t97J05_R3,
      q ∈ e.source ∧ apm_t97J05_regular_aux_H q ∈ e.target ∧
      (e : apm_t97J05_R3 → apm_t97J05_R3) = apm_t97J05_regular_aux_H ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  sorry

/-- A local flat model of the fiber.  The local inverse is supplied as a
hypothesis, so proving this statement requires only unpacking the first two
coordinates of `H`. -/
lemma apm_t97J05_regular_aux_flattens_fiber
    (e : OpenPartialHomeomorph apm_t97J05_R3 apm_t97J05_R3)
    (he : (e : apm_t97J05_R3 → apm_t97J05_R3) = apm_t97J05_regular_aux_H) :
    ∀ z ∈ e.source,
      z ∈ apm_t97J05_W ↔ e z 0 = 0 ∧ e z 1 = 1 := by
  sorry

/-- LIBRARY: global regular-level/embedded-submanifold assembly.  This is the
remaining missing Mathlib foundation: compatible subtype charts and the
smooth embedded inclusion are constructed from flat local fiber models. -/
lemma apm_t97J05_regular_fiber_global_assembly
    (hlocal : ∀ q ∈ apm_t97J05_W,
      ∃ e : OpenPartialHomeomorph apm_t97J05_R3 apm_t97J05_R3,
        q ∈ e.source ∧ ContDiffOn ℝ ∞ e e.source ∧
        ContDiffOn ℝ ∞ e.symm e.target ∧
        ∀ z ∈ e.source,
          z ∈ apm_t97J05_W ↔ e z 0 = 0 ∧ e z 1 = 1) :
    apm_t97J05_IsSmoothSubmanifold apm_t97J05_W := by
  sorry

theorem apm_t97J05_regular_fiber_embedded :
    apm_t97J05_IsSmoothSubmanifold apm_t97J05_W := by
  apply apm_t97J05_regular_fiber_global_assembly
  intro q hq
  have hz := apm_t97J05_fiber_third_ne_zero q hq
  have hs := apm_t97J05_fiber_sin_ne_zero q hq
  have hb := apm_t97J05_regular_aux_deriv_bijective q hz hs
  rcases apm_t97J05_regular_aux_local_inverse q hb with
    ⟨e, hqsrc, _hqtarget, he, hes, heis⟩
  exact ⟨e, hqsrc, hes, heis,
    apm_t97J05_regular_aux_flattens_fiber e he⟩

def apm_t97J05_local_normal_form_aux_H (q : apm_t97J05_R3) : apm_t97J05_R3 :=
  WithLp.toLp 2 ![Real.exp (q 0) * Real.cos (q 1), q 0 * q 2, q 2]

lemma apm_t97J05_local_normal_form_aux_smooth :
    ContDiff ℝ ∞ apm_t97J05_local_normal_form_aux_H := by
  unfold apm_t97J05_local_normal_form_aux_H
  rw [contDiff_piLp]
  intro i
  fin_cases i <;> simp <;> fun_prop

lemma apm_t97J05_local_normal_form_aux_deriv_apply (h : apm_t97J05_R3) :
    fderiv ℝ apm_t97J05_local_normal_form_aux_H apm_t97J05_p h =
      WithLp.toLp 2 ![-Real.exp 1 * h 1, h 0 + h 2, h 2] := by
  let g : apm_t97J05_R3 → (Fin 3 → ℝ) := fun q =>
    ![Real.exp (q 0) * Real.cos (q 1), q 0 * q 2, q 2]
  have hg : DifferentiableAt ℝ g apm_t97J05_p := by
    apply differentiableAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [g] <;> fun_prop
  have hc := (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 (g apm_t97J05_p)).comp
    apm_t97J05_p hg.hasFDerivAt
  have hdj (j : Fin 3) :
      DifferentiableAt ℝ (fun q : apm_t97J05_R3 => q j) apm_t97J05_p := by
    exact (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j).differentiableAt
  have hj (j : Fin 3) :
      fderiv ℝ (fun q : apm_t97J05_R3 => q j) apm_t97J05_p h = h j := by
    let P : apm_t97J05_R3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) j
    have hd := P.hasFDerivAt (x := apm_t97J05_p)
    exact congrArg (fun L : apm_t97J05_R3 →L[ℝ] ℝ => L h) hd.fderiv
  have hgv :
      fderiv ℝ g apm_t97J05_p h =
        ![-Real.exp 1 * h 1, h 0 + h 2, h 2] := by
    rw [fderiv_pi]
    · ext i
      fin_cases i
      · dsimp [g]
        rw [fderiv_fun_mul]
        · rw [fderiv_exp, fderiv_cos]
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
            smul_eq_mul]
          rw [hj, hj]
          simp [apm_t97J05_p, Real.cos_pi_div_two, Real.sin_pi_div_two]
          all_goals exact hdj _
        · exact (hdj 0).exp
        · exact (hdj 1).cos
      · dsimp [g]
        rw [fderiv_fun_mul]
        · simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
            smul_eq_mul]
          rw [hj, hj]
          simp [apm_t97J05_p]
          ring
        all_goals exact hdj _
      · dsimp [g]
        rw [hj]
    · intro i
      fin_cases i <;> dsimp [g] <;> fun_prop
  change fderiv ℝ (WithLp.toLp 2 ∘ g) apm_t97J05_p h = _
  rw [hc.fderiv]
  change WithLp.toLp 2 (fderiv ℝ g apm_t97J05_p h) = _
  rw [hgv]

lemma apm_t97J05_local_normal_form_aux_deriv_bij :
    Function.Bijective (fderiv ℝ apm_t97J05_local_normal_form_aux_H apm_t97J05_p) := by
  constructor
  · intro x y hxy
    have h0 := congrArg (fun q : apm_t97J05_R3 ↦ q 0) hxy
    have h1 := congrArg (fun q : apm_t97J05_R3 ↦ q 1) hxy
    have h2 := congrArg (fun q : apm_t97J05_R3 ↦ q 2) hxy
    simp only [apm_t97J05_local_normal_form_aux_deriv_apply] at h0 h1 h2
    ext i
    fin_cases i
    · simp at h1 h2
      simpa using sub_eq_zero.mp (by linarith : x 0 - y 0 = 0)
    · simpa using h0
    · simpa using h2
  · intro y
    let x : apm_t97J05_R3 := WithLp.toLp 2 ![y 1 - y 2, -y 0 / Real.exp 1, y 2]
    refine ⟨x, ?_⟩
    ext i
    fin_cases i <;> simp [apm_t97J05_local_normal_form_aux_deriv_apply, x] <;>
      field_simp [Real.exp_ne_zero]

lemma apm_t97J05_local_normal_form_aux_Hp :
    apm_t97J05_local_normal_form_aux_H apm_t97J05_p =
      WithLp.toLp 2 ![(0 : ℝ), 1, 1] := by
  ext i
  fin_cases i <;>
    simp [apm_t97J05_local_normal_form_aux_H, apm_t97J05_p,
      Real.cos_pi_div_two]

lemma apm_t97J05_local_normal_form_aux_inverse_at_p :
    ∃ e : OpenPartialHomeomorph apm_t97J05_R3 apm_t97J05_R3,
      apm_t97J05_p ∈ e.source ∧
      apm_t97J05_local_normal_form_aux_H apm_t97J05_p ∈ e.target ∧
      (e : apm_t97J05_R3 → apm_t97J05_R3) = apm_t97J05_local_normal_form_aux_H ∧
      ContDiffAt ℝ ∞ e.symm
        (apm_t97J05_local_normal_form_aux_H apm_t97J05_p) := by
  let L : apm_t97J05_R3 ≃L[ℝ] apm_t97J05_R3 :=
    ContinuousLinearEquiv.ofBijective
      (fderiv ℝ apm_t97J05_local_normal_form_aux_H apm_t97J05_p)
      (LinearMap.ker_eq_bot.mpr apm_t97J05_local_normal_form_aux_deriv_bij.1)
      (LinearMap.range_eq_top.mpr apm_t97J05_local_normal_form_aux_deriv_bij.2)
  have hH : ContDiffAt ℝ ∞ apm_t97J05_local_normal_form_aux_H apm_t97J05_p :=
    apm_t97J05_local_normal_form_aux_smooth.contDiffAt
  have hHL : HasFDerivAt apm_t97J05_local_normal_form_aux_H
      (L : apm_t97J05_R3 →L[ℝ] apm_t97J05_R3) apm_t97J05_p := by
    apply (hH.differentiableAt (by simp)).hasFDerivAt.congr_fderiv
    exact ContinuousLinearEquiv.coe_ofBijective _ _ _ |>.symm
  let e := hH.toOpenPartialHomeomorph apm_t97J05_local_normal_form_aux_H hHL (by simp)
  refine ⟨e, hH.mem_toOpenPartialHomeomorph_source hHL (by simp),
    hH.image_mem_toOpenPartialHomeomorph_target hHL (by simp), rfl, ?_⟩
  simpa [e] using hH.to_localInverse hHL (by simp)

lemma apm_t97J05_local_normal_form_aux_smooth_local_inverse :
    ∃ e : OpenPartialHomeomorph apm_t97J05_R3 apm_t97J05_R3,
      apm_t97J05_p ∈ e.source ∧
      apm_t97J05_local_normal_form_aux_H apm_t97J05_p ∈ e.target ∧
      (e : apm_t97J05_R3 → apm_t97J05_R3) = apm_t97J05_local_normal_form_aux_H ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  rcases apm_t97J05_local_normal_form_aux_inverse_at_p with
    ⟨e₀, hp, hHp, he₀, he₀inv⟩
  let U : Set apm_t97J05_R3 :=
    {x | IsUnit (fderiv ℝ apm_t97J05_local_normal_form_aux_H x)}
  have hUopen : IsOpen U := by
    exact Units.isOpen.preimage
      (apm_t97J05_local_normal_form_aux_smooth.continuous_fderiv (by simp))
  have hpU : apm_t97J05_p ∈ U := by
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr
      apm_t97J05_local_normal_form_aux_deriv_bij
  let e := e₀.restrOpen U hUopen
  have hp' : apm_t97J05_p ∈ e.source := ⟨hp, hpU⟩
  refine ⟨e, hp', ?_, ?_, ?_, ?_⟩
  · rw [← he₀]
    exact e.map_source hp'
  · simpa [e] using he₀
  · rw [show (e : apm_t97J05_R3 → apm_t97J05_R3) =
        apm_t97J05_local_normal_form_aux_H by simpa [e] using he₀]
    exact apm_t97J05_local_normal_form_aux_smooth.contDiffOn
  · intro y hy
    have hx : e.symm y ∈ U := by
      exact (e.map_target hy).2
    have hb : Function.Bijective
        (fderiv ℝ apm_t97J05_local_normal_form_aux_H (e.symm y)) :=
      ContinuousLinearMap.isUnit_iff_bijective.mp hx
    let L : apm_t97J05_R3 ≃L[ℝ] apm_t97J05_R3 :=
      ContinuousLinearEquiv.ofBijective
        (fderiv ℝ apm_t97J05_local_normal_form_aux_H (e.symm y))
        (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
    apply (e.contDiffAt_symm (f₀' := L) hy ?_ ?_).contDiffWithinAt
    · have hd := (apm_t97J05_local_normal_form_aux_smooth.differentiable
          (by simp) (e.symm y)).hasFDerivAt
      rw [show (e : apm_t97J05_R3 → apm_t97J05_R3) =
          apm_t97J05_local_normal_form_aux_H by simpa [e] using he₀]
      apply hd.congr_fderiv
      exact ContinuousLinearEquiv.coe_ofBijective _ _ _ |>.symm
    · rw [show (e : apm_t97J05_R3 → apm_t97J05_R3) =
          apm_t97J05_local_normal_form_aux_H by simpa [e] using he₀]
      exact apm_t97J05_local_normal_form_aux_smooth.contDiffAt

theorem apm_t97J05_local_normal_form :
    ∃ (φ : OpenPartialHomeomorph apm_t97J05_R3 apm_t97J05_R3)
        (ψ : OpenPartialHomeomorph apm_t97J05_R2 apm_t97J05_R2),
      0 ∈ φ.source ∧ φ 0 = apm_t97J05_p ∧
      apm_t97J05_value ∈ ψ.source ∧ ψ apm_t97J05_value = 0 ∧
      ContDiffOn ℝ ∞ φ φ.source ∧ ContDiffOn ℝ ∞ φ.symm φ.target ∧
      ContDiffOn ℝ ∞ ψ ψ.source ∧ ContDiffOn ℝ ∞ ψ.symm ψ.target ∧
      ∀ q ∈ φ.source, apm_t97J05_f (φ q) ∈ ψ.source ∧
        ψ (apm_t97J05_f (φ q)) = WithLp.toLp 2 ![q 0, q 1] := by
  rcases apm_t97J05_local_normal_form_aux_smooth_local_inverse with
    ⟨e₀, hp, hHp, he₀, he₀smooth, he₀inv⟩
  let T : apm_t97J05_R3 ≃ₜ apm_t97J05_R3 :=
    Homeomorph.addLeft (apm_t97J05_local_normal_form_aux_H apm_t97J05_p)
  let φ₀ : OpenPartialHomeomorph apm_t97J05_R3 apm_t97J05_R3 :=
    T.transOpenPartialHomeomorph e₀.symm
  let φ : OpenPartialHomeomorph apm_t97J05_R3 apm_t97J05_R3 := φ₀
  let ψ : OpenPartialHomeomorph apm_t97J05_R2 apm_t97J05_R2 :=
    (Homeomorph.addLeft (-apm_t97J05_value)).toOpenPartialHomeomorph
  refine ⟨φ, ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change 0 ∈ φ₀.source
    rw [Homeomorph.transOpenPartialHomeomorph_source]
    simpa [T] using hHp
  · change φ₀ 0 = apm_t97J05_p
    change e₀.symm (apm_t97J05_local_normal_form_aux_H apm_t97J05_p + 0) = _
    rw [← he₀]
    simpa using e₀.left_inv hp
  · simp [ψ]
  · simp [ψ]
  · intro x hx
    change ContDiffWithinAt ℝ ∞ (e₀.symm ∘ T) φ₀.source x
    apply (he₀inv (T x) (by simpa [φ₀] using hx)).comp x
      ((contDiff_const.add contDiff_id).contDiffWithinAt)
    exact fun y hy => by simpa [φ₀] using hy
  · intro x hx
    change ContDiffWithinAt ℝ ∞ (T.symm ∘ e₀) φ₀.target x
    have hs := he₀smooth x (by simpa [φ₀] using hx)
    have hout : ContDiff ℝ ∞ (fun y : apm_t97J05_R3 =>
        y - apm_t97J05_local_normal_form_aux_H apm_t97J05_p) :=
      contDiff_id.sub contDiff_const
    have hc := hout.contDiffWithinAt.comp x hs
      (fun y hy => Set.mem_univ _)
    simpa [T, Function.comp_def, sub_eq_add_neg, add_comm] using hc
  · intro x hx
    exact ((contDiff_const.add contDiff_id).contDiffWithinAt)
  · intro x hx
    exact ((contDiff_const.add contDiff_id).contDiffWithinAt)
  · intro q hq
    constructor
    · simp [ψ]
    · have hq₀ : q ∈ φ₀.source := by
        exact hq
      have hTq : T q ∈ e₀.target := by
        simpa [φ₀] using hq₀
      have hinv : e₀ (φ₀ q) = T q := e₀.right_inv hTq
      have hHq : apm_t97J05_local_normal_form_aux_H (φ q) =
          apm_t97J05_local_normal_form_aux_H apm_t97J05_p + q := by
        simpa [φ, φ₀, T, add_comm, he₀] using hinv
      ext i
      fin_cases i
      · have h := congrArg (fun x : apm_t97J05_R3 ↦ x 0) hHq
        simpa [ψ, apm_t97J05_f, apm_t97J05_value,
          apm_t97J05_local_normal_form_aux_H, apm_t97J05_p,
          Real.cos_pi_div_two] using h
      · have h := congrArg (fun x : apm_t97J05_R3 ↦ x 1) hHq
        have h' := congrArg (fun z : ℝ => z - 1) h
        simpa [ψ, apm_t97J05_f, apm_t97J05_value, sub_eq_add_neg, add_comm,
          apm_t97J05_local_normal_form_aux_H, apm_t97J05_p] using h'
/-
  let L : apm_t97J05_R3 ≃L[ℝ] apm_t97J05_R3 :=
    ContinuousLinearEquiv.ofBijective
      (fderiv ℝ apm_t97J05_local_normal_form_aux_H apm_t97J05_p)
      (LinearMap.ker_eq_bot.mpr apm_t97J05_local_normal_form_aux_deriv_bij.1)
      (LinearMap.range_eq_top.mpr apm_t97J05_local_normal_form_aux_deriv_bij.2)
  have hH : ContDiffAt ℝ ∞ apm_t97J05_local_normal_form_aux_H apm_t97J05_p :=
    apm_t97J05_local_normal_form_aux_smooth.contDiffAt
  have hHL : HasFDerivAt apm_t97J05_local_normal_form_aux_H
      (L : apm_t97J05_R3 →L[ℝ] apm_t97J05_R3) apm_t97J05_p := by
    apply (hH.differentiableAt (by simp)).hasFDerivAt.congr_fderiv
    exact ContinuousLinearEquiv.coe_ofBijective _ _ _ |>.symm
  let e₀ : OpenPartialHomeomorph apm_t97J05_R3 apm_t97J05_R3 :=
    hH.toOpenPartialHomeomorph apm_t97J05_local_normal_form_aux_H hHL (by simp)
  let T : apm_t97J05_R3 ≃ₜ apm_t97J05_R3 :=
    Homeomorph.addLeft (apm_t97J05_local_normal_form_aux_H apm_t97J05_p)
  let φ₀ : OpenPartialHomeomorph apm_t97J05_R3 apm_t97J05_R3 :=
    T.transOpenPartialHomeomorph e₀.symm
  let n : WithTop ℕ∞ := ↑(⊤ : ℕ∞)
  let φ : OpenPartialHomeomorph apm_t97J05_R3 apm_t97J05_R3 :=
    φ₀.restrContDiff ℝ n (by simp [n])
  let ψ : OpenPartialHomeomorph apm_t97J05_R2 apm_t97J05_R2 :=
    (Homeomorph.addLeft (-apm_t97J05_value)).toOpenPartialHomeomorph
  refine ⟨φ, ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change 0 ∈ (φ₀.restrContDiff ℝ n _).source
    simp only [OpenPartialHomeomorph.restrContDiff_source]
    refine ⟨?_, ?_, ?_⟩
    · rw [Homeomorph.transOpenPartialHomeomorph_source]
      change apm_t97J05_local_normal_form_aux_H apm_t97J05_p ∈ e₀.target
      exact hH.image_mem_toOpenPartialHomeomorph_target hHL (by simp)
    · change ContDiffAt ℝ n φ₀ 0
      dsimp [φ₀, T]
      apply (hH.to_localInverse hHL (by simp)).comp_of_eq 0
        ((contDiffAt_const.add contDiffAt_id).mono (by simp [n]))
      simp
    · change ContDiffAt ℝ n φ₀.symm (φ₀ 0)
      dsimp [φ₀, T]
      fun_prop
  · change φ₀ 0 = apm_t97J05_p
    change e₀.symm (apm_t97J05_local_normal_form_aux_H apm_t97J05_p + 0) = _
    simpa using e₀.left_inv
      (hH.mem_toOpenPartialHomeomorph_source hHL (by simp))
  · simp [ψ]
  · simp [ψ]
  · exact OpenPartialHomeomorph.contDiffOn_restrContDiff_source ℝ φ₀ (by simp [n])
  · exact OpenPartialHomeomorph.contDiffOn_restrContDiff_target ℝ φ₀ (by simp [n])
  · intro x hx
    exact ((contDiff_const.add contDiff_id).contDiffWithinAt)
  · intro x hx
    exact ((contDiff_const.add contDiff_id).contDiffWithinAt)
  · intro q hq
    constructor
    · simp [ψ]
    · have hq₀ : q ∈ φ₀.source := by
        exact (show q ∈ (φ₀.restrContDiff ℝ n _).source from hq).1
      have hTq : T q ∈ e₀.target := by
        simpa [φ₀] using hq₀
      have hinv : e₀ (φ₀ q) = T q := by
        exact e₀.right_inv hTq
      have hHq : apm_t97J05_local_normal_form_aux_H (φ q) =
          apm_t97J05_local_normal_form_aux_H apm_t97J05_p + q := by
        simpa [φ, φ₀, e₀, T, add_comm] using hinv
      ext i
      fin_cases i
      · have h := congrArg (fun x : apm_t97J05_R3 ↦ x 0) hHq
        simpa [ψ, apm_t97J05_f, apm_t97J05_value,
          apm_t97J05_local_normal_form_aux_H, apm_t97J05_p,
          Real.cos_pi_div_two] using h
      · have h := congrArg (fun x : apm_t97J05_R3 ↦ x 1) hHq
        simpa [ψ, apm_t97J05_f, apm_t97J05_value,
          apm_t97J05_local_normal_form_aux_H, apm_t97J05_p] using h
-/

theorem apm_t97j05 :
    (∀ h : apm_t97J05_R3,
      fderiv ℝ apm_t97J05_f apm_t97J05_p h =
        WithLp.toLp 2 ![-Real.exp 1 * h 1, h 0 + h 2]) ∧
    Function.Surjective (fderiv ℝ apm_t97J05_f apm_t97J05_p) ∧
    apm_t97J05_IsSmoothSubmanifold apm_t97J05_W ∧
    ContDiffOn ℝ ∞ apm_t97J05_gamma apm_t97J05_parameterDomain ∧
    Set.BijOn apm_t97J05_gamma apm_t97J05_parameterDomain apm_t97J05_parameterTarget ∧
    ∃ (φ : OpenPartialHomeomorph apm_t97J05_R3 apm_t97J05_R3)
        (ψ : OpenPartialHomeomorph apm_t97J05_R2 apm_t97J05_R2),
      0 ∈ φ.source ∧ φ 0 = apm_t97J05_p ∧
      apm_t97J05_value ∈ ψ.source ∧ ψ apm_t97J05_value = 0 ∧
      ContDiffOn ℝ ∞ φ φ.source ∧ ContDiffOn ℝ ∞ φ.symm φ.target ∧
      ContDiffOn ℝ ∞ ψ ψ.source ∧ ContDiffOn ℝ ∞ ψ.symm ψ.target ∧
      ∀ q ∈ φ.source, apm_t97J05_f (φ q) ∈ ψ.source ∧
        ψ (apm_t97J05_f (φ q)) = WithLp.toLp 2 ![q 0, q 1] := by
  rcases apm_t97J05_derivative_and_rank with ⟨hderiv, hrank⟩
  exact ⟨hderiv, hrank, apm_t97J05_regular_fiber_embedded,
    apm_t97J05_gamma_smooth, apm_t97J05_gamma_bijOn, apm_t97J05_local_normal_form⟩

#print axioms apm_t97j05
