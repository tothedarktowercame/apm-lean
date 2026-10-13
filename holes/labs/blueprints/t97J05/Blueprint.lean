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

/-- LIBRARY: the regular-level theorem, including the induced manifold structure
and the immersion assertion for its subtype inclusion. -/
theorem apm_t97J05_regular_fiber_embedded :
    apm_t97J05_IsSmoothSubmanifold apm_t97J05_W := by
  sorry

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

theorem apm_t97J05_local_normal_form :
    ∃ (φ : OpenPartialHomeomorph apm_t97J05_R3 apm_t97J05_R3)
        (ψ : OpenPartialHomeomorph apm_t97J05_R2 apm_t97J05_R2),
      0 ∈ φ.source ∧ φ 0 = apm_t97J05_p ∧
      apm_t97J05_value ∈ ψ.source ∧ ψ apm_t97J05_value = 0 ∧
      ContDiffOn ℝ ∞ φ φ.source ∧ ContDiffOn ℝ ∞ φ.symm φ.target ∧
      ContDiffOn ℝ ∞ ψ ψ.source ∧ ContDiffOn ℝ ∞ ψ.symm ψ.target ∧
      ∀ q ∈ φ.source, apm_t97J05_f (φ q) ∈ ψ.source ∧
        ψ (apm_t97J05_f (φ q)) = WithLp.toLp 2 ![q 0, q 1] := by
  sorry

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
