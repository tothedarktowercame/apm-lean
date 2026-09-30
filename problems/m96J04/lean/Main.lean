import Mathlib

/-!
# APM m96J04

## Statement repairs

None.

## Encoding questions

The Hilbert-space example is stated on two copies of `ℓ²(ℕ,ℝ)`. The Banach-space
example is pinned to the Volterra operator on `C([0,1],ℝ)` by its pointwise
integral formula, rather than represented by an anonymous compact operator.
-/

noncomputable section

abbrev apm_m96j04_H := ℓ²(ℕ, ℝ) × ℓ²(ℕ, ℝ)
abbrev apm_m96j04_C := C(Set.Icc (0 : ℝ) 1, ℝ)

def apm_m96j04_extend (f : apm_m96j04_C) (x : ℝ) : ℝ :=
  if hx : x ∈ Set.Icc (0 : ℝ) 1 then f ⟨x, hx⟩ else 0

/-- Although the chosen zero extension need not be continuous across the
endpoints, its restriction to the integration interval is continuous. -/
lemma apm_m96j04_extend_continuousOn (f : apm_m96j04_C) :
    ContinuousOn (apm_m96j04_extend f) (Set.Icc (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  convert f.continuous using 1
  funext x
  simp [apm_m96j04_extend, x.property]

lemma apm_m96j04_extend_intervalIntegrable (f : apm_m96j04_C)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable (apm_m96j04_extend f) MeasureTheory.volume 0 t := by
  exact ((apm_m96j04_extend_continuousOn f).mono
    (Set.uIcc_subset_Icc (by norm_num) ht)).intervalIntegrable

lemma apm_m96j04_integral_hasDerivAt (f : apm_m96j04_C)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun u ↦ ∫ s in (0 : ℝ)..u, apm_m96j04_extend f s)
      (apm_m96j04_extend f t) t := by
  have hcont : ContinuousAt (apm_m96j04_extend f) t :=
    (apm_m96j04_extend_continuousOn f t ⟨ht.1.le, ht.2.le⟩).continuousAt
      (Icc_mem_nhds ht.1 ht.2)
  have hmeas : StronglyMeasurableAtFilter (apm_m96j04_extend f)
      (nhds t) MeasureTheory.volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      ((apm_m96j04_extend_continuousOn f).mono
        (fun _ hx ↦ ⟨hx.1.le, hx.2.le⟩)) t ht
  exact intervalIntegral.integral_hasDerivAt_right
    (apm_m96j04_extend_intervalIntegrable f ⟨ht.1.le, ht.2.le⟩)
    hmeas hcont

/-- The block operator from the Hilbert-space example, together with its
pointwise formula and compactness of all powers from the second onward. -/
lemma apm_m96j04_block_exists :
    ∃ A : apm_m96j04_H →L[ℝ] apm_m96j04_H,
      (∀ x y : ℓ²(ℕ, ℝ), A (x, y) = (y, 0)) ∧
      ∀ n : ℕ, 2 ≤ n → IsCompactOperator (A ^ n) := by
  let A : apm_m96j04_H →L[ℝ] apm_m96j04_H :=
    (ContinuousLinearMap.inl ℝ ℓ²(ℕ, ℝ) ℓ²(ℕ, ℝ)).comp
      (ContinuousLinearMap.snd ℝ ℓ²(ℕ, ℝ) ℓ²(ℕ, ℝ))
  refine ⟨A, ?_, ?_⟩
  · intro x y
    simp [A]
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hzero : A ^ (2 + k) = 0 := by
      rw [pow_add]
      simp [show A ^ 2 = 0 by ext z <;> simp [A, pow_two]]
    rw [hzero]
    exact isCompactOperator_zero

/-- Any nonzero-eigenvalue eigenvector of an operator with the Volterra
pointwise formula has the required zero initial value. -/
lemma apm_m96j04_eigenvector_zero_at_zero
    (V : apm_m96j04_C →L[ℝ] apm_m96j04_C)
    (hV : ∀ (f : apm_m96j04_C) (t : Set.Icc (0 : ℝ) 1),
      V f t = ∫ s in (0 : ℝ)..(t : ℝ), apm_m96j04_extend f s)
    (eigenvalue : ℝ) (heigen : eigenvalue ≠ 0) (f : apm_m96j04_C)
    (hf : V f = eigenvalue • f) :
    f ⟨0, by norm_num⟩ = 0 := by
  let t0 : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  have h := congrArg (fun g : apm_m96j04_C ↦ g t0) hf
  change V f t0 = eigenvalue * f t0 at h
  rw [hV] at h
  have h' : 0 = eigenvalue * f t0 := by simpa [t0] using h
  have ht0 : f t0 = 0 := (mul_eq_zero.mp h'.symm).resolve_left heigen
  simpa [t0] using ht0

/-- On the interior, the Volterra eigenvector equation is the scalar ODE
`f' = f / eigenvalue`. -/
lemma apm_m96j04_eigenvector_hasDerivAt
    (V : apm_m96j04_C →L[ℝ] apm_m96j04_C)
    (hV : ∀ (f : apm_m96j04_C) (t : Set.Icc (0 : ℝ) 1),
      V f t = ∫ s in (0 : ℝ)..(t : ℝ), apm_m96j04_extend f s)
    (eigenvalue : ℝ) (heigen : eigenvalue ≠ 0) (f : apm_m96j04_C)
    (hf : V f = eigenvalue • f) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (apm_m96j04_extend f)
      (apm_m96j04_extend f t / eigenvalue) t := by
  let F : ℝ → ℝ := fun u ↦ ∫ s in (0 : ℝ)..u, apm_m96j04_extend f s
  have heq : (fun u ↦ eigenvalue * apm_m96j04_extend f u) =ᶠ[nhds t] F := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with u hu
    let tu : Set.Icc (0 : ℝ) 1 := ⟨u, hu⟩
    have h := congrArg (fun g : apm_m96j04_C ↦ g tu) hf
    change V f tu = eigenvalue * f tu at h
    rw [hV] at h
    simpa [F, apm_m96j04_extend, hu, tu] using h.symm
  have hscaled : HasDerivAt (fun u ↦ eigenvalue * apm_m96j04_extend f u)
      (apm_m96j04_extend f t) t :=
    (apm_m96j04_integral_hasDerivAt f ht).congr_of_eventuallyEq heq
  have hinv := hscaled.const_mul eigenvalue⁻¹
  convert hinv using 1 <;> field_simp

/-- The unbundled Volterra primitive as a continuous function on the pinned
interval.  This is the codomain-valued map underlying the required operator. -/
noncomputable def apm_m96j04_primitive (f : apm_m96j04_C) : apm_m96j04_C :=
  ⟨fun t ↦ ∫ s in (0 : ℝ)..(t : ℝ), apm_m96j04_extend f s, by
    have hint : MeasureTheory.IntegrableOn (apm_m96j04_extend f)
        (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        (apm_m96j04_extend_continuousOn f).integrableOn_compact isCompact_Icc
    have h := intervalIntegral.continuousOn_primitive_interval
      hint
    exact h.comp_continuous continuous_subtype_val (fun t ↦ by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using t.property)⟩

lemma apm_m96j04_primitive_apply (f : apm_m96j04_C)
    (t : Set.Icc (0 : ℝ) 1) :
    apm_m96j04_primitive f t =
      ∫ s in (0 : ℝ)..(t : ℝ), apm_m96j04_extend f s := rfl

/-- Concrete non-vacuity check for the newly bundled primitive. -/
lemma apm_m96j04_primitive_one_at_one :
    apm_m96j04_primitive (1 : apm_m96j04_C) ⟨1, by norm_num⟩ = 1 := by
  rw [apm_m96j04_primitive_apply]
  apply Eq.trans (intervalIntegral.integral_congr (f := apm_m96j04_extend 1)
    (g := fun _ : ℝ ↦ 1) ?_)
  · simp
  · intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    simp [apm_m96j04_extend, hx']

lemma apm_m96j04_extend_add (f g : apm_m96j04_C) :
    apm_m96j04_extend (f + g) =
      fun x ↦ apm_m96j04_extend f x + apm_m96j04_extend g x := by
  funext x
  simp only [apm_m96j04_extend]
  split <;> simp_all

lemma apm_m96j04_extend_smul (c : ℝ) (f : apm_m96j04_C) :
    apm_m96j04_extend (c • f) = fun x ↦ c * apm_m96j04_extend f x := by
  funext x
  simp only [apm_m96j04_extend]
  split <;> simp_all

lemma apm_m96j04_primitive_add (f g : apm_m96j04_C) :
    apm_m96j04_primitive (f + g) =
      apm_m96j04_primitive f + apm_m96j04_primitive g := by
  ext t
  rw [apm_m96j04_primitive_apply, apm_m96j04_extend_add,
    intervalIntegral.integral_add
      (apm_m96j04_extend_intervalIntegrable f t.property)
      (apm_m96j04_extend_intervalIntegrable g t.property)]
  rfl

lemma apm_m96j04_primitive_smul (c : ℝ) (f : apm_m96j04_C) :
    apm_m96j04_primitive (c • f) = c • apm_m96j04_primitive f := by
  ext t
  rw [apm_m96j04_primitive_apply, apm_m96j04_extend_smul,
    intervalIntegral.integral_const_mul]
  rfl

lemma apm_m96j04_primitive_norm_le (f : apm_m96j04_C) :
    ‖apm_m96j04_primitive f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le (f := apm_m96j04_primitive f) (norm_nonneg f)).2
  intro t
  calc
    ‖apm_m96j04_primitive f t‖ ≤ ‖f‖ * |(t : ℝ) - 0| := by
      rw [apm_m96j04_primitive_apply]
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Set.uIoc_of_le t.property.1] at hx
      have hx' : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.trans t.property.2⟩
      simpa [apm_m96j04_extend, hx'] using
        ContinuousMap.norm_coe_le_norm f ⟨x, hx'⟩
    _ ≤ ‖f‖ := by
      rw [sub_zero, abs_of_nonneg t.property.1]
      exact mul_le_of_le_one_right (norm_nonneg f) t.property.2

noncomputable def apm_m96j04_volterra :
    apm_m96j04_C →L[ℝ] apm_m96j04_C :=
  LinearMap.mkContinuous
    { toFun := apm_m96j04_primitive
      map_add' := apm_m96j04_primitive_add
      map_smul' := apm_m96j04_primitive_smul }
    1 (fun f ↦ by simpa using apm_m96j04_primitive_norm_le f)

lemma apm_m96j04_volterra_apply (f : apm_m96j04_C)
    (t : Set.Icc (0 : ℝ) 1) :
    apm_m96j04_volterra f t =
      ∫ s in (0 : ℝ)..(t : ℝ), apm_m96j04_extend f s := rfl

lemma apm_m96j04_integral_hasDerivWithinAt_zero (f : apm_m96j04_C) :
    HasDerivWithinAt
      (fun u ↦ ∫ s in (0 : ℝ)..u, apm_m96j04_extend f s)
      (apm_m96j04_extend f 0) (Set.Ici 0) 0 := by
  have hcont : ContinuousWithinAt (apm_m96j04_extend f) (Set.Icc 0 1) 0 :=
    apm_m96j04_extend_continuousOn f 0 (by norm_num)
  have hmem : Set.Icc (0 : ℝ) 1 ∈ nhdsWithin 0 (Set.Ioi 0) :=
    Icc_mem_nhdsGT (by norm_num)
  have hcont' : ContinuousWithinAt (apm_m96j04_extend f) (Set.Ioi 0) 0 :=
    hcont.mono_of_mem_nhdsWithin hmem
  have hmeas : StronglyMeasurableAtFilter (apm_m96j04_extend f)
      (nhdsWithin 0 (Set.Ioi 0)) MeasureTheory.volume :=
    AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
      ((apm_m96j04_extend_continuousOn f).aestronglyMeasurable measurableSet_Icc) hmem
  exact intervalIntegral.integral_hasDerivWithinAt_right
    (apm_m96j04_extend_intervalIntegrable f (by norm_num)) hmeas hcont'

lemma apm_m96j04_eigenvector_hasDerivWithinAt_zero
    (V : apm_m96j04_C →L[ℝ] apm_m96j04_C)
    (hV : ∀ (f : apm_m96j04_C) (t : Set.Icc (0 : ℝ) 1),
      V f t = ∫ s in (0 : ℝ)..(t : ℝ), apm_m96j04_extend f s)
    (eigenvalue : ℝ) (heigen : eigenvalue ≠ 0) (f : apm_m96j04_C)
    (hf : V f = eigenvalue • f) :
    HasDerivWithinAt (apm_m96j04_extend f)
      (apm_m96j04_extend f 0 / eigenvalue) (Set.Ici 0) 0 := by
  let F : ℝ → ℝ := fun u ↦ ∫ s in (0 : ℝ)..u, apm_m96j04_extend f s
  have heq : (fun u ↦ eigenvalue * apm_m96j04_extend f u) =ᶠ[
      nhdsWithin 0 (Set.Ici 0)] F := by
    filter_upwards [Icc_mem_nhdsGE (by norm_num : (0 : ℝ) < 1)] with u hu
    let tu : Set.Icc (0 : ℝ) 1 := ⟨u, hu⟩
    have h := congrArg (fun g : apm_m96j04_C ↦ g tu) hf
    change V f tu = eigenvalue * f tu at h
    rw [hV] at h
    simpa [F, apm_m96j04_extend, hu, tu] using h.symm
  have hscaled : HasDerivWithinAt
      (fun u ↦ eigenvalue * apm_m96j04_extend f u)
      (apm_m96j04_extend f 0) (Set.Ici 0) 0 :=
    (apm_m96j04_integral_hasDerivWithinAt_zero f).congr_of_eventuallyEq heq (by
      have hz := apm_m96j04_eigenvector_zero_at_zero V hV eigenvalue heigen f hf
      have hext : apm_m96j04_extend f 0 = 0 := by
        simpa [apm_m96j04_extend] using hz
      simp [hext])
  have hinv := hscaled.const_mul eigenvalue⁻¹
  convert hinv using 1 <;> field_simp

lemma apm_m96j04_eigenvector_eq_zero
    (V : apm_m96j04_C →L[ℝ] apm_m96j04_C)
    (hV : ∀ (f : apm_m96j04_C) (t : Set.Icc (0 : ℝ) 1),
      V f t = ∫ s in (0 : ℝ)..(t : ℝ), apm_m96j04_extend f s)
    (eigenvalue : ℝ) (heigen : eigenvalue ≠ 0) (f : apm_m96j04_C)
    (hf : V f = eigenvalue • f) : f = 0 := by
  let K : NNReal := ⟨|eigenvalue⁻¹|, abs_nonneg _⟩
  let v : ℝ → ℝ → ℝ := fun _ z ↦ z / eigenvalue
  have hv : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      LipschitzOnWith K (v t) Set.univ := by
    intro t ht
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |x / eigenvalue - y / eigenvalue| ≤ |eigenvalue⁻¹| * |x - y|
    rw [div_eq_mul_inv, div_eq_mul_inv, ← sub_mul, abs_mul]
    rw [mul_comm]
  have hf' : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      HasDerivWithinAt (apm_m96j04_extend f)
        (v t (apm_m96j04_extend f t)) (Set.Ici t) t := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      simpa [v] using
        apm_m96j04_eigenvector_hasDerivWithinAt_zero V hV eigenvalue heigen f hf
    · exact (apm_m96j04_eigenvector_hasDerivAt V hV eigenvalue heigen f hf
        ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩).hasDerivWithinAt
  have hzero' : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      HasDerivWithinAt (fun _ : ℝ ↦ (0 : ℝ))
        (v t 0) (Set.Ici t) t := by
    intro t ht
    simpa [v] using (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt
  have heq : Set.EqOn (apm_m96j04_extend f) (fun _ : ℝ ↦ 0)
      (Set.Icc 0 1) := ODE_solution_unique_of_mem_Icc_right
    (s := fun _ : ℝ ↦ Set.univ) hv
    (apm_m96j04_extend_continuousOn f) hf' (fun _ _ ↦ Set.mem_univ _)
    continuousOn_const hzero' (fun _ _ ↦ Set.mem_univ _)
    (by
      have hz := apm_m96j04_eigenvector_zero_at_zero V hV eigenvalue heigen f hf
      simpa [apm_m96j04_extend] using hz)
  ext t
  have := heq t.property
  simpa [apm_m96j04_extend, t.property] using this

/-- Every Volterra primitive is Lipschitz, with its input sup norm as
constant. This is the quantitative equicontinuity estimate used by Ascoli. -/
lemma apm_m96j04_primitive_dist_le (f : apm_m96j04_C)
    (x y : Set.Icc (0 : ℝ) 1) :
    dist (apm_m96j04_primitive f x) (apm_m96j04_primitive f y) ≤
      ‖f‖ * dist x y := by
  have h0x := apm_m96j04_extend_intervalIntegrable f x.property
  have hxy : IntervalIntegrable (apm_m96j04_extend f) MeasureTheory.volume
      (x : ℝ) (y : ℝ) :=
    ((apm_m96j04_extend_continuousOn f).mono (by
      intro z hz
      rcases Set.mem_uIcc.mp hz with hz | hz
      · exact ⟨le_trans x.property.1 hz.1, hz.2.trans y.property.2⟩
      · exact ⟨le_trans y.property.1 hz.1, hz.2.trans x.property.2⟩)).intervalIntegrable
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0x hxy
  rw [← apm_m96j04_primitive_apply f x,
    ← apm_m96j04_primitive_apply f y] at hadd
  have hdiff : apm_m96j04_primitive f x - apm_m96j04_primitive f y =
      -(∫ s in (x : ℝ)..(y : ℝ), apm_m96j04_extend f s) := by
    rw [← hadd]
    ring
  rw [Real.dist_eq, hdiff, abs_neg]
  calc
    |∫ s in (x : ℝ)..(y : ℝ), apm_m96j04_extend f s| ≤
        ‖f‖ * |(y : ℝ) - (x : ℝ)| := by
      change ‖∫ s in (x : ℝ)..(y : ℝ), apm_m96j04_extend f s‖ ≤ _
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro z hz
      have hz' : z ∈ Set.Icc (0 : ℝ) 1 := by
        rcases Set.mem_uIoc.mp hz with hz | hz
        · exact ⟨le_trans x.property.1 hz.1.le, hz.2.trans y.property.2⟩
        · exact ⟨le_trans y.property.1 hz.1.le, hz.2.trans x.property.2⟩
      simpa [apm_m96j04_extend, hz'] using
        ContinuousMap.norm_coe_le_norm f ⟨z, hz'⟩
    _ = ‖f‖ * dist x y := by
      congr 1
      change |(y : ℝ) - (x : ℝ)| = |(x : ℝ) - (y : ℝ)|
      exact abs_sub_comm _ _

/-- The remaining Arzelà--Ascoli assembly for the explicitly bundled
Volterra operator. -/
lemma apm_m96j04_volterra_compact :
    IsCompactOperator apm_m96j04_volterra := by
  change IsCompactOperator (apm_m96j04_volterra :
    apm_m96j04_C →ₗ[ℝ] apm_m96j04_C)
  rw [isCompactOperator_iff_isCompact_closure_image_closedBall
    (apm_m96j04_volterra : apm_m96j04_C →ₗ[ℝ] apm_m96j04_C) zero_lt_one]
  let s : Set apm_m96j04_C :=
    apm_m96j04_volterra '' Metric.closedBall (0 : apm_m96j04_C) 1
  let 𝔖 : Set (Set (Set.Icc (0 : ℝ) 1)) := {K | IsCompact K}
  letI : T2Space (UniformOnFun (Set.Icc (0 : ℝ) 1) ℝ 𝔖) :=
    UniformOnFun.t2Space_of_covering (by
      apply Set.eq_univ_iff_forall.mpr
      intro x
      exact Set.mem_sUnion_of_mem (Set.mem_singleton x) isCompact_singleton)
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (𝔖 := 𝔖) (F := ((↑) : apm_m96j04_C → Set.Icc (0 : ℝ) 1 → ℝ))
  · intro K hK
    exact hK
  · exact ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
  · intro K hK
    apply UniformEquicontinuousOn.equicontinuousOn
    apply LipschitzOnWith.uniformEquicontinuousOn _ 1
    intro g
    rcases g.property with ⟨f, hf, hfg⟩
    change LipschitzOnWith 1 (fun x => (g : apm_m96j04_C) x) K
    rw [← hfg]
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist (apm_m96j04_volterra f x) (apm_m96j04_volterra f y) ≤
          ‖f‖ * dist x y := apm_m96j04_primitive_dist_le f x y
      _ ≤ 1 * dist x y := by
        gcongr
        simpa [dist_zero_right] using hf
  · intro K hK x hx
    refine ⟨Set.Icc (-1 : ℝ) 1, isCompact_Icc, ?_⟩
    intro g hg
    rcases hg with ⟨f, hf, rfl⟩
    have hfnorm : ‖f‖ ≤ 1 := by simpa [dist_zero_right] using hf
    have hpoint : ‖apm_m96j04_volterra f x‖ ≤ 1 :=
      (ContinuousMap.norm_coe_le_norm (apm_m96j04_volterra f) x).trans
        ((apm_m96j04_primitive_norm_le f).trans hfnorm)
    simpa [Real.norm_eq_abs, abs_le] using hpoint

theorem apm_m96j04 :
    (∃ A : apm_m96j04_H →L[ℝ] apm_m96j04_H,
      (∀ x y : ℓ²(ℕ, ℝ), A (x, y) = (y, 0)) ∧
      ¬IsCompactOperator A ∧
      ∀ n : ℕ, 2 ≤ n → IsCompactOperator (A ^ n)) ∧
    ∃ V : apm_m96j04_C →L[ℝ] apm_m96j04_C,
      (∀ (f : apm_m96j04_C) (t : Set.Icc (0 : ℝ) 1),
        V f t = ∫ s in (0 : ℝ)..(t : ℝ), apm_m96j04_extend f s) ∧
      IsCompactOperator V ∧
      ∀ eigenvalue : ℝ, eigenvalue ≠ 0 →
        ∀ f : apm_m96j04_C, V f = eigenvalue • f → f = 0 := by
  constructor
  · obtain ⟨A, hA, hpow⟩ := apm_m96j04_block_exists
    refine ⟨A, hA, ?_, hpow⟩
    intro hcompact
    have hid : IsCompactOperator (id : ℓ²(ℕ, ℝ) → ℓ²(ℕ, ℝ)) := by
      have hcomp := (hcompact.comp_clm
        (ContinuousLinearMap.inr ℝ ℓ²(ℕ, ℝ) ℓ²(ℕ, ℝ))).clm_comp
          (ContinuousLinearMap.fst ℝ ℓ²(ℕ, ℝ) ℓ²(ℕ, ℝ))
      convert hcomp using 1
      funext x
      simp [hA]
    -- (Sibling: m95A02)
    let b : HilbertBasis ℕ ℝ ℓ²(ℕ, ℝ) :=
      HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ ℓ²(ℕ, ℝ))
    letI : FiniteDimensional ℝ ℓ²(ℕ, ℝ) :=
      FiniteDimensional.of_isCompactOperator_id hid
    letI : Finite ℕ := b.orthonormal.linearIndependent.finite
    exact not_finite ℕ
  · exact ⟨apm_m96j04_volterra, apm_m96j04_volterra_apply,
      apm_m96j04_volterra_compact, fun eigenvalue heigen f hf ↦
        apm_m96j04_eigenvector_eq_zero apm_m96j04_volterra
          apm_m96j04_volterra_apply eigenvalue heigen f hf⟩
    /-
    PARTIAL boundary (Volterra operator).  The Hilbert-space clause is now
    closed, including noncompactness, by factoring a hypothetical compact block
    map into the identity and contradicting finiteness of the canonical
    `HilbertBasis ℕ ℝ ℓ²`.

    The remaining clause requires bundling the parameter-dependent interval
    integral as a continuous linear map into `C(Icc 0 1,ℝ)`.  Compactness then
    needs converting the uniformly bounded Lipschitz image of the unit ball
    into the pointwise-compact hypothesis of
    `ArzelaAscoli.isCompact_of_equicontinuous`.  The eigenvalue clause requires
    an interval FTC/ODE uniqueness bridge.  Searches of `LEMMA-INDEX.md`, 172
    closed artifacts, `ConstructionTargets/`, `YoungL2.lean`, Mathlib's
    continuous-map integral APIs, Ascoli implementation, and interval FTC found
    no packaged Volterra continuous-linear-map construction or compactness
    theorem.  This assembly remains open.

    Closer hop 1 isolates and proves the initial-value part of the eigenvector
    argument as `apm_m96j04_eigenvector_zero_at_zero`: evaluating the frozen
    Volterra formula at `t = 0` forces every eigenvector for a nonzero
    eigenvalue to vanish at zero.  Additional searches covered
    `intervalIntegral.integral_hasDerivAt_right`, Gronwall/ODE uniqueness,
    `ContinuousMap` operator constructors, Ascoli, and all closed artifacts.
    The remaining eigenvector bridge is to turn the integral equation into
    `HasDerivAt f (f/eigenvalue)` on the subtype interval and apply uniqueness;
    compactness still requires constructing the continuous linear map and the
    equicontinuous compact image.

    Closer hop 2 now compiles all FTC prerequisites.  The zero extension is
    continuous on the closed integration interval as
    `apm_m96j04_extend_continuousOn`, is interval-integrable on every
    `[0,t]` by `apm_m96j04_extend_intervalIntegrable`, and
    `apm_m96j04_integral_hasDerivAt` proves that its Volterra primitive has
    derivative equal to the integrand at every `t ∈ (0,1)`.  These lemmas use
    `continuousOn_iff_continuous_restrict`, compact-interval integrability, and
    `intervalIntegral.integral_hasDerivAt_right`; they avoid incorrectly
    claiming that the zero extension is globally continuous at the endpoints.
    The eigenvalue clause is therefore narrowed to transporting the continuous-
    map equality through this derivative theorem and applying zero-initial-value
    uniqueness for `f' = f/eigenvalue`.  Construction and Ascoli compactness of
    the bundled Volterra operator remain the independent larger boundary.

    Closer hop 3 completes that transport as
    `apm_m96j04_eigenvector_hasDerivAt`: on every interior point, the frozen
    continuous-map eigenvector equality is evaluated pointwise, made into a
    neighborhood equality using `Icc_mem_nhds`, transferred through the FTC
    lemma by `HasDerivAt.congr_of_eventuallyEq`, and divided by the nonzero
    eigenvalue.  Inspection of `ODE_solution_unique_of_mem_Icc_right` shows the
    final uniqueness application additionally needs a one-sided derivative at
    the initial endpoint; the compiled derivative lemma deliberately states
    only the mathematically justified open-interval result.  The principal
    unresolved bridge is still construction and boundedness of the Volterra
    continuous linear map and its Arzela--Ascoli compactness proof.  Renewed
    searches of `LEMMA-INDEX.md`, solved siblings, `ConstructionTargets/`,
    `YoungL2.lean`, Mathlib's derivative-congruence, Gronwall, and Ascoli source
    found no packaged construction closing that bridge.

    HOP 4 checked the `L1.integralCLM` family, continuous-map constructors,
    `ArzelaAscoli.isCompact_of_equicontinuous`, and the one-sided ODE
    uniqueness API. The integral CLM acts on `L1`, not directly on the
    variable-upper-limit continuous-map codomain, and Ascoli still requires
    the explicit uniform sup-norm and equicontinuity estimates.

    The exact missing operator lemma is:

      `∃ V : apm_m96j04_C →L[ℝ] apm_m96j04_C,
        (∀ (f : apm_m96j04_C) (t : Set.Icc (0 : ℝ) 1),
          V f t = ∫ s in (0 : ℝ)..(t : ℝ), apm_m96j04_extend f s) ∧
        IsCompactOperator V`.

    Its proof must bundle the pointwise primitive, prove
    `‖V f‖ ≤ ‖f‖`, and show that the image of the unit ball is uniformly
    bounded and Lipschitz before applying Arzela--Ascoli.

    The independent endpoint-uniqueness lemma needed after construction is:

      `∀ (V : apm_m96j04_C →L[ℝ] apm_m96j04_C),
        (∀ (f : apm_m96j04_C) (t : Set.Icc (0 : ℝ) 1),
          V f t = ∫ s in (0 : ℝ)..(t : ℝ), apm_m96j04_extend f s) →
        ∀ eigenvalue : ℝ, eigenvalue ≠ 0 →
          ∀ f : apm_m96j04_C, V f = eigenvalue • f → f = 0`.

    The compiled zero-at-zero and interior derivative lemmas are exactly its
    hypotheses; closing it requires a one-sided derivative or an integral
    Gronwall argument valid from `0`. Neither statement is defective, but no
    searched declaration supplies either assembly. The frozen main statement
    remains unchanged.
    -/

#print axioms apm_m96j04
