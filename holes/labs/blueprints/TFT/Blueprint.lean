import Mathlib

/-!
# Translation of test functions

A shared blueprint for the analytic input needed by `m98J02` and `m98A04`.
The hard estimates are isolated from the fixed-support-stage and LF-topology
bookkeeping.
-/

open Set TopologicalSpace Filter
open scoped Distributions ContDiff BoundedContinuousFunction Topology

noncomputable section

#check TestFunction.continuous_ofSupportedIn
#check ContDiffMapSupportedIn.continuous_iff_comp
#check ContDiffMapSupportedIn.withSeminorms
#check ContDiffMapSupportedIn.seminorm_le_iff
#check BoundedContinuousFunction.ofNormedAddCommGroup
#check HasCompactSupport.comp_homeomorph
#check Homeomorph.addLeft

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev TFT (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :=
  TestFunction (⊤ : Opens E) F ⊤

/-- Translation with the sign convention used in `m98J02`.  Reflection turns
`φ (x - y)` into an instance of this convention. -/
def tftTranslate (x : E) (ψ : TFT E F) : TFT E F where
  toFun := fun y => ψ (x + y)
  contDiff' := ψ.contDiff.comp (contDiff_const.add contDiff_id)
  hasCompactSupport' := ψ.hasCompactSupport.comp_homeomorph (Homeomorph.addLeft x)
  tsupport_subset' := by simp

@[simp] lemma tftTranslate_apply (x y : E) (ψ : TFT E F) :
    tftTranslate x ψ y = ψ (x + y) := rfl

lemma tft_directional_contDiff (v : E) (ψ : TFT E F) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ (ψ : E → F) y v) := by
  exact (contDiff_infty_iff_fderiv.mp ψ.contDiff).2.clm_apply contDiff_const

lemma tft_directional_hasCompactSupport (v : E) (ψ : TFT E F) :
    HasCompactSupport (fun y => fderiv ℝ (ψ : E → F) y v) := by
  exact ψ.hasCompactSupport.fderiv_apply ℝ v

/-- The directional derivative, bundled again as a test function. -/
def tftDirectional (v : E) (ψ : TFT E F) : TFT E F where
  toFun := fun y => fderiv ℝ (ψ : E → F) y v
  contDiff' := tft_directional_contDiff v ψ
  hasCompactSupport' := tft_directional_hasCompactSupport v ψ
  tsupport_subset' := by simp

@[simp] lemma tftDirectional_apply (v : E) (ψ : TFT E F) (y : E) :
    tftDirectional v ψ y = fderiv ℝ (ψ : E → F) y v := rfl

/-- A compact set containing the supports of all translates with parameter in
the closed unit ball around `x₀`. -/
def tftTranslationCompact (ψ : TFT E F) (x₀ : E) : Compacts E :=
  ⟨(fun p : E × E => p.2 - p.1) ''
      (Metric.closedBall x₀ 1 ×ˢ tsupport (ψ : E → F)), by
    exact ((isCompact_closedBall x₀ 1).prod ψ.hasCompactSupport).image (by fun_prop)⟩

/-- S0: all nearby translates have one compact support. -/
lemma tft_local_fixed_support (ψ : TFT E F) (x₀ : E) :
    ∀ x ∈ Metric.closedBall x₀ 1,
      tsupport (tftTranslate x ψ : E → F) ⊆ tftTranslationCompact ψ x₀ := by
  intro x hx y hy
  change y ∈ (fun p : E × E => p.2 - p.1) ''
    (Metric.closedBall x₀ 1 ×ˢ tsupport (ψ : E → F))
  refine ⟨(x, x + y), ⟨hx, ?_⟩, ?_⟩
  · have hsupport := tsupport_comp_eq_preimage (ψ : E → F) (Homeomorph.addLeft x)
    have : y ∈ (Homeomorph.addLeft x : E ≃ₜ E) ⁻¹' tsupport (ψ : E → F) := by
      rw [← hsupport]
      simpa [Function.comp_def] using hy
    exact this
  · simp


lemma tft_local_fixed_function_support (ψ : TFT E F) (x₀ : E) :
    ∀ x ∈ Metric.closedBall x₀ 1,
      Function.support (fun y => ψ (x + y)) ⊆ tftTranslationCompact ψ x₀ := by
  intro x hx y hy
  change y ∈ (fun p : E × E ↦ p.2 - p.1) ''
    (Metric.closedBall x₀ 1 ×ˢ tsupport (ψ : E → F))
  refine ⟨(x, x + y), ⟨hx, ?_⟩, ?_⟩
  · exact subset_tsupport _ hy
  · simp

/-- The nearby translate regarded as an element of one fixed Fréchet stage;
outside the closed unit ball it is harmlessly set to zero. -/
def tftTranslateStageLocal (ψ : TFT E F) (x₀ x : E) :
    ContDiffMapSupportedIn E F ⊤ (tftTranslationCompact ψ x₀) := by
  classical
  exact if hx : x ∈ Metric.closedBall x₀ 1 then
    ContDiffMapSupportedIn.of_support_subset
      (ψ.contDiff.comp (contDiff_const.add contDiff_id))
      (tft_local_fixed_function_support ψ x₀ x hx)
  else 0

lemma tftTranslateStageLocal_apply (ψ : TFT E F) (x₀ x : E)
    (hx : x ∈ Metric.closedBall x₀ 1) (y : E) :
    tftTranslateStageLocal ψ x₀ x y = ψ (x + y) := by
  simp [tftTranslateStageLocal, hx]

lemma tft_directional_translate_function_support
    (ψ : TFT E F) (x₀ x v : E) (hx : x ∈ Metric.closedBall x₀ 1) :
    Function.support (fun y => fderiv ℝ (ψ : E → F) (x + y) v) ⊆
      tftTranslationCompact ψ x₀ := by
  intro y hy
  have hlin : fderiv ℝ (ψ : E → F) (x + y) ≠ 0 := by
    intro hzero
    apply hy
    dsimp
    rw [hzero]
    exact ContinuousLinearMap.zero_apply v
  have hz : x + y ∈ tsupport (ψ : E → F) :=
    support_fderiv_subset ℝ hlin
  change y ∈ (fun p : E × E => p.2 - p.1) ''
    (Metric.closedBall x₀ 1 ×ˢ tsupport (ψ : E → F))
  refine ⟨(x, x + y), ⟨hx, hz⟩, ?_⟩
  simp

/-- The translated directional derivative, bundled in the *same* stage as
`ψ`; differentiation does not enlarge support. -/
def tftDirectionalTranslateStage (ψ : TFT E F) (x₀ x v : E) :
    ContDiffMapSupportedIn E F ⊤ (tftTranslationCompact ψ x₀) := by
  classical
  exact if hx : x ∈ Metric.closedBall x₀ 1 then
    ContDiffMapSupportedIn.of_support_subset
      ((tft_directional_contDiff v ψ).comp (contDiff_const.add contDiff_id))
      (tft_directional_translate_function_support ψ x₀ x v hx)
  else 0

lemma tft_compactSupport_bounded (f : E → F) (hf : Continuous f)
    (hfc : HasCompactSupport f) : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  exact hfc.exists_bound_of_continuous hf

/-- A compactly supported continuous map, bundled as a bounded continuous
map.  This vector-valued wrapper avoids the ring-valued specialization of
Mathlib's constructor with the same purpose. -/
def tftBCFOfCompactSupport (f : E → F) (hf : Continuous f)
    (hfc : HasCompactSupport f) : E →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup f hf
    (tft_compactSupport_bounded f hf hfc).choose
    (tft_compactSupport_bounded f hf hfc).choose_spec

/-- U1: compactly supported continuous functions vary continuously in sup norm
under translation.  This is the uniform-continuity estimate. -/
lemma tft_translate_bcf_continuous
    (f : E → F) (hf : Continuous f) (hfc : HasCompactSupport f) :
    Continuous (fun x : E =>
      tftBCFOfCompactSupport (fun y => f (x + y))
        (hf.comp (continuous_const.add continuous_id))
        (hfc.comp_homeomorph (Homeomorph.addLeft x))) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  have huc : UniformContinuous f := hfc.uniformContinuous_of_continuous hf
  obtain ⟨δ, hδ, hmod⟩ :=
    (Metric.uniformContinuous_iff.mp huc) (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun z hz => ?_⟩
  apply lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (le_of_lt (half_pos hε))).2 ?_)
    (half_lt_self hε)
  intro y
  change dist (f (z + y)) (f (x + y)) ≤ ε / 2
  exact le_of_lt (hmod (by simpa only [dist_add_right] using hz))

lemma tft_difference_quotient_continuous
    (f : E → F) (hf : ContDiff ℝ 1 f) (x v : E) (h : ℝ) :
    Continuous (fun y => h⁻¹ • (f (x + h • v + y) - f (x + y))) := by
  fun_prop

lemma tft_difference_quotient_hasCompactSupport
    (f : E → F) (hfc : HasCompactSupport f) (x v : E) (h : ℝ) :
    HasCompactSupport (fun y => h⁻¹ • (f (x + h • v + y) - f (x + y))) := by
  have h₁ := hfc.comp_homeomorph (Homeomorph.addLeft (x + h • v))
  have h₂ := hfc.comp_homeomorph (Homeomorph.addLeft x)
  have hs := h₁.sub h₂
  have hm := hs.comp_left (g := fun z : F => h⁻¹ • z) (smul_zero _)
  simpa [Function.comp_def] using hm

lemma tft_fderiv_translate_continuous
    (f : E → F) (hf : ContDiff ℝ 1 f) (x v : E) :
    Continuous (fun y => fderiv ℝ f (x + y) v) := by
  exact ((hf.continuous_fderiv (by norm_num)).comp
    (continuous_const.add continuous_id)).clm_apply continuous_const

lemma tft_fderiv_translate_hasCompactSupport
    (f : E → F) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (x v : E) :
    HasCompactSupport (fun y => fderiv ℝ f (x + y) v) := by
  simpa [Function.comp_def] using
    (hfc.fderiv_apply ℝ v).comp_homeomorph (Homeomorph.addLeft x)

/-- U2 step: mean-value bound for one difference quotient, given a modulus for `fderiv`. -/
lemma tft_translate_bcf_difference_quotient_aux_mvt
    (f : E → F) (hf : ContDiff ℝ 1 f) (z v : E) (h ε : ℝ) (hh : h ≠ 0)
    (hε : ∀ w, dist w z ≤ |h| * ‖v‖ → ‖fderiv ℝ f w - fderiv ℝ f z‖ ≤ ε) :
    ‖h⁻¹ • (f (z + h • v) - f z) - fderiv ℝ f z v‖ ≤ ε * ‖v‖ := by
  let D : E →L[ℝ] F := fderiv ℝ f z
  let g : E → F := fun w => f w - D w
  have hf' : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hg' : ∀ w, DifferentiableAt ℝ g w := by
    intro w
    exact (hf' w).sub D.differentiableAt
  have hD : ∀ w, fderiv ℝ g w = fderiv ℝ f w - D := by
    intro w
    exact ((hf' w).hasFDerivAt.sub D.hasFDerivAt).fderiv
  have hε0 : 0 ≤ ε := by
    have hz := hε z (by simp; positivity)
    simpa using (norm_nonneg (fderiv ℝ f z - fderiv ℝ f z)).trans hz
  let s : Set E := Metric.closedBall z (|h| * ‖v‖)
  have hend : z + h • v ∈ s := by
    change dist (z + h • v) z ≤ |h| * ‖v‖
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  have hstart : z ∈ s := by
    change dist z z ≤ |h| * ‖v‖
    simp
    positivity
  have hbound : ∀ w ∈ s, ‖fderiv ℝ g w‖ ≤ ε := by
    intro w hw
    rw [hD]
    exact hε w hw
  have hmvt : ‖g (z + h • v) - g z‖ ≤ ε * ‖(z + h • v) - z‖ :=
    (convex_closedBall z (|h| * ‖v‖)).norm_image_sub_le_of_norm_fderiv_le
      (fun w _ => hg' w) hbound hstart hend
  have hrewrite :
      h⁻¹ • (f (z + h • v) - f z) - fderiv ℝ f z v =
        h⁻¹ • (g (z + h • v) - g z) := by
    dsimp [g, D]
    rw [map_add, map_smul]
    simp only [smul_sub, smul_add, smul_smul]
    have hinv : h⁻¹ * h = 1 := inv_mul_cancel₀ hh
    rw [hinv, one_smul]
    module
  rw [hrewrite, norm_smul, Real.norm_eq_abs]
  calc
    |h⁻¹| * ‖g (z + h • v) - g z‖ ≤
        |h⁻¹| * (ε * ‖(z + h • v) - z‖) :=
      mul_le_mul_of_nonneg_left hmvt (abs_nonneg _)
    _ = ε * ‖v‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_inv]
      field_simp [abs_ne_zero.mpr hh]

lemma tft_translate_bcf_difference_quotient_aux_uniform
    (f : E → F) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (x v : E) :
    Tendsto (fun h : ℝ =>
        ‖tftBCFOfCompactSupport
            (fun y => h⁻¹ • (f (x + h • v + y) - f (x + y)))
            (tft_difference_quotient_continuous f hf x v h)
            (tft_difference_quotient_hasCompactSupport f hfc x v h) -
          tftBCFOfCompactSupport
            (fun y => fderiv ℝ f (x + y) v)
            (tft_fderiv_translate_continuous f hf x v)
            (tft_fderiv_translate_hasCompactSupport f hf hfc x v)‖)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have huc : UniformContinuous (fderiv ℝ f) :=
    (hfc.fderiv ℝ).uniformContinuous_of_continuous (hf.continuous_fderiv (by norm_num))
  have hv : (0 : ℝ) < ‖v‖ + 1 := by positivity
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.1 huc (ε / 2 / (‖v‖ + 1)) (by positivity)
  refine ⟨δ / (‖v‖ + 1), by positivity, fun h hh0 hh => ?_⟩
  have hh0' : h ≠ 0 := hh0
  have hhδ : |h| * ‖v‖ < δ := by
    rw [dist_zero_right, Real.norm_eq_abs, lt_div_iff₀ hv] at hh
    nlinarith [abs_nonneg h]
  rw [dist_zero_right, norm_norm]
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun y => ?_
  rw [BoundedContinuousFunction.sub_apply]
  simp only [tftBCFOfCompactSupport, BoundedContinuousFunction.coe_ofNormedAddCommGroup]
  have key := tft_translate_bcf_difference_quotient_aux_mvt f hf (x + y) v h
    (ε / 2 / (‖v‖ + 1)) hh0' (fun w hw => by
      have := hmod (lt_of_le_of_lt hw hhδ)
      rw [dist_eq_norm] at this
      exact this.le)
  rw [show x + h • v + y = x + y + h • v by abel]
  refine key.trans ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ hv]
  nlinarith [norm_nonneg v]

/-- U2 (assembled). -/
lemma tft_translate_bcf_difference_quotient
    (f : E → F) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (x v : E) :
    Tendsto (fun h : ℝ =>
        tftBCFOfCompactSupport
          (fun y => h⁻¹ • (f (x + h • v + y) - f (x + y)))
          (tft_difference_quotient_continuous f hf x v h)
          (tft_difference_quotient_hasCompactSupport f hfc x v h))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (tftBCFOfCompactSupport
        (fun y => fderiv ℝ f (x + y) v)
        (tft_fderiv_translate_continuous f hf x v)
        (tft_fderiv_translate_hasCompactSupport f hf hfc x v))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact tft_translate_bcf_difference_quotient_aux_uniform f hf hfc x v

/-- S1: continuity into the fixed stage.  The hypothesis is precisely U1 for
every iterated derivative (the maps occurring in `continuous_iff_comp`). -/
lemma tft_stage_continuousAt_of_structure_maps
    (ψ : TFT E F) (x₀ : E)
    (hU1 : ∀ i : ℕ, ContinuousAt
      (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i ∘
        tftTranslateStageLocal ψ x₀) x₀) :
    ContinuousAt (tftTranslateStageLocal ψ x₀) x₀ := by
  let T := ContinuousLinearMap.pi
    (ContDiffMapSupportedIn.structureMapCLM ℝ (⊤ : ℕ∞) :
      ∀ i : ℕ, ContDiffMapSupportedIn E F ⊤ (tftTranslationCompact ψ x₀) →L[ℝ]
        E →ᵇ (E [×i]→L[ℝ] F))
  apply (ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM ℝ).toIsUniformInducing.isInducing.continuousAt_iff.mpr
  rw [continuousAt_pi]
  intro i
  simpa [T, Function.comp_def] using hU1 i

/-- S1 with U1 discharged for every iterated derivative of `ψ`. -/
lemma tft_stage_continuousAt (ψ : TFT E F) (x₀ : E) :
    ContinuousAt (tftTranslateStageLocal ψ x₀) x₀ := by
  apply tft_stage_continuousAt_of_structure_maps ψ x₀
  intro i
  let f : E → (E [×i]→L[ℝ] F) := iteratedFDeriv ℝ i (ψ : E → F)
  have hf : Continuous f :=
    ψ.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hfc : HasCompactSupport f := ψ.hasCompactSupport.iteratedFDeriv i
  have hc : ContinuousAt (fun x : E =>
      tftBCFOfCompactSupport (fun y => f (x + y))
        (hf.comp (continuous_const.add continuous_id))
        (hfc.comp_homeomorph (Homeomorph.addLeft x))) x₀ :=
    (tft_translate_bcf_continuous f hf hfc).continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [Metric.closedBall_mem_nhds x₀ (by norm_num : (0 : ℝ) < 1)] with x hx
  apply BoundedContinuousFunction.ext
  intro y
  have heq : (tftTranslateStageLocal ψ x₀ x : E → F) =
      fun z ↦ ψ (x + z) := by
    funext z
    exact tftTranslateStageLocal_apply ψ x₀ x hx z
  rw [Function.comp_apply, ContDiffMapSupportedIn.structureMapCLM_top_apply]
  change iteratedFDeriv ℝ i (tftTranslateStageLocal ψ x₀ x : E → F) y = _
  rw [heq, iteratedFDeriv_comp_add_left]
  rfl

/-- S2: convergence in a fixed stage, reduced to convergence under every
structure map. -/
lemma tft_stage_difference_quotient_of_structure_maps
    (ψ : TFT E F) (x₀ v : E)
    (hU2 : ∀ i : ℕ, Tendsto (fun h : ℝ =>
        ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i
          (h⁻¹ • (tftTranslateStageLocal ψ x₀ (x₀ + h • v) -
            tftTranslateStageLocal ψ x₀ x₀)))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i
        (tftDirectionalTranslateStage ψ x₀ x₀ v)))) :
    Tendsto (fun h : ℝ => h⁻¹ •
        (tftTranslateStageLocal ψ x₀ (x₀ + h • v) -
          tftTranslateStageLocal ψ x₀ x₀))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (tftDirectionalTranslateStage ψ x₀ x₀ v)) := by
  rw [show nhds (tftDirectionalTranslateStage ψ x₀ x₀ v) =
      ⨅ i : ℕ, Filter.comap
        (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i)
        (nhds (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i
          (tftDirectionalTranslateStage ψ x₀ x₀ v))) by
    change @nhds _ (⨅ i : ℕ, TopologicalSpace.induced
      (ContDiffMapSupportedIn.structureMapLM ℝ ⊤ i) inferInstance) _ = _
    rw [nhds_iInf]
    congr 1
    funext i
    rw [nhds_induced]
    rfl]
  rw [Filter.tendsto_iInf]
  intro i
  rw [Filter.tendsto_comap_iff]
  exact hU2 i

/-- S2 with U2 discharged for every iterated derivative of `ψ`. -/
lemma tft_stage_difference_quotient_aux_eventually (x₀ v : E) :
    ∀ᶠ h : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      x₀ + h • v ∈ Metric.closedBall x₀ 1 := by
  have hc0 : ContinuousAt (fun h : ℝ => x₀ + h • v) 0 := by fun_prop
  have hc : Tendsto (fun h : ℝ => x₀ + h • v)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds x₀) := by
    simpa using hc0.mono_left inf_le_left
  exact hc.eventually (Metric.closedBall_mem_nhds x₀ zero_lt_one)

lemma tft_stage_difference_quotient_aux_contDiff (ψ : TFT E F) (i : ℕ) :
    ContDiff ℝ 1 (iteratedFDeriv ℝ i (ψ : E → F)) := by
  exact ψ.contDiff.iteratedFDeriv_right
    (by exact_mod_cast (show 1 + i ≤ (⊤ : ℕ∞) from le_top))

/-- A directional derivative commutes with the `i`-th derivative of a smooth map
(symmetry of higher derivatives; Mathlib has it only for analytic maps). -/
lemma tft_stage_difference_quotient_aux_directional_comm_aux_smooth
    (g : E → F) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedFDeriv ℝ i g) := by
  exact hg.iteratedFDeriv_right
    (by exact_mod_cast (show (⊤ : ℕ∞) + i ≤ (⊤ : ℕ∞) from by simp))

lemma tft_stage_difference_quotient_aux_directional_comm
    (g : E → F) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : ℕ) (v y : E) :
    iteratedFDeriv ℝ i (fun z => fderiv ℝ g z v) y =
      fderiv ℝ (iteratedFDeriv ℝ i g) y v := by
  revert y
  rw [← funext_iff]
  induction i with
  | zero =>
    funext y
    rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp]
    rw [(continuousMultilinearCurryFin0 ℝ E F).symm.comp_fderiv]
    rfl
  | succ i ih =>
    funext y
    have hGs := tft_stage_difference_quotient_aux_directional_comm_aux_smooth g hg i
    have hdG : Differentiable ℝ (fderiv ℝ (iteratedFDeriv ℝ i g)) :=
      (contDiff_infty_iff_fderiv.1 hGs).2.differentiable (by simp)
    have hL : iteratedFDeriv ℝ (i + 1) (fun z => fderiv ℝ g z v) y =
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => E) F).symm
          (fderiv ℝ (iteratedFDeriv ℝ i (fun z => fderiv ℝ g z v)) y) := by
      rw [iteratedFDeriv_succ_eq_comp_left]; rfl
    have hRR : iteratedFDeriv ℝ (i + 1) g =
        ⇑(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => E) F).symm ∘
          fderiv ℝ (iteratedFDeriv ℝ i g) := iteratedFDeriv_succ_eq_comp_left
    rw [hL, hRR, ih]
    have hR := ContinuousLinearEquiv.comp_fderiv (𝕜 := ℝ)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => E) F).symm.toContinuousLinearEquiv
      (f := fderiv ℝ (iteratedFDeriv ℝ i g)) (x := y)
    erw [hR, ContinuousLinearMap.comp_apply]
    refine congrArg (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => E) F).symm ?_
    have hsymm := (hGs.contDiffAt (x := y)).isSymmSndFDerivAt
      (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
    ext w
    rw [fderiv_clm_apply (hdG y) (differentiableAt_const v)]
    rw [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply, hsymm w v]


lemma tft_stage_difference_quotient_aux_coe_local (ψ : TFT E F) (x₀ x : E)
    (hx : x ∈ Metric.closedBall x₀ 1) :
    ⇑(tftTranslateStageLocal ψ x₀ x) = fun y => ψ (x + y) :=
  funext (tftTranslateStageLocal_apply ψ x₀ x hx)

lemma tft_stage_difference_quotient_aux_coe_dir (ψ : TFT E F) (x₀ v : E) :
    ⇑(tftDirectionalTranslateStage ψ x₀ x₀ v) = fun y => fderiv ℝ (ψ : E → F) (x₀ + y) v := by
  funext y
  simp [tftDirectionalTranslateStage, Metric.mem_closedBall]

lemma tft_stage_difference_quotient (ψ : TFT E F) (x₀ v : E) :
    Tendsto (fun h : ℝ => h⁻¹ •
        (tftTranslateStageLocal ψ x₀ (x₀ + h • v) -
          tftTranslateStageLocal ψ x₀ x₀))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (tftDirectionalTranslateStage ψ x₀ x₀ v)) := by
  apply tft_stage_difference_quotient_of_structure_maps
  intro i
  have hdiff := tft_stage_difference_quotient_aux_contDiff ψ i
  have h := tft_translate_bcf_difference_quotient
    (iteratedFDeriv ℝ i (ψ : E → F)) hdiff
    (ψ.hasCompactSupport.iteratedFDeriv i) x₀ v
  have hev := tft_stage_difference_quotient_aux_eventually x₀ v
  have hx₀ : x₀ ∈ Metric.closedBall x₀ 1 := Metric.mem_closedBall_self zero_le_one
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (ψ : E → F) := ψ.contDiff
  rw [show ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i
      (tftDirectionalTranslateStage ψ x₀ x₀ v) =
      tftBCFOfCompactSupport
        (fun y => fderiv ℝ (iteratedFDeriv ℝ i (ψ : E → F)) (x₀ + y) v)
        (tft_fderiv_translate_continuous _ hdiff x₀ v)
        (tft_fderiv_translate_hasCompactSupport _ hdiff
          (ψ.hasCompactSupport.iteratedFDeriv i) x₀ v) by
    ext y : 1
    rw [ContDiffMapSupportedIn.structureMapCLM_top_apply, tft_stage_difference_quotient_aux_coe_dir]
    change iteratedFDeriv ℝ i (fun y => fderiv ℝ (ψ : E → F) (x₀ + y) v) y =
      fderiv ℝ (iteratedFDeriv ℝ i (ψ : E → F)) (x₀ + y) v
    rw [iteratedFDeriv_comp_add_left' i x₀ (f := fun z => fderiv ℝ (ψ : E → F) z v)]
    exact tft_stage_difference_quotient_aux_directional_comm _ hψ i v (x₀ + y)]
  refine h.congr' ?_
  filter_upwards [hev] with h hh
  ext y : 1
  rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
  change h⁻¹ • (iteratedFDeriv ℝ i (ψ : E → F) (x₀ + h • v + y) - iteratedFDeriv ℝ i (ψ : E → F) (x₀ + y)) = _
  rw [ContDiffMapSupportedIn.coe_smul, ContDiffMapSupportedIn.coe_sub,
    tft_stage_difference_quotient_aux_coe_local ψ x₀ _ hh,
    tft_stage_difference_quotient_aux_coe_local ψ x₀ _ hx₀]
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y => ψ (x₀ + h • v + y)) :=
    hψ.comp (contDiff_const.add contDiff_id)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun y => ψ (x₀ + y)) :=
    hψ.comp (contDiff_const.add contDiff_id)
  have hi : ((i : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  set f1 : E → F := fun y => ψ (x₀ + h • v + y) with hf1
  set f2 : E → F := fun y => ψ (x₀ + y) with hf2
  have hs : ContDiff ℝ (⊤ : ℕ∞) (f1 - f2) := h1.sub h2
  rw [iteratedFDeriv_const_smul_apply (hs.of_le hi).contDiffAt,
    iteratedFDeriv_sub_apply (h1.of_le hi).contDiffAt (h2.of_le hi).contDiffAt, hf1, hf2,
    iteratedFDeriv_comp_add_left' i (x₀ + h • v) (f := (ψ : E → F)),
    iteratedFDeriv_comp_add_left' i x₀ (f := (ψ : E → F))]

lemma tft_ofSupportedIn_stage_eq (ψ : TFT E F) (x₀ x : E)
    (hx : x ∈ Metric.closedBall x₀ 1) :
    TestFunction.ofSupportedIn (by simp :
        (tftTranslationCompact ψ x₀ : Set E) ⊆ (⊤ : Opens E))
        (tftTranslateStageLocal ψ x₀ x) = tftTranslate x ψ := by
  apply TestFunction.toTestFunctionClass.coe_injective'
  funext y
  exact tftTranslateStageLocal_apply ψ x₀ x hx y

/-- Applying the continuous stage inclusion to S2 and replacing the local
representatives by their concrete translates. -/
lemma tft_stage_difference_quotient_to_lf (ψ : TFT E F) (x v : E) :
    Tendsto (fun h : ℝ => h⁻¹ •
        (tftTranslate (x + h • v) ψ - tftTranslate x ψ))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (tftTranslate x (tftDirectional v ψ))) := by
  sorry

/-- T1: translation is continuous in the LF test-function topology. -/
theorem tftTranslate_continuous (ψ : TFT E F) :
    Continuous (fun x : E => tftTranslate x ψ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  let hsub : (tftTranslationCompact ψ x₀ : Set E) ⊆ (⊤ : Opens E) := by simp
  let inc : ContDiffMapSupportedIn E F ⊤ (tftTranslationCompact ψ x₀) →
      TFT E F := TestFunction.ofSupportedIn hsub
  have hinc : Continuous inc := TestFunction.continuous_ofSupportedIn hsub
  have hc : ContinuousAt (fun x => inc (tftTranslateStageLocal ψ x₀ x)) x₀ := by
    simpa only [Function.comp_apply] using
      hinc.continuousAt.comp (tft_stage_continuousAt ψ x₀)
  apply hc.congr_of_eventuallyEq
  filter_upwards [Metric.closedBall_mem_nhds x₀ zero_lt_one] with x hx
  exact (tft_ofSupportedIn_stage_eq ψ x₀ x hx).symm

/-- T2: directional difference quotients converge in the LF topology. -/
theorem tftTranslate_difference_quotient (ψ : TFT E F) (x v : E) :
    Tendsto (fun h : ℝ => h⁻¹ •
        (tftTranslate (x + h • v) ψ - tftTranslate x ψ))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (tftTranslate x (tftDirectional v ψ))) := by
  exact tft_stage_difference_quotient_to_lf ψ x v
