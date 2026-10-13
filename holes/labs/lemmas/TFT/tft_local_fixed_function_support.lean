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
  sorry

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
  sorry


-- BEGIN SEAT AREA
lemma tft_local_fixed_function_support (ψ : TFT E F) (x₀ : E) :
    ∀ x ∈ Metric.closedBall x₀ 1,
      Function.support (fun y => ψ (x + y)) ⊆ tftTranslationCompact ψ x₀ := by
  intro x hx y hy
  change y ∈ (fun p : E × E ↦ p.2 - p.1) ''
    (Metric.closedBall x₀ 1 ×ˢ tsupport (ψ : E → F))
  refine ⟨(x, x + y), ⟨hx, ?_⟩, ?_⟩
  · exact subset_tsupport _ hy
  · simp
-- END SEAT AREA

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
  sorry

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
  sorry

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
  sorry

lemma tft_difference_quotient_continuous
    (f : E → F) (hf : ContDiff ℝ 1 f) (x v : E) (h : ℝ) :
    Continuous (fun y => h⁻¹ • (f (x + h • v + y) - f (x + y))) := by
  sorry

lemma tft_difference_quotient_hasCompactSupport
    (f : E → F) (hfc : HasCompactSupport f) (x v : E) (h : ℝ) :
    HasCompactSupport (fun y => h⁻¹ • (f (x + h • v + y) - f (x + y))) := by
  sorry

lemma tft_fderiv_translate_continuous
    (f : E → F) (hf : ContDiff ℝ 1 f) (x v : E) :
    Continuous (fun y => fderiv ℝ f (x + y) v) := by
  sorry

lemma tft_fderiv_translate_hasCompactSupport
    (f : E → F) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (x v : E) :
    HasCompactSupport (fun y => fderiv ℝ f (x + y) v) := by
  sorry

/-- U2: the directional difference quotient converges in sup norm. -/
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
  sorry

/-- S1: continuity into the fixed stage.  The hypothesis is precisely U1 for
every iterated derivative (the maps occurring in `continuous_iff_comp`). -/
lemma tft_stage_continuousAt_of_structure_maps
    (ψ : TFT E F) (x₀ : E)
    (hU1 : ∀ i : ℕ, ContinuousAt
      (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i ∘
        tftTranslateStageLocal ψ x₀) x₀) :
    ContinuousAt (tftTranslateStageLocal ψ x₀) x₀ := by
  sorry

/-- S1 with U1 discharged for every iterated derivative of `ψ`. -/
lemma tft_stage_continuousAt (ψ : TFT E F) (x₀ : E) :
    ContinuousAt (tftTranslateStageLocal ψ x₀) x₀ := by
  sorry

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
  sorry

/-- S2 with U2 discharged for every iterated derivative of `ψ`. -/
lemma tft_stage_difference_quotient (ψ : TFT E F) (x₀ v : E) :
    Tendsto (fun h : ℝ => h⁻¹ •
        (tftTranslateStageLocal ψ x₀ (x₀ + h • v) -
          tftTranslateStageLocal ψ x₀ x₀))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (tftDirectionalTranslateStage ψ x₀ x₀ v)) := by
  sorry

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
