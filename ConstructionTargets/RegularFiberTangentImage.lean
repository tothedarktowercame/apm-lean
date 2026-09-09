import ConstructionTargets.RegularFiberSmoothInclusion

open Set Filter
open scoped ContDiff Manifold Topology
noncomputable section
namespace ConstructionTargets.RegularFiberTangentImage
open RegularFiberFixedModelOverlaps RegularFiberGlobalAtlas
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (f : E → F) (c : F) (hsm : ContDiff ℝ ∞ f)
  (hreg : ∀ x, f x = c → Function.Surjective (fderiv ℝ f x))
omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ F] in
lemma backward_injective (d : FiberChart f c) (z : Model (E := E) (F := F))
    (hz : z ∈ d.chart.target) : Function.Injective (fderiv ℝ d.backward z) := by
  have hm : MapsTo d.backward d.chart.target d.ambient := by
    intro w hw
    rw [← d.backward_eq w hw]
    have ht := d.chart.map_target hw
    rwa [d.source_eq] at ht
  have hd := (d.backward_smooth.contDiffAt (d.chart.open_target.mem_nhds hz)).differentiableAt (by simp)
  have hf := (d.forward_smooth.differentiableOn (by simp) _ (hm hz)).hasFDerivWithinAt
  have hc := hf.comp_hasFDerivAt z hd.hasFDerivAt
    (Filter.eventually_of_mem (d.chart.open_target.mem_nhds hz) (fun w hw => hm hw))
  have he : d.forward ∘ d.backward =ᶠ[𝓝 z] id := by
    filter_upwards [d.chart.open_target.mem_nhds hz] with w hw
    change d.forward (d.backward w) = w
    rw [← d.backward_eq w hw, ← d.forward_eq, d.chart.right_inv hw]
  have hid := hc.congr_of_eventuallyEq he.symm
  have hcomp := hid.unique (hasFDerivAt_id z)
  intro a b hab
  have h := congrArg (fun L : Model (E := E) (F := F) →L[ℝ] Model (E := E) (F := F) => L a) hcomp
  have h' := congrArg (fun L : Model (E := E) (F := F) →L[ℝ] Model (E := E) (F := F) => L b) hcomp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h h'
  rw [hab] at h
  exact h.symm.trans h'

lemma derivative_eq (x : {x : E // f x = c}) :
    letI := chartedSpace f c hsm hreg
    mfderiv 𝓘(ℝ, Model (E := E) (F := F)) 𝓘(ℝ,E) Subtype.val x =
      fderiv ℝ (selected f c hsm hreg x).backward ((selected f c hsm hreg x).chart x) := by
  letI := chartedSpace f c hsm hreg
  have hd := (RegularFiberSmoothInclusion.smooth_inclusion f c hsm hreg).mdifferentiable (by simp) x
  rw [mfderiv, if_pos hd]
  simp only [writtenInExtChartAt, mfld_simps]
  change fderivWithin ℝ (fun z => ((selected f c hsm hreg x).chart.symm z).val) Set.univ
    ((selected f c hsm hreg x).chart x) = _
  rw [fderivWithin_univ]
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [(selected f c hsm hreg x).chart.open_target.mem_nhds
    ((selected f c hsm hreg x).chart.map_source (selected_center f c hsm hreg x))] with z hz
  exact (selected f c hsm hreg x).backward_eq z hz
theorem inclusion_injective (x : {x : E // f x = c}) :
    letI := chartedSpace f c hsm hreg
    Function.Injective (mfderiv 𝓘(ℝ, Model (E := E) (F := F)) 𝓘(ℝ,E) Subtype.val x) := by
  letI := chartedSpace f c hsm hreg
  rw [derivative_eq f c hsm hreg x]
  exact backward_injective f c _ _
    ((selected f c hsm hreg x).chart.map_source (selected_center f c hsm hreg x))

theorem inclusion_range (x : {x : E // f x = c}) :
    letI := chartedSpace f c hsm hreg
    LinearMap.range (mfderiv 𝓘(ℝ, Model (E := E) (F := F)) 𝓘(ℝ,E) Subtype.val x).toLinearMap =
      (fderiv ℝ f x.val).ker := by
  letI := chartedSpace f c hsm hreg
  let d := selected f c hsm hreg x
  have hz : d.chart x ∈ d.chart.target := d.chart.map_source (selected_center f c hsm hreg x)
  have hx : d.backward (d.chart x) = x.val := by
    rw [← d.backward_eq _ hz, d.chart.left_inv (selected_center f c hsm hreg x)]
  have hb := (d.backward_smooth.contDiffAt (d.chart.open_target.mem_nhds hz)).differentiableAt (by simp)
  have hf : HasFDerivAt f (fderiv ℝ f x.val) (d.backward (d.chart x)) := by
    rw [hx]
    exact (hsm.differentiable (by simp) x.val).hasFDerivAt
  have hc := hf.comp (d.chart x) hb.hasFDerivAt
  have he : f ∘ d.backward =ᶠ[𝓝 (d.chart x)] (fun _ => c) := by
    filter_upwards [d.chart.open_target.mem_nhds hz] with z hz'
    change f (d.backward z) = c
    rw [← d.backward_eq _ hz']
    exact (d.chart.symm z).property
  have hzero := (hc.congr_of_eventuallyEq he.symm).unique (hasFDerivAt_const c (d.chart x))
  have hle : LinearMap.range (fderiv ℝ d.backward (d.chart x)).toLinearMap ≤ (fderiv ℝ f x.val).ker := by
    rintro y ⟨v, rfl⟩
    change (fderiv ℝ f x.val) ((fderiv ℝ d.backward (d.chart x)) v) = 0
    exact congrArg (fun L : Model (E := E) (F := F) →L[ℝ] F => L v) hzero
  rw [derivative_eq f c hsm hreg x]
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearMap.finrank_range_of_inj (backward_injective f c d _ hz)]
  rw [RegularFiberFixedModel.kernel_dimension _ (hreg x.val x.property)]
  simp [Model, RegularFiberFixedModel.Model]
#print axioms backward_injective
#print axioms derivative_eq
#print axioms inclusion_injective
#print axioms inclusion_range
end ConstructionTargets.RegularFiberTangentImage
