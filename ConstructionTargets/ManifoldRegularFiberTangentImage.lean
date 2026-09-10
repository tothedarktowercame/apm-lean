import ConstructionTargets.ManifoldRegularFiberGlobalAtlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
open Set Filter
open scoped ContDiff Manifold Topology
noncomputable section
namespace ConstructionTargets.ManifoldRegularFiberTangentImage
open ManifoldRegularFiberCharts ManifoldRegularFiberGlobalAtlas
variable {E F M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (f : M → F) (c : F) (hsm : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
  (hreg : ∀ x, f x = c → Function.Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x))
omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ F] [IsManifold 𝓘(ℝ,E) ∞ M] in
lemma backward_injective (d : FiberChart (E := E) f c)
    (z : Model (E := E) (F := F)) (hz : z ∈ d.chart.target) :
    Function.Injective (mfderiv 𝓘(ℝ,Model (E := E) (F := F)) 𝓘(ℝ,E) d.backward z) := by
  have hm : MapsTo d.backward d.chart.target d.ambient := by
    intro w hw
    rw [← d.backward_eq w hw]
    have ht := d.chart.map_target hw
    rwa [d.source_eq] at ht
  have hd := (d.backward_smooth.contMDiffAt (d.chart.open_target.mem_nhds hz)).mdifferentiableAt (by simp)
  have hf := d.forward_smooth.mdifferentiableOn (by simp) _ (hm hz)
  have hc := mfderivWithin_comp z hf hd.mdifferentiableWithinAt hm
    (d.chart.open_target.uniqueMDiffWithinAt hz)
  simp only [mfderivWithin_of_mem_nhds (d.chart.open_target.mem_nhds hz)] at hc
  have he : d.forward ∘ d.backward =ᶠ[𝓝 z] id := by
    filter_upwards [d.chart.open_target.mem_nhds hz] with w hw
    change d.forward (d.backward w) = w
    rw [← d.backward_eq w hw, ← d.forward_eq _ (d.chart.map_target hw), d.chart.right_inv hw]
  rw [he.mfderiv_eq, mfderiv_id] at hc
  intro a b hab
  have h := congrArg (fun L : Model (E := E) (F := F) →L[ℝ] Model (E := E) (F := F) => L a) hc
  have h' := congrArg (fun L : Model (E := E) (F := F) →L[ℝ] Model (E := E) (F := F) => L b) hc
  change a = (mfderivWithin 𝓘(ℝ,E) 𝓘(ℝ,Model (E := E) (F := F)) d.forward d.ambient (d.backward z)) ((mfderiv 𝓘(ℝ,Model (E := E) (F := F)) 𝓘(ℝ,E) d.backward z) a) at h
  change b = (mfderivWithin 𝓘(ℝ,E) 𝓘(ℝ,Model (E := E) (F := F)) d.forward d.ambient (d.backward z)) ((mfderiv 𝓘(ℝ,Model (E := E) (F := F)) 𝓘(ℝ,E) d.backward z) b) at h'
  rw [hab] at h
  exact h.trans h'.symm
lemma derivative_eq (x : {x : M // f x = c}) :
    letI := chartedSpace f c hsm hreg
    mfderiv 𝓘(ℝ,Model (E := E) (F := F)) 𝓘(ℝ,E) Subtype.val x =
      mfderiv 𝓘(ℝ,Model (E := E) (F := F)) 𝓘(ℝ,E)
        (selected f c hsm hreg x).backward ((selected f c hsm hreg x).chart x) := by
  letI := chartedSpace f c hsm hreg
  let d := selected f c hsm hreg x
  have hz : d.chart x ∈ d.chart.target := d.chart.map_source (selected_center f c hsm hreg x)
  have hx : d.backward (d.chart x) = x.val := by
    rw [← d.backward_eq _ hz, d.chart.left_inv (selected_center f c hsm hreg x)]
  have hd := (smooth_inclusion f c hsm hreg).mdifferentiable (by simp) x
  have hb := (d.backward_smooth.contMDiffAt (d.chart.open_target.mem_nhds hz)).mdifferentiableAt (by simp)
  change _ = mfderiv _ _ d.backward (d.chart x)
  rw [mfderiv, if_pos hd, mfderiv, if_pos hb]
  simp only [writtenInExtChartAt, mfld_simps]
  simp only [hx]
  apply Filter.EventuallyEq.fderivWithin_eq
  · filter_upwards [Filter.mem_of_superset (d.chart.open_target.mem_nhds hz) (fun z hz => hz) |> mem_nhdsWithin_of_mem_nhds] with z hz'
    exact congrArg (chartAt E x.val) (d.backward_eq z hz')
  · exact congrArg (chartAt E x.val) (d.backward_eq (d.chart x) hz)

theorem inclusion_injective (x : {x : M // f x = c}) :
    letI := chartedSpace f c hsm hreg
    Function.Injective (mfderiv 𝓘(ℝ,Model (E := E) (F := F)) 𝓘(ℝ,E) Subtype.val x) := by
  letI := chartedSpace f c hsm hreg
  rw [derivative_eq f c hsm hreg x]
  exact backward_injective f c _ _
    ((selected f c hsm hreg x).chart.map_source (selected_center f c hsm hreg x))
theorem inclusion_range (x : {x : M // f x = c}) :
    letI := chartedSpace f c hsm hreg
    LinearMap.range (mfderiv 𝓘(ℝ,Model (E := E) (F := F)) 𝓘(ℝ,E) Subtype.val x).toLinearMap =
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x.val).ker := by
  letI := chartedSpace f c hsm hreg
  letI := isManifold f c hsm hreg
  have hi := (smooth_inclusion f c hsm hreg).mdifferentiable (by simp) x
  have hc := mfderiv_comp x (hsm.mdifferentiable (by simp) x.val) hi
  have he : (f ∘ (Subtype.val : {x : M // f x = c} → M)) = (fun _ => c) := by
    funext y
    exact y.property
  rw [he, mfderiv_const] at hc
  have hle : LinearMap.range (mfderiv 𝓘(ℝ,Model (E := E) (F := F)) 𝓘(ℝ,E) Subtype.val x).toLinearMap ≤
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x.val).ker := by
    rintro y ⟨v, rfl⟩
    have hv := congrArg (fun L => L v) hc
    exact hv.symm
  letI : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) x.val) := inferInstanceAs (FiniteDimensional ℝ E)
  letI : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model (E := E) (F := F)) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model (E := E) (F := F)))
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearMap.finrank_range_of_inj (inclusion_injective f c hsm hreg x)]
  have hk := RegularFiberFixedModel.kernel_dimension (E := E) (F := F)
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x.val) (hreg x.val x.property)
  calc
    _ = Module.finrank ℝ E - Module.finrank ℝ F := by
      change Module.finrank ℝ (Model (E := E) (F := F)) = _
      simp [ManifoldRegularFiberCharts.Model, RegularFiberFixedModelOverlaps.Model, RegularFiberFixedModel.Model]
    _ = _ := hk.symm

#print axioms inclusion_range
#print axioms derivative_eq
#print axioms inclusion_injective
#print axioms backward_injective
end ConstructionTargets.ManifoldRegularFiberTangentImage
