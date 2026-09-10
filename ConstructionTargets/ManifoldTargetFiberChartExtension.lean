import ConstructionTargets.SardGenuineSmoothOpenDomainLocalization
import ConstructionTargets.RegularFiberFixedModelOverlaps
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
open Set Filter
open scoped ContDiff Manifold Topology
noncomputable section
namespace ConstructionTargets.ManifoldTargetFiberChartExtension
variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
  (f : M → N) (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f) (x : M)
include hf
omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ F] in
lemma representative_smooth :
    ContDiffOn ℝ ∞ ((chartAt F (f x)) ∘ f ∘ (chartAt E x).symm)
      ((chartAt E x).target ∩ (chartAt E x).symm ⁻¹' (f ⁻¹' (chartAt F (f x)).source)) := by
  simpa only [extChartAt, mfld_simps] using (contMDiff_iff.mp hf).2 x (f x)
omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ F] [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
lemma representative_derivative :
    fderiv ℝ ((chartAt F (f x)) ∘ f ∘ (chartAt E x).symm) ((chartAt E x) x) =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x := by
  rw [mfderiv, if_pos (hf.mdifferentiable (by simp) x)]
  simp only [writtenInExtChartAt, mfld_simps]
  rw [fderivWithin_univ]

theorem exists_extension_chart
    (hs : Function.Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x)) :
    ∃ (g : E → F) (_hg : ContDiff ℝ ∞ g) (V : Set E),
      IsOpen V ∧ (chartAt E x) x ∈ V ∧
      V ⊆ ((chartAt E x).target ∩ (chartAt E x).symm ⁻¹' (f ⁻¹' (chartAt F (f x)).source)) ∧
      (∀ z ∈ V, g z = (chartAt F (f x)) (f ((chartAt E x).symm z))) ∧
      (∀ z ∈ V, fderiv ℝ g z = fderiv ℝ ((chartAt F (f x)) ∘ f ∘ (chartAt E x).symm) z) ∧
      (∀ z ∈ V, g z = (chartAt F (f x)) (f x) ↔ f ((chartAt E x).symm z) = f x) ∧
      ∃ (hx : g ((chartAt E x) x) = (chartAt F (f x)) (f x))
        (d : RegularFiberFixedModelOverlaps.FiberChart g ((chartAt F (f x)) (f x))),
        (⟨(chartAt E x) x, hx⟩ : {z // g z = (chartAt F (f x)) (f x)}) ∈ d.chart.source := by
  letI : MeasurableSpace F := borel F
  letI : BorelSpace F := ⟨rfl⟩
  let e := chartAt E x
  let v := chartAt F (f x)
  let U := e.target ∩ e.symm ⁻¹' (f ⁻¹' v.source)
  have hU : IsOpen U := e.isOpen_inter_preimage_symm (v.open_source.preimage hf.continuous)
  have hxU : e x ∈ U := by
    refine ⟨e.map_source (mem_chart_source E x), ?_⟩
    change f (e.symm (e x)) ∈ v.source
    rw [e.left_inv (mem_chart_source E x)]
    exact mem_chart_source F (f x)
  obtain ⟨g,hg,he⟩ := SardGenuineSmoothOpenDomainLocalizationProbe.exists_smooth_extension_near
    (v ∘ f ∘ e.symm) U hU (representative_smooth f hf x) (e x) hxU
  obtain ⟨W,hW,hWo,hxW⟩ := mem_nhds_iff.mp he
  let V := W ∩ U
  have hVo : IsOpen V := hWo.inter hU
  have hxV : e x ∈ V := ⟨hxW,hxU⟩
  have hv (z) (hz : z ∈ V) : g z = v (f (e.symm z)) := hW hz.1
  have hd (z) (hz : z ∈ V) : fderiv ℝ g z = fderiv ℝ (v ∘ f ∘ e.symm) z := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hVo.mem_nhds hz] with w hw
    exact hv w hw
  have hiff (z) (hz : z ∈ V) : g z = v (f x) ↔ f (e.symm z) = f x := by
    rw [hv z hz]
    exact v.injOn.eq_iff hz.2.2 (mem_chart_source F (f x))
  have hx : g (e x) = v (f x) := by
    rw [hv _ hxV, e.left_inv (mem_chart_source E x)]
  have hgs : Function.Surjective (fderiv ℝ g (e x)) := by
    rw [hd _ hxV, representative_derivative f hf x]
    exact hs
  obtain ⟨d,hdc⟩ := RegularFiberFixedModelOverlaps.exists_chart g (v (f x)) hg ⟨e x,hx⟩ hgs
  exact ⟨g,hg,V,hVo,hxV,inter_subset_right,hv,hd,hiff,hx,d,hdc⟩
#print axioms representative_smooth
#print axioms representative_derivative
#print axioms exists_extension_chart
end ConstructionTargets.ManifoldTargetFiberChartExtension
