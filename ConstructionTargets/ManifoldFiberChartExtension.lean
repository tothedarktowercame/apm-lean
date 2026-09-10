import ConstructionTargets.SardGenuineSmoothOpenDomainLocalization
import ConstructionTargets.RegularFiberFixedModelOverlaps
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
open Set Filter
open scoped ContDiff Manifold Topology
noncomputable section
namespace ConstructionTargets.ManifoldFiberChartExtension
variable {E F M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (f : M → F) (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f) (x : M)
include hf
omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ F] in
lemma representative_smooth : ContDiffOn ℝ ∞ (f ∘ (chartAt E x).symm) (chartAt E x).target := by
  exact (hf.comp_contMDiffOn contMDiffOn_chart_symm).contDiffOn
omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ F] in
omit [IsManifold 𝓘(ℝ,E) ∞ M] in
lemma representative_derivative :
    fderiv ℝ (f ∘ (chartAt E x).symm) ((chartAt E x) x) =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x := by
  rw [mfderiv, if_pos (hf.mdifferentiable (by simp) x)]
  simp only [writtenInExtChartAt, mfld_simps]
  rw [fderivWithin_univ]

theorem exists_extension_chart
    (hs : Function.Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x)) :
    ∃ (g : E → F) (_hg : ContDiff ℝ ∞ g) (V : Set E),
      IsOpen V ∧ (chartAt E x) x ∈ V ∧ V ⊆ (chartAt E x).target ∧
      (∀ z ∈ V, g z = f ((chartAt E x).symm z)) ∧
      (∀ z ∈ V, fderiv ℝ g z = fderiv ℝ (f ∘ (chartAt E x).symm) z) ∧
      ∃ (hx : g ((chartAt E x) x) = f x)
        (d : RegularFiberFixedModelOverlaps.FiberChart g (f x)),
        (⟨(chartAt E x) x, hx⟩ : {z // g z = f x}) ∈ d.chart.source := by
  letI : MeasurableSpace F := borel F
  letI : BorelSpace F := ⟨rfl⟩
  let e := chartAt E x
  obtain ⟨g,hg,he⟩ := SardGenuineSmoothOpenDomainLocalizationProbe.exists_smooth_extension_near
    (f ∘ e.symm) e.target e.open_target (representative_smooth f hf x) (e x)
    (e.map_source (mem_chart_source E x))
  obtain ⟨W,hW,hWo,hxW⟩ := mem_nhds_iff.mp he
  let V := W ∩ e.target
  have hVo : IsOpen V := hWo.inter e.open_target
  have hxV : e x ∈ V := ⟨hxW,e.map_source (mem_chart_source E x)⟩
  have hv (z) (hz : z ∈ V) : g z = f (e.symm z) := hW hz.1
  have hd (z) (hz : z ∈ V) : fderiv ℝ g z = fderiv ℝ (f ∘ e.symm) z := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hVo.mem_nhds hz] with w hw
    exact hv w hw
  have hx : g (e x) = f x := by
    rw [hv _ hxV, e.left_inv (mem_chart_source E x)]
  have hgs : Function.Surjective (fderiv ℝ g (e x)) := by
    rw [hd _ hxV, representative_derivative f hf x]
    exact hs
  obtain ⟨d,hdc⟩ := RegularFiberFixedModelOverlaps.exists_chart g (f x) hg ⟨e x,hx⟩ hgs
  exact ⟨g,hg,V,hVo,hxV,inter_subset_right,hv,hd,hx,d,hdc⟩
#print axioms representative_smooth
#print axioms representative_derivative
#print axioms exists_extension_chart
end ConstructionTargets.ManifoldFiberChartExtension
