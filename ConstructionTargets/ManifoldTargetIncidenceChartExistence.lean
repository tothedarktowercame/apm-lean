import ConstructionTargets.LocalTransverseExtensionChart
import ConstructionTargets.ManifoldTargetIncidenceCoordinateTransport
import ConstructionTargets.FiberPredicateTransfer
open Set Filter
open scoped ContDiff Manifold Topology
noncomputable section
namespace ConstructionTargets.ManifoldTargetIncidenceChartExistence
variable {E G F M N P : Type*}
 [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
 [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G] [CompleteSpace G]
 [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
 [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
 [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℝ,G) ∞ N]
 [TopologicalSpace P] [ChartedSpace F P] [IsManifold 𝓘(ℝ,F) ∞ P]
theorem exists_chart (f : M → P) (g : N → P)
 (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f) (hg : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,F) ∞ g)
 (x : M) (y : N) (h : f x = g y)
 (ht : LinearMap.range (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x).toLinearMap ⊔
       LinearMap.range (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,F) g y).toLinearMap = ⊤) :
 ∃ d : OpenPartialHomeomorph {z : M × N // f z.1 = g z.2}
   (RegularFiberFixedModelOverlaps.Model (E := E × G) (F := F)),
   (⟨(x,y),h⟩ : {z : M × N // f z.1 = g z.2}) ∈ d.source := by
 let e := chartAt E x
 let d := chartAt G y
 let c := chartAt F (f x)
 let a := c ∘ f ∘ e.symm
 let b := c ∘ g ∘ d.symm
 let U := e.target ∩ e.symm ⁻¹' (f ⁻¹' c.source)
 let V := d.target ∩ d.symm ⁻¹' (g ⁻¹' c.source)
 have hU : IsOpen U := e.isOpen_inter_preimage_symm (c.open_source.preimage hf.continuous)
 have hV : IsOpen V := d.isOpen_inter_preimage_symm (c.open_source.preimage hg.continuous)
 have hx : e x ∈ U := by
  refine ⟨e.map_source (mem_chart_source E x), ?_⟩
  change f (e.symm (e x)) ∈ c.source
  rw [e.left_inv (mem_chart_source E x)]
  exact mem_chart_source F (f x)
 have hy : d y ∈ V := by
  refine ⟨d.map_source (mem_chart_source G y), ?_⟩
  change g (d.symm (d y)) ∈ c.source
  rw [d.left_inv (mem_chart_source G y), ← h]
  exact mem_chart_source F (f x)
 have hab : a (e x) = b (d y) := by
  dsimp [a,b]
  rw [e.left_inv (mem_chart_source E x), d.left_inv (mem_chart_source G y), h]
 obtain ⟨aa,bb,haa,hbb,hea,heb,hz,q,hq⟩ := LocalTransverseExtensionChart.exists_chart
   a b U V hU hV
   (ManifoldTargetFiberChartExtension.representative_smooth f hf x)
   (ManifoldTargetIncidenceCoordinateTransport.right_smooth f g hg x y h)
   (e x) (d y) hx hy hab
   (ManifoldTargetIncidenceCoordinateTransport.coordinate_transversality f g hf hg x y h ht)
 obtain ⟨A,hA,hAo,hxA⟩ := mem_nhds_iff.mp hea
 obtain ⟨B,hB,hBo,hyB⟩ := mem_nhds_iff.mp heb
 let W := (A ∩ U) ×ˢ (B ∩ V)
 have hW : IsOpen W := (hAo.inter hU).prod (hBo.inter hV)
 let k := e.prod d
 let R := fun z : M × N => f z.1 = g z.2
 let S := fun z : E × G => LocalTransverseDifference.difference aa bb z = 0
 have hWt : W ⊆ k.target := fun z hz => ⟨hz.1.2.1,hz.2.2.1⟩
 have heq (z) (hz : z ∈ W) : S z ↔ R (k.symm z) := by
  change aa z.1 - bb z.2 = 0 ↔ f (e.symm z.1) = g (d.symm z.2)
  rw [hA hz.1.1, hB hz.2.1, sub_eq_zero]
  exact c.injOn.eq_iff hz.1.2.2 hz.2.2.2
 let u : {z // R z} := ⟨(x,y),h⟩
 have hu : u.val ∈ k.source := ⟨mem_chart_source E x, mem_chart_source G y⟩
 have huW : k u.val ∈ W := ⟨⟨hxA,hx⟩,⟨hyB,hy⟩⟩
 let p := FiberPredicateTransfer.transfer k R S W hW hWt heq u hu huW
 refine ⟨p.trans q.chart, ?_⟩
 have hp : u ∈ p.source := FiberPredicateTransfer.center_mem k R S W hW hWt heq u hu huW
 change u ∈ p.source ∧ p u ∈ q.chart.source
 refine ⟨hp,?_⟩
 have hpv : p u = ⟨(e x,d y),hz⟩ := Subtype.ext
   (FiberPredicateTransfer.forward_eq k R S W hW hWt heq u hu huW u hp)
 rw [hpv]
 exact hq
theorem exists_chart_normalized (f : M → P) (g : N → P)
 (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f) (hg : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,F) ∞ g)
 (x : M) (y : N) (h : f x = g y)
 (ht : LinearMap.range (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x).toLinearMap ⊔
       LinearMap.range (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,F) g y).toLinearMap = ⊤) :
 ∃ d : OpenPartialHomeomorph {z : M × N // f z.1 = g z.2}
   (EuclideanSpace ℝ (Fin (Module.finrank ℝ E + Module.finrank ℝ G - Module.finrank ℝ F))),
   (⟨(x,y),h⟩ : {z : M × N // f z.1 = g z.2}) ∈ d.source := by
 have hd : Module.finrank ℝ (E × G) = Module.finrank ℝ E + Module.finrank ℝ G := Module.finrank_prod
 rw [← hd]
 exact exists_chart f g hf hg x y h ht
#print axioms exists_chart_normalized
#print axioms exists_chart
end ConstructionTargets.ManifoldTargetIncidenceChartExistence
