import ConstructionTargets.ManifoldTargetIncidenceCoordinateTransport
import ConstructionTargets.LocalTransverseDifference
open Set
open scoped ContDiff Manifold
noncomputable section
namespace ConstructionTargets.ManifoldTargetIncidenceDifference
variable {E G F M N P : Type*}
 [NormedAddCommGroup E] [InnerProductSpace ℝ E]
 [NormedAddCommGroup G] [InnerProductSpace ℝ G]
 [NormedAddCommGroup F] [InnerProductSpace ℝ F]
 [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
 [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℝ,G) ∞ N]
 [TopologicalSpace P] [ChartedSpace F P] [IsManifold 𝓘(ℝ,F) ∞ P]
 (f : M → P) (g : N → P)
 (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
 (hg : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,F) ∞ g)
 (x : M) (y : N) (h : f x = g y)

include hf hg h in
theorem local_packet
 (ht : LinearMap.range (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x).toLinearMap ⊔
       LinearMap.range (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,F) g y).toLinearMap = ⊤) :
 let a := (chartAt F (f x)) ∘ f ∘ (chartAt E x).symm
 let b := (chartAt F (f x)) ∘ g ∘ (chartAt G y).symm
 let U := (chartAt E x).target ∩ (chartAt E x).symm ⁻¹' (f ⁻¹' (chartAt F (f x)).source)
 let V := (chartAt G y).target ∩ (chartAt G y).symm ⁻¹' (g ⁻¹' (chartAt F (f x)).source)
 let z := ((chartAt E x) x, (chartAt G y) y)
 IsOpen (U ×ˢ V) ∧ z ∈ U ×ˢ V ∧
 ContDiffOn ℝ ∞ (LocalTransverseDifference.difference a b) (U ×ˢ V) ∧
 LocalTransverseDifference.difference a b z = 0 ∧
 Function.Surjective (fderiv ℝ (LocalTransverseDifference.difference a b) z) := by
 dsimp only
 let e := chartAt E x
 let d := chartAt G y
 let c := chartAt F (f x)
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
 have ha := ManifoldTargetFiberChartExtension.representative_smooth f hf x
 have hb := ManifoldTargetIncidenceCoordinateTransport.right_smooth f g hg x y h
 refine ⟨hU.prod hV, ⟨hx,hy⟩, LocalTransverseDifference.smooth_on _ _ ha hb, ?_, ?_⟩
 · simp only [LocalTransverseDifference.difference, Function.comp_apply]
   rw [(chartAt E x).left_inv (mem_chart_source E x),
     (chartAt G y).left_inv (mem_chart_source G y), h, sub_self]
 · apply LocalTransverseDifference.surjective
   · exact (ha.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
   · exact (hb.contDiffAt (hV.mem_nhds hy)).differentiableAt (by simp)
   · exact ManifoldTargetIncidenceCoordinateTransport.coordinate_transversality f g hf hg x y h ht
#print axioms local_packet
end ConstructionTargets.ManifoldTargetIncidenceDifference
