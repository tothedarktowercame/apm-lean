import Mathlib
import ConstructionTargets.ScaledTriangleNeighborhood
noncomputable section
open Set Topology
namespace ConstructionTargets.ChartTriangleEmbedding
open StandardTriangleEmbedding ScaledTriangleNeighborhood
variable {M : Type*} [TopologicalSpace M] [T2Space M]

theorem exists_chart_triangle (e : OpenPartialHomeomorph M (ℝ × ℝ)) (x : M)
 (hx : x ∈ e.source) :
 ∃ r : ℝ, 0 < r ∧ Set.range (scaled (e x) r) ⊆ e.target ∧
 IsClosedEmbedding (e.symm ∘ scaled (e x) r) ∧
 IsCompact (Set.range (e.symm ∘ scaled (e x) r)) ∧
 Set.range (e.symm ∘ scaled (e x) r) ⊆ e.source ∧
 IsOpen ((e.symm ∘ scaled (e x) r) '' interiorParameters) ∧
 x ∈ (e.symm ∘ scaled (e x) r) '' interiorParameters := by
 obtain ⟨r,hr,hemb,hcompact,hsub,hopen,hcenter⟩ :=
  exists_triangle e.target e.open_target (e x) (e.map_source hx)
 have hm : MapsTo (scaled (e x) r) Set.univ e.target := fun z _ => hsub ⟨z,rfl⟩
 have hc : Continuous (e.symm ∘ scaled (e x) r) :=
  continuousOn_univ.mp (e.continuousOn_symm.comp hemb.continuous.continuousOn hm)
 have hi : Function.Injective (e.symm ∘ scaled (e x) r) := by
  intro a b h
  exact hemb.injective (e.symm.injOn (hm (Set.mem_univ a)) (hm (Set.mem_univ b)) h)
 refine ⟨r,hr,hsub,hc.isClosedEmbedding hi,isCompact_range hc,?_,?_,?_⟩
 · rintro _ ⟨z,rfl⟩
   exact e.map_target (hm (Set.mem_univ z))
 · rw [Set.image_comp]
   exact e.symm.isOpen_image_of_subset_source hopen (fun y hy => hsub (Set.image_subset_range _ _ hy))
 · obtain ⟨z,hz,heq⟩ := hcenter
   refine ⟨z,hz,?_⟩
   change e.symm (scaled (e x) r z) = x
   rw [heq,e.left_inv hx]

#print axioms exists_chart_triangle
end ConstructionTargets.ChartTriangleEmbedding
