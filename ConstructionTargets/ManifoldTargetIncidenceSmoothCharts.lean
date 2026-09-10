import ConstructionTargets.LocalTransverseExtensionChart
import ConstructionTargets.ManifoldTargetIncidenceCoordinateTransport
import ConstructionTargets.FiberPredicateTransfer
open Set Filter
open scoped ContDiff Manifold Topology
noncomputable section
namespace ConstructionTargets.ManifoldTargetIncidenceSmoothCharts
variable {E G F M N P : Type*}
 [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
 [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G] [CompleteSpace G]
 [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
 [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
 [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℝ,G) ∞ N]
 [TopologicalSpace P] [ChartedSpace F P] [IsManifold 𝓘(ℝ,F) ∞ P]
local instance : ChartedSpace (E × G) (M × N) := prodChartedSpace E M G N
local instance : IsManifold 𝓘(ℝ,E × G) ∞ (M × N) := by
 rw [modelWithCornersSelf_prod]
 exact IsManifold.prod M N
abbrev Model := RegularFiberFixedModelOverlaps.Model (E := E × G) (F := F)
structure IncidenceChart (f : M → P) (g : N → P) where
 chart : OpenPartialHomeomorph {z : M × N // f z.1 = g z.2} (Model (E := E) (G := G) (F := F))
 ambient : Set (M × N)
 forward : M × N → Model (E := E) (G := G) (F := F)
 backward : Model (E := E) (G := G) (F := F) → M × N
 source_eq : chart.source = Subtype.val ⁻¹' ambient
 forward_eq : ∀ z ∈ chart.source, chart z = forward z.val
 backward_eq : ∀ z ∈ chart.target, (chart.symm z).val = backward z
 forward_smooth : ContMDiffOn 𝓘(ℝ,E × G) 𝓘(ℝ,Model (E := E) (G := G) (F := F)) ∞ forward ambient
 backward_smooth : ContMDiffOn 𝓘(ℝ,Model (E := E) (G := G) (F := F)) 𝓘(ℝ,E × G) ∞ backward chart.target
theorem exists_chart (f : M → P) (g : N → P)
 (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f) (hg : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,F) ∞ g)
 (x : M) (y : N) (h : f x = g y)
 (ht : LinearMap.range (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x).toLinearMap ⊔
       LinearMap.range (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,F) g y).toLinearMap = ⊤) :
 ∃ d : IncidenceChart (E := E) (G := G) (F := F) f g,
   (⟨(x,y),h⟩ : {z : M × N // f z.1 = g z.2}) ∈ d.chart.source := by
 letI : ChartedSpace (E × G) (E × G) := chartedSpaceSelf (E × G)
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
 let t := p.trans q.chart
 let C : Set (M × N) := {z | z ∈ k.source ∧ k z ∈ W ∧ k z ∈ q.ambient}
 have hp (z) (hz : z ∈ p.source) : (p z).val = k z.val :=
   FiberPredicateTransfer.forward_eq k R S W hW hWt heq u hu huW z hz
 have hps : p.source = {z | z.val ∈ k.source ∧ k z.val ∈ W} :=
   FiberPredicateTransfer.source_eq k R S W hW hWt heq u hu huW
 have hpt : p.target = Subtype.val ⁻¹' W :=
   FiberPredicateTransfer.target_eq k R S W hW hWt heq u hu huW
 have hsource : t.source = Subtype.val ⁻¹' C := by
   ext z
   change (z ∈ p.source ∧ p z ∈ q.chart.source) ↔ _
   rw [q.source_eq]
   constructor
   · rintro ⟨hz,hqz⟩
     change (p z).val ∈ q.ambient at hqz
     rw [hp z hz] at hqz
     rw [hps] at hz
     exact ⟨hz.1,hz.2,hqz⟩
   · rintro ⟨hz,hw,hqz⟩
     have hz' : z ∈ p.source := by rw [hps]; exact ⟨hz,hw⟩
     refine ⟨hz',?_⟩
     change (p z).val ∈ q.ambient
     rw [hp z hz']
     exact hqz
 have hb (z) (hz : z ∈ t.target) : q.backward z ∈ W := by
   have hv : (q.chart.symm z).val ∈ W := by
     have hh := hz.2
     change q.chart.symm z ∈ p.target at hh
     rwa [hpt] at hh
   rwa [q.backward_eq z hz.1] at hv
 refine ⟨⟨t,C,q.forward ∘ k,k.symm ∘ q.backward,hsource,?_,?_,?_,?_⟩,?_⟩
 · intro z hz
   change q.chart (p z) = q.forward (k z.val)
   rw [q.forward_eq, hp z hz.1]
 · intro z hz
   change (p.symm (q.chart.symm z)).val = k.symm (q.backward z)
   have hv : (q.chart.symm z).val ∈ W := by
     rw [q.backward_eq z hz.1]
     exact hb z hz
   rw [FiberPredicateTransfer.backward_eq k R S W hW hWt heq u hu huW _ hv,
     q.backward_eq z hz.1]
 · have hk : ContMDiffOn 𝓘(ℝ,E × G) 𝓘(ℝ,E × G) ∞ k C :=
     (show ContMDiffOn 𝓘(ℝ,E × G) 𝓘(ℝ,E × G) ∞ k k.source from
       (contMDiffOn_chart (I := 𝓘(ℝ,E × G)) (x := (x,y)))).mono (fun z hz => hz.1)
   exact q.forward_smooth.contMDiffOn.comp hk (fun z hz => hz.2.2)
 · have hq : ContMDiffOn 𝓘(ℝ,Model (E := E) (G := G) (F := F)) 𝓘(ℝ,E × G) ∞ q.backward t.target :=
     (q.backward_smooth.mono (show t.target ⊆ q.chart.target from fun z hz => hz.1)).contMDiffOn
   exact (show ContMDiffOn 𝓘(ℝ,E × G) 𝓘(ℝ,E × G) ∞ k.symm k.target from
     (contMDiffOn_chart_symm (I := 𝓘(ℝ,E × G)) (x := (x,y)))).comp hq (fun z hz => hWt (hb z hz))
 · have hpu : u ∈ p.source := FiberPredicateTransfer.center_mem k R S W hW hWt heq u hu huW
   change u ∈ p.source ∧ p u ∈ q.chart.source
   refine ⟨hpu,?_⟩
   have hpv : p u = ⟨(e x,d y),hz⟩ := Subtype.ext (hp u hpu)
   rw [hpv]
   exact hq
omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ G] [CompleteSpace G]
 [FiniteDimensional ℝ F] [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,G) ∞ N]
 [TopologicalSpace P] [ChartedSpace F P] [IsManifold 𝓘(ℝ,F) ∞ P] in
theorem overlap_smooth (f : M → P) (g : N → P)
 (d d' : IncidenceChart (E := E) (G := G) (F := F) f g) :
 ContDiffOn ℝ ∞ (d.chart.symm.trans d'.chart) (d.chart.symm.trans d'.chart).source := by
 let S := (d.chart.symm.trans d'.chart).source
 have hb := d.backward_smooth.mono (show S ⊆ d.chart.target from fun z hz => hz.1)
 have h := d'.forward_smooth.comp hb (by
   intro z hz
   change d.backward z ∈ d'.ambient
   rw [← d.backward_eq z hz.1]
   exact (congrArg (fun s => d.chart.symm z ∈ s) d'.source_eq).mp hz.2)
 apply h.contDiffOn.congr
 intro z hz
 change d'.chart (d.chart.symm z) = d'.forward (d.backward z)
 rw [d'.forward_eq (d.chart.symm z) hz.2, d.backward_eq z hz.1]

theorem exists_cover (f : M → P) (g : N → P)
 (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f) (hg : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,F) ∞ g)
 (ht : ∀ x y, f x = g y → LinearMap.range (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x).toLinearMap ⊔
       LinearMap.range (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,F) g y).toLinearMap = ⊤) :
 ∃ d : {z : M × N // f z.1 = g z.2} → IncidenceChart (E := E) (G := G) (F := F) f g,
 (∀ z, z ∈ (d z).chart.source) ∧
 ∀ z w, ContDiffOn ℝ ∞ ((d z).chart.symm.trans (d w).chart) ((d z).chart.symm.trans (d w).chart).source := by
 have hh (z : {z : M × N // f z.1 = g z.2}) :=
   exists_chart f g hf hg z.val.1 z.val.2 z.property (ht _ _ z.property)
 choose d hd using hh
 exact ⟨d,hd,fun z w => overlap_smooth f g (d z) (d w)⟩

theorem exists_cover_normalized (f : M → P) (g : N → P)
 (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f) (hg : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,F) ∞ g)
 (ht : ∀ x y, f x = g y → LinearMap.range (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x).toLinearMap ⊔
       LinearMap.range (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,F) g y).toLinearMap = ⊤) :
 ∃ d : {z : M × N // f z.1 = g z.2} → OpenPartialHomeomorph
   {z : M × N // f z.1 = g z.2}
   (EuclideanSpace ℝ (Fin (Module.finrank ℝ E + Module.finrank ℝ G - Module.finrank ℝ F))),
 (∀ z, z ∈ (d z).source) ∧
 ∀ z w, ContDiffOn ℝ ∞ ((d z).symm.trans (d w)) ((d z).symm.trans (d w)).source := by
 have hn : Module.finrank ℝ (E × G) = Module.finrank ℝ E + Module.finrank ℝ G := Module.finrank_prod
 rw [← hn]
 obtain ⟨d,hd,ho⟩ := exists_cover f g hf hg ht
 exact ⟨fun z => (d z).chart,hd,ho⟩
#print axioms exists_chart
#print axioms overlap_smooth
#print axioms exists_cover
#print axioms exists_cover_normalized
end ConstructionTargets.ManifoldTargetIncidenceSmoothCharts
