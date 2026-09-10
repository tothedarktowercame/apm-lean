import ConstructionTargets.ManifoldTargetIncidenceSmoothCharts
import ConstructionTargets.ManifoldTargetIncidenceCoordinateTransport
import ConstructionTargets.FiberPredicateTransfer
open Set Filter
open scoped ContDiff Manifold Topology
noncomputable section
namespace ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas
section Transport
variable {X : Type*} [TopologicalSpace X] {m n : ℕ}
@[reducible] def castAtlas (h : m = n) (c : ChartedSpace (EuclideanSpace ℝ (Fin m)) X) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) X := h ▸ c

def castChart (h : m = n) (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin m))) :
    OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)) := h ▸ e

theorem cast_chartAt (h : m = n) (c : ChartedSpace (EuclideanSpace ℝ (Fin m)) X) (x : X) :
    letI := c
    letI := castAtlas h c
    chartAt (EuclideanSpace ℝ (Fin n)) x = castChart h (chartAt (EuclideanSpace ℝ (Fin m)) x) := by
  cases h
  rfl

theorem cast_atlas (h : m = n) (c : ChartedSpace (EuclideanSpace ℝ (Fin m)) X) :
    letI := c
    letI := castAtlas h c
    atlas (EuclideanSpace ℝ (Fin n)) X = castChart h '' atlas (EuclideanSpace ℝ (Fin m)) X := by
  cases h
  change atlas (EuclideanSpace ℝ (Fin m)) X = id '' atlas (EuclideanSpace ℝ (Fin m)) X
  simp

theorem cast_property (h : m = n) (c : ChartedSpace (EuclideanSpace ℝ (Fin m)) X)
    (P : ∀ k : ℕ, ChartedSpace (EuclideanSpace ℝ (Fin k)) X → Prop) (hc : P m c) :
    P n (castAtlas h c) := by cases h; exact hc
end Transport
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
open ManifoldTargetIncidenceSmoothCharts
variable (f : M → P) (g : N → P)
 (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f) (hg : ContMDiff 𝓘(ℝ,G) 𝓘(ℝ,F) ∞ g)
 (ht : ∀ x y, f x = g y → LinearMap.range (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x).toLinearMap ⊔
       LinearMap.range (mfderiv 𝓘(ℝ,G) 𝓘(ℝ,F) g y).toLinearMap = ⊤)
def selected : {z : M × N // f z.1 = g z.2} → IncidenceChart (E := E) (G := G) (F := F) f g :=
  Classical.choose (exists_cover f g hf hg ht)

theorem selected_center (x : {z : M × N // f z.1 = g z.2}) :
    x ∈ (selected f g hf hg ht x).chart.source :=
  (Classical.choose_spec (exists_cover f g hf hg ht)).1 x

@[reducible] def chartedSpace : ChartedSpace (Model (E := E) (G := G) (F := F)) {z : M × N // f z.1 = g z.2} where
  atlas := Set.range (fun x => (selected f g hf hg ht x).chart)
  chartAt x := (selected f g hf hg ht x).chart
  mem_chart_source := selected_center f g hf hg ht
  chart_mem_atlas x := ⟨x,rfl⟩

theorem chartAt_eq (x : {z : M × N // f z.1 = g z.2}) :
    letI := chartedSpace f g hf hg ht
    chartAt (Model (E := E) (G := G) (F := F)) x = (selected f g hf hg ht x).chart := rfl

theorem atlas_eq :
    letI := chartedSpace f g hf hg ht
    atlas (Model (E := E) (G := G) (F := F)) {z : M × N // f z.1 = g z.2} =
      Set.range (fun x => (selected f g hf hg ht x).chart) := rfl

theorem selected_mem_atlas (x : {z : M × N // f z.1 = g z.2}) :
    letI := chartedSpace f g hf hg ht
    (selected f g hf hg ht x).chart ∈ atlas (Model (E := E) (G := G) (F := F)) {z : M × N // f z.1 = g z.2} :=
  ⟨x,rfl⟩

theorem isManifold :
    letI := chartedSpace f g hf hg ht
    IsManifold 𝓘(ℝ, Model (E := E) (G := G) (F := F)) ∞ {z : M × N // f z.1 = g z.2} := by
  letI := chartedSpace f g hf hg ht
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨x,rfl⟩ := he
  obtain ⟨y,rfl⟩ := he'
  simpa using overlap_smooth f g (selected f g hf hg ht x) (selected f g hf hg ht y)

include hf hg ht in
theorem exists_manifold :
    ∃ charts : ChartedSpace (Model (E := E) (G := G) (F := F)) {z : M × N // f z.1 = g z.2},
      letI := charts
      IsManifold 𝓘(ℝ, Model (E := E) (G := G) (F := F)) ∞ {z : M × N // f z.1 = g z.2} :=
  ⟨chartedSpace f g hf hg ht,isManifold f g hf hg ht⟩

theorem smooth_inclusion :
    letI := chartedSpace f g hf hg ht
    ContMDiff 𝓘(ℝ, Model (E := E) (G := G) (F := F)) 𝓘(ℝ,E × G) ∞
      (Subtype.val : {z : M × N // f z.1 = g z.2} → M × N) := by
  letI := chartedSpace f g hf hg ht
  letI := isManifold f g hf hg ht
  apply contMDiff_iff.mpr
  refine ⟨continuous_subtype_val, ?_⟩
  intro x y
  let d := selected f g hf hg ht x
  have hb : ContMDiffOn 𝓘(ℝ,Model (E := E) (G := G) (F := F)) 𝓘(ℝ,E × G) ∞
      (fun z => (d.chart.symm z).val) d.chart.target :=
    d.backward_smooth.congr (fun z hz => d.backward_eq z hz)
  have hh := (contMDiffOn_iff_target.mp hb).2 y
  simpa [extChartAt, chartAt, d] using hh.contDiffOn


abbrev Space := EuclideanSpace ℝ (Fin (Module.finrank ℝ E + Module.finrank ℝ G - Module.finrank ℝ F))

omit [CompleteSpace E] [CompleteSpace G] [FiniteDimensional ℝ F] in
theorem index_eq : Module.finrank ℝ (E × G) - Module.finrank ℝ F =
    Module.finrank ℝ E + Module.finrank ℝ G - Module.finrank ℝ F := by
  rw [Module.finrank_prod]

@[reducible] def normalizedAtlas : ChartedSpace (Space (E := E) (G := G) (F := F))
    {z : M × N // f z.1 = g z.2} :=
  castAtlas (index_eq (E := E) (G := G) (F := F)) (chartedSpace f g hf hg ht)

theorem normalized_chartAt (x : {z : M × N // f z.1 = g z.2}) :
    letI := normalizedAtlas f g hf hg ht
    chartAt (Space (E := E) (G := G) (F := F)) x =
      castChart (index_eq (E := E) (G := G) (F := F)) (selected f g hf hg ht x).chart :=
  cast_chartAt _ _ _

theorem normalized_atlas :
    letI := normalizedAtlas f g hf hg ht
    atlas (Space (E := E) (G := G) (F := F)) {z : M × N // f z.1 = g z.2} =
      castChart (index_eq (E := E) (G := G) (F := F)) ''
        Set.range (fun x => (selected f g hf hg ht x).chart) :=
  cast_atlas _ _

def Geometry (n : ℕ)
    (c : ChartedSpace (EuclideanSpace ℝ (Fin n)) {z : M × N // f z.1 = g z.2}) : Prop :=
  letI := c
  IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ {z : M × N // f z.1 = g z.2} ∧
    ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) (𝓘(ℝ,E).prod 𝓘(ℝ,G)) ∞
      (Subtype.val : {z : M × N // f z.1 = g z.2} → M × N)

theorem normalized_geometry :
    Geometry (E := E) (G := G) f g _ (normalizedAtlas f g hf hg ht) := by
  apply cast_property (index_eq (E := E) (G := G) (F := F)) (chartedSpace f g hf hg ht)
    (Geometry (E := E) (G := G) f g)
  refine ⟨isManifold f g hf hg ht, ?_⟩
  have h := smooth_inclusion f g hf hg ht
  rwa [modelWithCornersSelf_prod] at h

theorem normalized_isManifold :
    letI := normalizedAtlas f g hf hg ht
    IsManifold 𝓘(ℝ,Space (E := E) (G := G) (F := F)) ∞ {z : M × N // f z.1 = g z.2} :=
  (normalized_geometry f g hf hg ht).1

theorem normalized_smooth_inclusion :
    letI := normalizedAtlas f g hf hg ht
    ContMDiff 𝓘(ℝ,Space (E := E) (G := G) (F := F)) (𝓘(ℝ,E).prod 𝓘(ℝ,G)) ∞
      (Subtype.val : {z : M × N // f z.1 = g z.2} → M × N) :=
  (normalized_geometry f g hf hg ht).2

theorem normalized_chart_mem (x : {z : M × N // f z.1 = g z.2}) :
    letI := normalizedAtlas f g hf hg ht
    castChart (index_eq (E := E) (G := G) (F := F)) (selected f g hf hg ht x).chart ∈
      atlas (Space (E := E) (G := G) (F := F)) {z : M × N // f z.1 = g z.2} := by
  rw [normalized_atlas]
  exact ⟨_, ⟨x,rfl⟩, rfl⟩
end ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas

#print axioms ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.castAtlas
#print axioms ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.castChart
#print axioms ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.cast_chartAt
#print axioms ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.cast_atlas
#print axioms ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.cast_property
#print axioms ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.selected
#print axioms ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.selected_center
#print axioms ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.chartedSpace
#print axioms ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.chartAt_eq
#print axioms ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.atlas_eq
#print axioms ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.selected_mem_atlas
#print axioms ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.isManifold
#print axioms ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.exists_manifold
#print axioms ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.smooth_inclusion
#print axioms ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.index_eq
#print axioms ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.normalizedAtlas
#print axioms ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.normalized_chartAt
#print axioms ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.normalized_atlas
#print axioms ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.Geometry
#print axioms ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.normalized_geometry
#print axioms ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.normalized_isManifold
#print axioms ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.normalized_smooth_inclusion
#print axioms ConstructionTargets.ManifoldTargetIncidenceGlobalAtlas.normalized_chart_mem
