import ConstructionTargets.ManifoldTargetRegularFiberCharts
import Mathlib.Geometry.Manifold.IsManifold.Basic
open Set
open scoped ContDiff Manifold
noncomputable section
namespace ConstructionTargets.ManifoldTargetRegularFiberGlobalAtlas
open ManifoldTargetRegularFiberCharts
variable {E F M N : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
  (f : M → N) (c : N) (hsm : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
  (hreg : ∀ x, f x = c → Function.Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x))

def selected : {x : M // f x = c} → FiberChart (E := E) (F := F) f c :=
  Classical.choose (exists_cover f c hsm hreg)

theorem selected_center (x : {x : M // f x = c}) :
    x ∈ (selected f c hsm hreg x).chart.source :=
  (Classical.choose_spec (exists_cover f c hsm hreg)).1 x

@[reducible] def chartedSpace : ChartedSpace (Model (E := E) (F := F)) {x : M // f x = c} where
  atlas := Set.range (fun x => (selected f c hsm hreg x).chart)
  chartAt x := (selected f c hsm hreg x).chart
  mem_chart_source := selected_center f c hsm hreg
  chart_mem_atlas x := ⟨x,rfl⟩

theorem chartAt_eq (x : {x : M // f x = c}) :
    letI := chartedSpace f c hsm hreg
    chartAt (Model (E := E) (F := F)) x = (selected f c hsm hreg x).chart := rfl

theorem atlas_eq :
    letI := chartedSpace f c hsm hreg
    atlas (Model (E := E) (F := F)) {x : M // f x = c} =
      Set.range (fun x => (selected f c hsm hreg x).chart) := rfl

theorem selected_mem_atlas (x : {x : M // f x = c}) :
    letI := chartedSpace f c hsm hreg
    (selected f c hsm hreg x).chart ∈ atlas (Model (E := E) (F := F)) {x : M // f x = c} :=
  ⟨x,rfl⟩

theorem isManifold :
    letI := chartedSpace f c hsm hreg
    IsManifold 𝓘(ℝ, Model (E := E) (F := F)) ∞ {x : M // f x = c} := by
  letI := chartedSpace f c hsm hreg
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨x,rfl⟩ := he
  obtain ⟨y,rfl⟩ := he'
  simpa using overlap_smooth f c (selected f c hsm hreg x) (selected f c hsm hreg y)

include hsm hreg in
theorem exists_manifold :
    ∃ charts : ChartedSpace (Model (E := E) (F := F)) {x : M // f x = c},
      letI := charts
      IsManifold 𝓘(ℝ, Model (E := E) (F := F)) ∞ {x : M // f x = c} :=
  ⟨chartedSpace f c hsm hreg,isManifold f c hsm hreg⟩

theorem smooth_inclusion :
    letI := chartedSpace f c hsm hreg
    ContMDiff 𝓘(ℝ, Model (E := E) (F := F)) 𝓘(ℝ,E) ∞
      (Subtype.val : {x : M // f x = c} → M) := by
  letI := chartedSpace f c hsm hreg
  letI := isManifold f c hsm hreg
  apply contMDiff_iff.mpr
  refine ⟨continuous_subtype_val, ?_⟩
  intro x y
  let d := selected f c hsm hreg x
  have hb : ContMDiffOn 𝓘(ℝ,Model (E := E) (F := F)) 𝓘(ℝ,E) ∞
      (fun z => (d.chart.symm z).val) d.chart.target :=
    d.backward_smooth.congr (fun z hz => d.backward_eq z hz)
  have hh := (contMDiffOn_iff_target.mp hb).2 y
  simpa [extChartAt, chartAt, d] using hh.contDiffOn
#print axioms smooth_inclusion
#print axioms selected_center
#print axioms chartAt_eq
#print axioms atlas_eq
#print axioms selected_mem_atlas
#print axioms isManifold
#print axioms exists_manifold
end ConstructionTargets.ManifoldTargetRegularFiberGlobalAtlas
