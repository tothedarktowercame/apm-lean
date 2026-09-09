import ConstructionTargets.RegularFiberFixedModelOverlaps
import Mathlib.Geometry.Manifold.IsManifold.Basic
open Set
open scoped ContDiff Manifold
noncomputable section
namespace ConstructionTargets.RegularFiberGlobalAtlas
open RegularFiberFixedModelOverlaps
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (f : E → F) (c : F) (hsm : ContDiff ℝ ∞ f)
  (hreg : ∀ x, f x = c → Function.Surjective (fderiv ℝ f x))

def selected : {x : E // f x = c} → FiberChart f c :=
  Classical.choose (exists_cover f c hsm hreg)

theorem selected_center (x : {x : E // f x = c}) :
    x ∈ (selected f c hsm hreg x).chart.source :=
  (Classical.choose_spec (exists_cover f c hsm hreg)).1 x

@[reducible] def chartedSpace : ChartedSpace (Model (E := E) (F := F)) {x : E // f x = c} where
  atlas := Set.range (fun x => (selected f c hsm hreg x).chart)
  chartAt x := (selected f c hsm hreg x).chart
  mem_chart_source := selected_center f c hsm hreg
  chart_mem_atlas x := ⟨x,rfl⟩

theorem chartAt_eq (x : {x : E // f x = c}) :
    letI := chartedSpace f c hsm hreg
    chartAt (Model (E := E) (F := F)) x = (selected f c hsm hreg x).chart := rfl

theorem atlas_eq :
    letI := chartedSpace f c hsm hreg
    atlas (Model (E := E) (F := F)) {x : E // f x = c} =
      Set.range (fun x => (selected f c hsm hreg x).chart) := rfl

theorem selected_mem_atlas (x : {x : E // f x = c}) :
    letI := chartedSpace f c hsm hreg
    (selected f c hsm hreg x).chart ∈ atlas (Model (E := E) (F := F)) {x : E // f x = c} :=
  ⟨x,rfl⟩

theorem isManifold :
    letI := chartedSpace f c hsm hreg
    IsManifold 𝓘(ℝ, Model (E := E) (F := F)) ∞ {x : E // f x = c} := by
  letI := chartedSpace f c hsm hreg
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨x,rfl⟩ := he
  obtain ⟨y,rfl⟩ := he'
  simpa using overlap_smooth f c (selected f c hsm hreg x) (selected f c hsm hreg y)

include hsm hreg in
theorem exists_manifold :
    ∃ charts : ChartedSpace (Model (E := E) (F := F)) {x : E // f x = c},
      letI := charts
      IsManifold 𝓘(ℝ, Model (E := E) (F := F)) ∞ {x : E // f x = c} :=
  ⟨chartedSpace f c hsm hreg,isManifold f c hsm hreg⟩

#print axioms selected_center
#print axioms chartAt_eq
#print axioms atlas_eq
#print axioms selected_mem_atlas
#print axioms isManifold
#print axioms exists_manifold
end ConstructionTargets.RegularFiberGlobalAtlas
