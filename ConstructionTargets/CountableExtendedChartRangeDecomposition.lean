import ConstructionTargets.ChartCoordinateDimensionDropNullity
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Topology.Bases

/-! # Countable source patches subordinate to source and target charts -/

open Set Filter
open scoped Topology
noncomputable section

namespace ConstructionTargets.CountableExtendedChartRangeDecomposition

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ F H')
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [SecondCountableTopology M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]

/-- The patch centered at `x` lies in the source chart centered at `x` and
maps into the target chart centered at `f x`. -/
def chartPairPatch (f : M → N) (x : M) : Set M :=
  (extChartAt I x).source ∩ f ⁻¹' (extChartAt J (f x)).source

/-- For a continuous map, every chart-pair patch is a neighborhood of its
center. -/
theorem chartPairPatch_mem_nhds (f : M → N) (hf : Continuous f) (x : M) :
    chartPairPatch I J f x ∈ 𝓝 x := by
  exact inter_mem (extChartAt_source_mem_nhds x)
    (hf.tendsto x (extChartAt_source_mem_nhds (f x)))

/-- A second-countable manifold domain admits countably many chart-pair
patches covering it.  The associated image pieces have exactly the full range
as their union.  Target charts are deliberately allowed to vary with `x`. -/
theorem exists_countable_chartPairPatch_range_decomposition
    (f : M → N) (hf : Continuous f) :
    ∃ centers : Set M,
      centers.Countable ∧
      (⋃ x ∈ centers, chartPairPatch I J f x) = univ ∧
      range f = ⋃ x ∈ centers, f '' chartPairPatch I J f x := by
  obtain ⟨centers, hcount, hcover⟩ :=
    countable_cover_nhds (fun x ↦ chartPairPatch_mem_nhds I J f hf x)
  refine ⟨centers, hcount, hcover, ?_⟩
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    have hx : x ∈ ⋃ z ∈ centers, chartPairPatch I J f z := by
      rw [hcover]
      trivial
    obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hzc, hxz⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion_of_mem z
      (Set.mem_iUnion_of_mem hzc ⟨x, hxz, rfl⟩)
  · rintro y hy
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hy
    obtain ⟨_, hyx⟩ := Set.mem_iUnion.mp hx
    exact image_subset_range f _ hyx

/-- On its chart-pair patch, the literal target coordinate of `f y` is the
source-chart coordinate representative evaluated at the coordinate of `y`.
This records the exact equation needed by a subsequent local nullity theorem;
it does not extend the representative to the whole model space. -/
theorem chartPairPatch_coordinate_equation
    (f : M → N) (x y : M) (hy : y ∈ chartPairPatch I J f x) :
    extChartAt J (f x) (f y) =
      (extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm)
        (extChartAt I x y) := by
  simp only [Function.comp_apply]
  rw [(extChartAt I x).left_inv hy.1]

#print axioms chartPairPatch_mem_nhds
#print axioms exists_countable_chartPairPatch_range_decomposition
#print axioms chartPairPatch_coordinate_equation

end ConstructionTargets.CountableExtendedChartRangeDecomposition
