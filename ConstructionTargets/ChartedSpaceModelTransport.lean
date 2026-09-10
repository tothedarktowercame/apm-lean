import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.LinearAlgebra.Dimension.Constructions

open Set
open scoped Manifold
noncomputable section
namespace ConstructionTargets.ChartedSpaceModelTransport
variable {H K M : Type*} [TopologicalSpace H] [TopologicalSpace K]
  [TopologicalSpace M] [ChartedSpace H M]

def chart (e : H ≃ₜ K) (x : M) : OpenPartialHomeomorph M K :=
  (chartAt H x).trans e.toOpenPartialHomeomorph

@[reducible] def chartedSpace (e : H ≃ₜ K) : ChartedSpace K M where
  atlas := Set.range (chart e)
  chartAt := chart e
  mem_chart_source x := by simp [chart, mem_chart_source]
  chart_mem_atlas x := ⟨x, rfl⟩

theorem chartAt_eq (e : H ≃ₜ K) (x : M) :
    letI := chartedSpace (M := M) e
    chartAt K x = chart e x := rfl

theorem atlas_eq (e : H ≃ₜ K) :
    letI := chartedSpace (M := M) e
    atlas K M = Set.range (chart e) := rfl

theorem chart_source (e : H ≃ₜ K) (x : M) :
    (chart e x).source = (chartAt H x).source := by simp [chart]

theorem chart_target (e : H ≃ₜ K) (x : M) :
    (chart e x).target = e '' (chartAt H x).target := by
  ext y
  simp only [chart, OpenPartialHomeomorph.trans_target]
  change (y ∈ Set.univ ∧ e.symm y ∈ (chartAt H x).target) ↔ _
  constructor
  · intro h; exact ⟨e.symm y, h.2, e.apply_symm_apply y⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨Set.mem_univ _, by simpa using hz⟩

theorem chart_apply (e : H ≃ₜ K) (x y : M) :
    chart e x y = e (chartAt H x y) := rfl

theorem chart_symm_apply (e : H ≃ₜ K) (x : M) (y : K) :
    (chart e x).symm y = (chartAt H x).symm (e.symm y) := rfl

section Product
variable {E G N : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [TopologicalSpace N] [ChartedSpace E M] [ChartedSpace G N]

@[reducible] def productChartedSpace : ChartedSpace (WithLp 2 (E × G)) (M × N) :=
  letI : ChartedSpace (E × G) (M × N) := prodChartedSpace E M G N
  chartedSpace (WithLp.prodContinuousLinearEquiv 2 ℝ E G).symm.toHomeomorph

theorem product_dimension [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] :
    Module.finrank ℝ (WithLp 2 (E × G)) = Module.finrank ℝ E + Module.finrank ℝ G := by
  rw [(WithLp.prodContinuousLinearEquiv 2 ℝ E G).toLinearEquiv.finrank_eq]
  exact Module.finrank_prod
end Product
#print axioms chartedSpace
#print axioms chartAt_eq
#print axioms atlas_eq
#print axioms chart_source
#print axioms chart_target
#print axioms chart_apply
#print axioms chart_symm_apply
#print axioms productChartedSpace
#print axioms product_dimension
end ConstructionTargets.ChartedSpaceModelTransport
