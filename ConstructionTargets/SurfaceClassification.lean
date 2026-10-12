import ConstructionTargets.SurfaceNestedTriangleCover

noncomputable section
open Set Topology

namespace ConstructionTargets.SurfaceClassification

open StandardTriangleEmbedding ScaledTriangleNeighborhood
open CompactSurfaceTriangleCover SurfaceNestedTriangleCover

abbrev EuclideanPlane := EuclideanSpace ℝ (Fin 2)

theorem compactSurfaceFiniteNestedTriangleCover
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanPlane M] [CompactSpace M] :
    let hd : Module.finrank ℝ EuclideanPlane = 2 := by simp [EuclideanPlane]
    ∃ (s : Finset M) (r : M → ℝ),
      (∀ x ∈ s,
        Good (planeChart hd x) x (r x) ∧
        Good (planeChart hd x) x (r x / 2) ∧
        Set.range (triangle (planeChart hd x) x (r x / 2)) ⊆
          triangle (planeChart hd x) x (r x) '' interiorParameters ∧
        Set.range ((planeEquiv hd).symm ∘ scaled (planeChart hd x x) (r x)) ⊆
          (chartAt EuclideanPlane x).target) ∧
      (∀ y : M, ∃ x ∈ s,
        y ∈ triangle (planeChart hd x) x (r x / 2) '' interiorParameters) := by
  dsimp only
  exact finite_nested (E := EuclideanPlane) (M := M) (by simp [EuclideanPlane])

end ConstructionTargets.SurfaceClassification
