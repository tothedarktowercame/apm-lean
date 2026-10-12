import ConstructionTargets.SurfaceNestedTriangleCover

noncomputable section
open Set Topology

namespace ConstructionTargets.SurfaceClassification

open StandardTriangleEmbedding ScaledTriangleNeighborhood
open CompactSurfaceTriangleCover SurfaceNestedTriangleCover

abbrev EuclideanPlane := EuclideanSpace ℝ (Fin 2)

/-- A finite semisimplicial complex truncated in dimensions zero through two.
The compatibility field records the two vertices of each boundary edge of a
face; injectivity excludes degenerate triangular faces. -/
structure FiniteTwoComplex where
  vertex : Type
  edge : Type
  face : Type
  vertex_finite : Finite vertex
  edge_finite : Finite edge
  face_finite : Finite face
  edgeVertex : edge → Fin 2 → vertex
  faceEdge : face → Fin 3 → edge
  faceVertex : face → Fin 3 → vertex
  face_compat : ∀ f i j, edgeVertex (faceEdge f i) j =
    faceVertex f (Fin.succAbove i j)
  face_vertices_injective : ∀ f, Function.Injective (faceVertex f)

namespace FiniteTwoComplex

instance (K : FiniteTwoComplex) : Finite K.vertex := K.vertex_finite
instance (K : FiniteTwoComplex) : Finite K.edge := K.edge_finite
instance (K : FiniteTwoComplex) : Finite K.face := K.face_finite

/-- The set of boundary edges named by a two-face. -/
def boundaryEdges (K : FiniteTwoComplex) (f : K.face) : Finset K.edge := by
  classical
  exact Finset.univ.image (K.faceEdge f)

/-- The finite-combinatorics interface asserting the triangular face bound. -/
def FaceBound (K : FiniteTwoComplex) : Prop :=
  ∀ f : K.face, (K.boundaryEdges f).card ≤ 3

/-- Every face of a `FiniteTwoComplex` has at most three boundary edges. -/
theorem face_card_le_three (K : FiniteTwoComplex) : K.FaceBound := by
  intro f
  classical
  unfold boundaryEdges
  simpa using (Finset.card_image_le (s := Finset.univ) (f := K.faceEdge f))

end FiniteTwoComplex

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
