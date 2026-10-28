import Mathlib
import ConstructionTargets.LefschetzCompactPolyhedron
import ConstructionTargets.PointWedgeQuotient
import ConstructionTargets.StatementSurfaceModels

/-! # Finite triangulations and point wedges

Interfaces used by the three finite-polyhedron adapters in the Lefschetz
cluster.  A marked triangulation remembers that the distinguished point is a
vertex; this is the datum needed to glue triangulations across a point wedge.
-/

open Set

noncomputable section

namespace ConstructionTargets.FiniteTriangulation

open ConstructionTargets.LefschetzCompactPolyhedron
open ConstructionTargets.PointWedgeQuotient

/-- A finite geometric triangulation in which `x₀` is represented by a vertex. -/
def HasFiniteVertexTriangulation (X : Type) [TopologicalSpace X] (x₀ : X) : Prop :=
  ∃ (n : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
      (e : X ≃ₜ K.space) (v : EuclideanSpace ℝ (Fin n)),
    K.faces.Finite ∧ {v} ∈ K.faces ∧ (e x₀ : EuclideanSpace ℝ (Fin n)) = v

/-- Forgetting the marked vertex gives an ordinary finite triangulation. -/
theorem HasFiniteVertexTriangulation.isFinitePolyhedron
    {X : Type} [TopologicalSpace X] {x₀ : X}
    (h : HasFiniteVertexTriangulation X x₀) : IsFinitePolyhedron X := by
  obtain ⟨n, K, e, _v, hfinite, _hv, _hx⟩ := h
  exact ⟨n, K, hfinite, ⟨e⟩⟩

/-- **LIBRARY (stellar subdivision).** A chosen point of a finite polyhedron
can be made a vertex by a finite subdivision, without changing its topology. -/
theorem hasFiniteVertexTriangulation_of_isFinitePolyhedron
    {X : Type} [TopologicalSpace X] (x₀ : X)
    (hX : IsFinitePolyhedron X) : HasFiniteVertexTriangulation X x₀ := by
  sorry

/-- **LIBRARY (simplicial point gluing).** Triangulations whose marked points
are vertices glue to a finite geometric triangulation of the point wedge. -/
theorem wedge_isFinitePolyhedron_of_vertexTriangulations
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y)
    (hX : HasFiniteVertexTriangulation X x₀)
    (hY : HasFiniteVertexTriangulation Y y₀) :
    HasFiniteVertexTriangulation (Wedge x₀ y₀) (quotientMap x₀ y₀ (.inl x₀)) := by
  sorry

/-- Finite polyhedra are closed under point wedges. -/
theorem wedge_isFinitePolyhedron
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) (hX : IsFinitePolyhedron X)
    (hY : IsFinitePolyhedron Y) : IsFinitePolyhedron (Wedge x₀ y₀) := by
  exact (wedge_isFinitePolyhedron_of_vertexTriangulations x₀ y₀
    (hasFiniteVertexTriangulation_of_isFinitePolyhedron x₀ hX)
    (hasFiniteVertexTriangulation_of_isFinitePolyhedron y₀ hY)).isFinitePolyhedron

/-- SUPERSEDED (claude-14, 2026-10-28): consumers use
`RealProjectivePlaneTriangulation.realProjectivePlane_hasFiniteVertexTriangulation`
(that module imports this one); not queued.
**LIBRARY (concrete `RP²` triangulation).** The subdivided polygon model
has a finite triangulation in which the disk centre is a vertex. -/
theorem realProjectivePlane_hasFiniteVertexTriangulation :
    HasFiniteVertexTriangulation
      ConstructionTargets.StatementSurfaceModels.RealProjectivePlane
      (ConstructionTargets.StatementSurfaceModels.surfacePoint false 1) := by
  sorry

end ConstructionTargets.FiniteTriangulation
