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

theorem wedge_isFinitePolyhedron_of_vertexTriangulations_aux_base_eq
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) :
    quotientMap x₀ y₀ (.inl x₀) = quotientMap x₀ y₀ (.inr y₀) := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ Rel.base

/-- (G1) Two finite complexes glued at one vertex each: translate the marked
vertices to the origin and place the complexes in the two factors of
`ℝ^(a+b)`.  The images meet only at the origin; the intersection axiom holds
because a vertex lying in the hull of a face is a vertex of that face. -/
-- BEGIN SEAT AREA
theorem wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed {a b : ℕ}
    (K₁ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)))
    (K₂ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin b)))
    (h₁ : K₁.faces.Finite) (h₂ : K₂.faces.Finite)
    (v₁ : EuclideanSpace ℝ (Fin a)) (v₂ : EuclideanSpace ℝ (Fin b))
    (hv₁ : {v₁} ∈ K₁.faces) (hv₂ : {v₂} ∈ K₂.faces) :
    ∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
      (ι₁ : C(K₁.space, K.space)) (ι₂ : C(K₂.space, K.space))
      (p : EuclideanSpace ℝ (Fin N)),
      K.faces.Finite ∧ {p} ∈ K.faces ∧
      Function.Injective ι₁ ∧ Function.Injective ι₂ ∧
      (∀ z : K.space, (∃ x, ι₁ x = z) ∨ (∃ y, ι₂ y = z)) ∧
      (∀ x y, ι₁ x = ι₂ y ↔
        ((x : EuclideanSpace ℝ (Fin a)) = v₁ ∧ (y : EuclideanSpace ℝ (Fin b)) = v₂)) ∧
      (∀ x : K₁.space, (x : EuclideanSpace ℝ (Fin a)) = v₁ →
        (ι₁ x : EuclideanSpace ℝ (Fin N)) = p) := by
  sorry
-- END SEAT AREA

/-- (G2) From (G1)'s embedding data and marked homeomorphisms `X ≃ₜ K₁.space`,
`Y ≃ₜ K₂.space`, the wedge is homeomorphic to `K.space` with the wedge point at
`p`: the map induced on the quotient by `Sum.elim (ι₁ ∘ e₁) (ι₂ ∘ e₂)` is a
continuous bijection from a compact space to a Hausdorff one. -/
theorem wedge_isFinitePolyhedron_of_vertexTriangulations_aux_homeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y) {a b N : ℕ}
    (K₁ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)))
    (K₂ : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin b)))
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
    (h₁ : K₁.faces.Finite) (h₂ : K₂.faces.Finite) (hK : K.faces.Finite)
    (e₁ : X ≃ₜ K₁.space) (e₂ : Y ≃ₜ K₂.space)
    (v₁ : EuclideanSpace ℝ (Fin a)) (v₂ : EuclideanSpace ℝ (Fin b))
    (he₁ : (e₁ x₀ : EuclideanSpace ℝ (Fin a)) = v₁)
    (he₂ : (e₂ y₀ : EuclideanSpace ℝ (Fin b)) = v₂)
    (ι₁ : C(K₁.space, K.space)) (ι₂ : C(K₂.space, K.space))
    (p : EuclideanSpace ℝ (Fin N))
    (hinj₁ : Function.Injective ι₁) (hinj₂ : Function.Injective ι₂)
    (hcov : ∀ z : K.space, (∃ x, ι₁ x = z) ∨ (∃ y, ι₂ y = z))
    (hmeet : ∀ x y, ι₁ x = ι₂ y ↔
      ((x : EuclideanSpace ℝ (Fin a)) = v₁ ∧ (y : EuclideanSpace ℝ (Fin b)) = v₂))
    (hp : ∀ x : K₁.space, (x : EuclideanSpace ℝ (Fin a)) = v₁ →
      (ι₁ x : EuclideanSpace ℝ (Fin N)) = p) :
    ∃ e : Wedge x₀ y₀ ≃ₜ K.space,
      (e (quotientMap x₀ y₀ (.inl x₀)) : EuclideanSpace ℝ (Fin N)) = p := by
  sorry

/-- **LIBRARY (simplicial point gluing).** Triangulations whose marked points
are vertices glue to a finite geometric triangulation of the point wedge. -/
theorem wedge_isFinitePolyhedron_of_vertexTriangulations
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y)
    (hX : HasFiniteVertexTriangulation X x₀)
    (hY : HasFiniteVertexTriangulation Y y₀) :
    HasFiniteVertexTriangulation (Wedge x₀ y₀) (quotientMap x₀ y₀ (.inl x₀)) := by
  obtain ⟨a, K₁, e₁, v₁, hK₁, hv₁, he₁⟩ := hX
  obtain ⟨b, K₂, e₂, v₂, hK₂, hv₂, he₂⟩ := hY
  obtain ⟨N, K, ι₁, ι₂, p, hK, hp, hinj₁, hinj₂, hcov, hmeet, hpv⟩ :=
    wedge_isFinitePolyhedron_of_vertexTriangulations_aux_embed K₁ K₂ hK₁ hK₂ v₁ v₂ hv₁ hv₂
  obtain ⟨e, he⟩ := wedge_isFinitePolyhedron_of_vertexTriangulations_aux_homeomorph
    x₀ y₀ K₁ K₂ K hK₁ hK₂ hK e₁ e₂ v₁ v₂ he₁ he₂ ι₁ ι₂ p hinj₁ hinj₂ hcov hmeet hpv
  exact ⟨N, K, e, p, hK, hp, he⟩

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
