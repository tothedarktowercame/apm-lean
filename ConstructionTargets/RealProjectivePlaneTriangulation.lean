import ConstructionTargets.FiniteTriangulation

/-! # A finite marked triangulation of the real projective plane

This file isolates the concrete polygon-triangulation input from the compact-to-Hausdorff
topological upgrade.  The intended proof of `rp2_explicit_finite_model` uses the six-vertex
triangulation of `RP²` (ten triangles), realized by coordinate vertices.
-/

open Set

noncomputable section

namespace ConstructionTargets.RealProjectivePlaneTriangulation

open ConstructionTargets.FiniteTriangulation
open ConstructionTargets.StatementSurfaceModels

/-- The one-crosscap polygon quotient is Hausdorff.  Concretely, its generating relation
identifies a boundary point with its antipode and is a closed equivalence relation on the
compact disk. -/
theorem rp2_t2Space : T2Space RealProjectivePlane := by
  sorry

/-- A finite geometric simplicial complex has compact underlying space. -/
theorem finite_simplicialComplex_space_isCompact
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) : IsCompact K.space := by
  sorry

/-- **LIBRARY (explicit six-vertex model).** There is a finite coordinate realization of
the standard six-vertex, ten-triangle triangulation of `RP²`, together with a continuous
bijection to the disk quotient.  The distinguished vertex maps to the disk centre.

The combinatorial model has vertices `Fin 6`; its ten facets are the complementary pairs
in the standard minimal triangulation.  Realizing vertices by standard basis vectors makes
affine independence and the face-intersection axiom coordinate-support calculations. -/
theorem rp2_explicit_finite_model :
    ∃ (n : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
      (v : K.space) (f : K.space → RealProjectivePlane),
      K.faces.Finite ∧ {(v : EuclideanSpace ℝ (Fin n))} ∈ K.faces ∧
      Continuous f ∧ Function.Bijective f ∧
      f v = surfacePoint false 1 := by
  sorry

/-- Upgrade the explicit continuous bijection to a marked finite vertex triangulation. -/
theorem realProjectivePlane_hasFiniteVertexTriangulation :
    HasFiniteVertexTriangulation RealProjectivePlane (surfacePoint false 1) := by
  obtain ⟨n, K, v, f, hfin, hv, hfcont, hfbij, hmark⟩ :=
    rp2_explicit_finite_model
  letI : CompactSpace K.space :=
    isCompact_iff_compactSpace.mp (finite_simplicialComplex_space_isCompact K hfin)
  letI : T2Space RealProjectivePlane := rp2_t2Space
  let e' : K.space ≃ₜ RealProjectivePlane :=
    hfcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hfbij)
  let e : RealProjectivePlane ≃ₜ K.space := e'.symm
  refine ⟨n, K, e, (v : EuclideanSpace ℝ (Fin n)), hfin, hv, ?_⟩
  have heq : e (surfacePoint false 1) = v := by
    apply e'.injective
    simpa [e, e'] using hmark.symm
  exact congrArg Subtype.val heq

#print axioms realProjectivePlane_hasFiniteVertexTriangulation

end ConstructionTargets.RealProjectivePlaneTriangulation
