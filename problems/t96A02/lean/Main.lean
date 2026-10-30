import Mathlib
import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.RationalLefschetz
import ConstructionTargets.LefschetzCompactPolyhedron
import ConstructionTargets.ProjectivePlaneWedgeRationalHomology
import ConstructionTargets.FiniteTriangulation
import ConstructionTargets.RealProjectivePlaneTriangulation
import ConstructionTargets.LefschetzFixedPoint

/-! # t96A02: fixed points on the wedge of two real projective planes -/

open ConstructionTargets.StatementSurfaceModels
open ConstructionTargets.RationalLefschetz
open ConstructionTargets.LefschetzCompactPolyhedron

noncomputable section

/-- **LIBRARY.** Every self-map of the wedge of two projective planes has
rational Lefschetz number one. -/
theorem t96A02_wedge_lefschetz_number :
    ∀ f : C(ProjectivePlaneWedge, ProjectivePlaneWedge),
      HasLefschetzNumber f 1 := by
  intro f
  open ConstructionTargets.ProjectivePlaneWedgeRationalHomology in
    letI : PathConnectedSpace
        ConstructionTargets.StatementSurfaceModels.RealProjectivePlane :=
      realProjectivePlane_pathConnected
    exact lefschetzNumber_one_of_rationallyPointlike
      projectivePlaneWedge_rationallyPointlike f

/-- **LIBRARY.** The polygon quotient and point wedge admit a common finite
triangulation. -/
theorem t96A02_projectivePlaneWedge_isFinitePolyhedron :
    IsFinitePolyhedron ProjectivePlaneWedge := by
  open ConstructionTargets.FiniteTriangulation in
    exact (wedge_isFinitePolyhedron_of_vertexTriangulations _ _
      ConstructionTargets.RealProjectivePlaneTriangulation.realProjectivePlane_hasFiniteVertexTriangulation
      ConstructionTargets.RealProjectivePlaneTriangulation.realProjectivePlane_hasFiniteVertexTriangulation).isFinitePolyhedron

/-- The Lefschetz fixed-point implication, specialized to the wedge of two
projective planes. Its homology calculation is supplied as a hypothesis so
this foundation can be developed in parallel with it. -/
theorem t96A02_wedge_fixed_point_of_lefschetz
    (hL : ∀ f : C(ProjectivePlaneWedge, ProjectivePlaneWedge),
      HasLefschetzNumber f 1) :
    ∀ f : C(ProjectivePlaneWedge, ProjectivePlaneWedge), ∃ x, f x = x := by
  intro f
  exact ConstructionTargets.LefschetzFixedPoint.fixedPointOfNonzeroLefschetz
    t96A02_projectivePlaneWedge_isFinitePolyhedron f (hL f) one_ne_zero

theorem apm_t96a02 :
    ∀ f : ContinuousMap ProjectivePlaneWedge ProjectivePlaneWedge, ∃ x, f x = x := by
  exact t96A02_wedge_fixed_point_of_lefschetz
    t96A02_wedge_lefschetz_number

#print axioms apm_t96a02
