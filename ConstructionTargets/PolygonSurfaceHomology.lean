import Mathlib
import ConstructionTargets.PolygonSurfacePiOne
import ConstructionTargets.PolygonOverlapHomotopyEquivCircle
import ConstructionTargets.SingularHomologyConcrete
import ConstructionTargets.IntegralSingularHomologyComparison
import ConstructionTargets.CircleHomology

/-!
# Homology of one-vertex polygon quotients

This file begins the singular-homology calculation described in
`PolygonSurfaceHomology.blueprint.md`.  The first layer fixes the integral
homology notation and the coordinates of the cellular-looking boundary map
that the later radial Mayer--Vietoris argument identifies with its singular
homology boundary morphism.
-/

namespace ConstructionTargets.PolygonSurfaceHomology

open ConstructionTargets.PolygonSurfacePiOne
open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap

noncomputable section

/-- Integral singular homology of the quotient surface carried by `P`. -/
abbrev H (P : PairingData) (k : ℕ) : ModuleCat ℤ :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of P.Space))

/-- The signed contribution made by one oriented polygon edge to its orbit
circle.  This is the degree convention used by `PairingData.signedWedgeArc`:
`true` traverses `circleArc`, while `false` traverses its reversal. -/
def edgeAttachingDegree (P : PairingData) (i : Fin P.edgeCount) : ℤ :=
  if P.sign i then 1 else -1

@[simp] theorem edgeAttachingDegree_of_sign_true (P : PairingData)
    (i : Fin P.edgeCount) (h : P.sign i = true) :
    edgeAttachingDegree P i = 1 := by
  simp [edgeAttachingDegree, h]

@[simp] theorem edgeAttachingDegree_of_sign_false (P : PairingData)
    (i : Fin P.edgeCount) (h : P.sign i = false) :
    edgeAttachingDegree P i = -1 := by
  simp [edgeAttachingDegree, h]

/-- The abelianized attaching word in the edge-orbit basis.  The formula is
representative-free: it sums over all polygon edge indices and merely tests
which quotient orbit each edge belongs to. -/
def edgeOrbitContribution (P : PairingData) (i : Fin P.edgeCount)
    (l : PairingOrbit P.pair) : ℤ := by
  classical
  exact if P.orbit i = l then edgeAttachingDegree P i else 0

@[simp] theorem edgeOrbitContribution_of_mem (P : PairingData)
    (i : Fin P.edgeCount) (l : PairingOrbit P.pair) (h : P.orbit i = l) :
    edgeOrbitContribution P i l = edgeAttachingDegree P i := by
  classical
  simp [edgeOrbitContribution, h]

@[simp] theorem edgeOrbitContribution_of_not_mem (P : PairingData)
    (i : Fin P.edgeCount) (l : PairingOrbit P.pair) (h : P.orbit i ≠ l) :
    edgeOrbitContribution P i l = 0 := by
  classical
  simp [edgeOrbitContribution, h]

def attachingDegree (P : PairingData) : PairingOrbit P.pair → ℤ :=
  fun l => ∑ i : Fin P.edgeCount, edgeOrbitContribution P i l

@[simp] theorem attachingDegree_apply (P : PairingData)
    (l : PairingOrbit P.pair) :
    attachingDegree P l = ∑ i : Fin P.edgeCount,
      edgeOrbitContribution P i l := rfl

/-- The degree-two boundary map in the orbit-circle coordinates. -/
def attachingBoundary (P : PairingData) :
    ℤ →ₗ[ℤ] (PairingOrbit P.pair → ℤ) where
  toFun n := n • attachingDegree P
  map_add' m n := by
    simp only [add_smul]
  map_smul' m n := by
    ext l
    simp [mul_assoc]

@[simp] theorem attachingBoundary_apply (P : PairingData) (n : ℤ) :
    attachingBoundary P n = n • attachingDegree P := rfl

@[simp] theorem attachingBoundary_apply_apply (P : PairingData) (n : ℤ)
    (l : PairingOrbit P.pair) :
    attachingBoundary P n l = n * attachingDegree P l := by
  rfl

/-- The degree-two model produced by the radial Mayer--Vietoris sequence. -/
abbrev BoundaryKernel (P : PairingData) :=
  LinearMap.ker (attachingBoundary P)

/-- The degree-one model produced by the radial Mayer--Vietoris sequence. -/
abbrev BoundaryCokernel (P : PairingData) :=
  (PairingOrbit P.pair → ℤ) ⧸ LinearMap.range (attachingBoundary P)

/-! ## The inner piece and annular overlap -/

/-- Integral singular homology of an arbitrary topological space. -/
abbrev SpaceH (X : Type) [TopologicalSpace X] (k : ℕ) : ModuleCat ℤ :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

/-- The inner member of the radial open cover, with its subtype topology. -/
abbrev InnerPiece (P : PairingData) :=
  {q // q ∈ (openCover P).inner}

/-- The annular intersection of the radial open cover. -/
abbrev OverlapPiece (P : PairingData) :=
  ConstructionTargets.PolygonRadialOpenCover.overlapOpen P.Rel

/-- The pointed contraction supplied by the radial cover, expressed as a
homotopy equivalence with a point. -/
def innerHomotopyEquivPoint (P : PairingData) : InnerPiece P ≃ₕ Unit where
  toFun := ContinuousMap.const (InnerPiece P) ()
  invFun := ContinuousMap.const Unit (openCover P).center
  left_inv := ⟨(openCover P).contraction.homotopy.symm⟩
  right_inv := by
    rw [show (ContinuousMap.const (InnerPiece P) ()).comp
        (ContinuousMap.const Unit (openCover P).center) =
        ContinuousMap.id Unit by
      apply ContinuousMap.ext
      intro u
      exact Subsingleton.elim _ _]

/-- The overlap-to-circle orientation of the explicit annular radial
homotopy equivalence. -/
def overlapHomotopyEquivCircle (P : PairingData) : OverlapPiece P ≃ₕ Circle :=
  (ConstructionTargets.PolygonOverlapHomotopyEquivCircle.overlapHomotopyEquivCircle
    P.Rel (fun {_ _} h => pairingRel_radius P h)
      (fun {_ _} h => pairingRel_boundary P h)).symm

/-- The inner radial piece has integral zeroth homology `ℤ`. -/
noncomputable def innerH0IsoInt (P : PairingData) :
    SpaceH (InnerPiece P) 0 ≅ ModuleCat.of ℤ ℤ :=
  ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsoOfGroupIso
    (TopCat.of (InnerPiece P)) 0 (ModuleCat.of ℤ ℤ)
      (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
        (innerHomotopyEquivPoint P) 0 ≪≫
          ConstructionTargets.SingularHomologyConcrete.pointH0IsoInt)

/-- The inner radial piece has no positive-degree integral homology. -/
theorem innerHigherHomology_isZero (P : PairingData) (k : ℕ) (hk : k ≠ 0) :
    IsZero (SpaceH (InnerPiece P) k) := by
  apply ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsZeroOfGroupIsZero
  exact (ConstructionTargets.SingularHomologyConcrete.pointHigherHomology_isZero k hk).of_iso
    (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
      (innerHomotopyEquivPoint P) k)

/-- Additive-group coordinates for zeroth homology of the positive circle. -/
noncomputable def circleGroupH0IsoInt :
    ConstructionTargets.SingularHomologyConcrete.SingularHomology 0 (TopCat.of Circle) ≅
      AddCommGrpCat.of ℤ :=
  ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
      ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.toHomotopyEquiv 0 ≪≫
    ConstructionTargets.SphereHomology.sphereH0IsoInt 1 one_pos

/-- Additive-group coordinates for first homology of the positive circle. -/
noncomputable def circleGroupH1IsoInt :
    ConstructionTargets.SingularHomologyConcrete.SingularHomology 1 (TopCat.of Circle) ≅
      AddCommGrpCat.of ℤ :=
  ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
      ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.toHomotopyEquiv 1 ≪≫
    ConstructionTargets.SphereHomology.sphereTopHomologyIsoInt 1 one_pos

/-- The annular overlap has integral zeroth homology `ℤ`. -/
noncomputable def overlapH0IsoInt (P : PairingData) :
    SpaceH (OverlapPiece P) 0 ≅ ModuleCat.of ℤ ℤ :=
  ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsoOfGroupIso
    (TopCat.of (OverlapPiece P)) 0 (ModuleCat.of ℤ ℤ)
      (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
        (overlapHomotopyEquivCircle P) 0 ≪≫ circleGroupH0IsoInt)

/-- The annular overlap has integral first homology `ℤ`, in the coordinate
transported from the positive radial circle. -/
noncomputable def overlapH1IsoInt (P : PairingData) :
    SpaceH (OverlapPiece P) 1 ≅ ModuleCat.of ℤ ℤ :=
  ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsoOfGroupIso
    (TopCat.of (OverlapPiece P)) 1 (ModuleCat.of ℤ ℤ)
      (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
        (overlapHomotopyEquivCircle P) 1 ≪≫ circleGroupH1IsoInt)

/-- The annular overlap has no integral homology above degree one. -/
theorem overlapHigherHomology_isZero (P : PairingData) (k : ℕ) (hk : 1 < k) :
    IsZero (SpaceH (OverlapPiece P) k) := by
  apply ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsZeroOfGroupIsZero
  exact (ConstructionTargets.SphereHomology.sphereHomology_isZero_of_gt 1 k hk).of_iso
    ((ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
      (overlapHomotopyEquivCircle P) k).trans
        (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
          ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.toHomotopyEquiv k))

/-- B5: the complete homology table needed from the inner radial piece and
its annular overlap.  The overlap coordinates are induced by the explicit
positive radial-circle equivalence above. -/
theorem innerOverlapHomology (P : PairingData) :
    Nonempty (SpaceH (InnerPiece P) 0 ≅ ModuleCat.of ℤ ℤ) ∧
    (∀ k : ℕ, k ≠ 0 → IsZero (SpaceH (InnerPiece P) k)) ∧
    Nonempty (SpaceH (OverlapPiece P) 0 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (SpaceH (OverlapPiece P) 1 ≅ ModuleCat.of ℤ ℤ) ∧
    (∀ k : ℕ, 1 < k → IsZero (SpaceH (OverlapPiece P) k)) := by
  exact ⟨⟨innerH0IsoInt P⟩, innerHigherHomology_isZero P,
    ⟨overlapH0IsoInt P⟩, ⟨overlapH1IsoInt P⟩,
      overlapHigherHomology_isZero P⟩

end

end ConstructionTargets.PolygonSurfaceHomology
