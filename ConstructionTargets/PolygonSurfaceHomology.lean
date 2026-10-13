import Mathlib
import ConstructionTargets.PolygonSurfacePiOne

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

end

end ConstructionTargets.PolygonSurfaceHomology
