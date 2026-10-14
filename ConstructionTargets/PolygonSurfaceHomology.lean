import Mathlib
import ConstructionTargets.PolygonSurfacePiOne
import ConstructionTargets.PolygonOverlapHomotopyEquivCircle
import ConstructionTargets.SingularHomologyConcrete
import ConstructionTargets.IntegralSingularHomologyComparison
import ConstructionTargets.CircleHomology
import ConstructionTargets.T02A06SphereH0
import ConstructionTargets.CoefficientSigmaConstFinsuppComparison
import ConstructionTargets.SingularHomologyHomotopy
import ConstructionTargets.DegreeOneHurewiczSurjective
import ConstructionTargets.CircleHurewiczIsomorphism
import ConstructionTargets.PointWedgeVanKampen

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

/-! ## The outer piece and its signed orbit-circle wedge -/

/-- The outer member of the radial cover. -/
abbrev OuterPiece (P : PairingData) :=
  ConstructionTargets.PolygonRadialOpenCover.outerOpen P.Rel

/-- The boundary skeleton, regarded as a subspace of the outer member. -/
abbrev OuterBoundaryPiece (P : PairingData) :=
  {z : OuterPiece P // z ∈ P.outerBoundarySkeleton}

/-- The strong deformation retract already constructed for the punctured
polygon gives a homotopy equivalence from the outer piece to its boundary
skeleton. -/
def outerHomotopyEquivBoundary (P : PairingData) :
    OuterPiece P ≃ₕ OuterBoundaryPiece P where
  toFun :=
    { toFun := fun z =>
        ⟨(punctureDeformationRetract P).homotopy (1, z),
          (punctureDeformationRetract P).one_mem z⟩
      continuous_toFun := by
        fun_prop }
  invFun :=
    { toFun := fun z => z.1
      continuous_toFun := continuous_subtype_val }
  left_inv := by
    let D := punctureDeformationRetract P
    let H :
        ContinuousMap.Homotopy (ContinuousMap.id (OuterPiece P))
          ((ContinuousMap.mk (fun z : OuterBoundaryPiece P => z.1)
              continuous_subtype_val).comp
            (ContinuousMap.mk (fun z : OuterPiece P =>
              ⟨D.homotopy (1, z), D.one_mem z⟩) (by fun_prop))) :=
      { toFun := fun p => D.homotopy p
        continuous_toFun := D.homotopy.continuous
        map_zero_left := D.zero
        map_one_left := by intro z; rfl }
    exact ⟨H.symm⟩
  right_inv := by
    have hmap :
        (ContinuousMap.mk
            (fun z : OuterPiece P =>
              ⟨(punctureDeformationRetract P).homotopy (1, z),
                (punctureDeformationRetract P).one_mem z⟩)
            (by fun_prop)).comp
          (ContinuousMap.mk (fun z : OuterBoundaryPiece P => z.1)
            continuous_subtype_val) =
          ContinuousMap.id (OuterBoundaryPiece P) := by
      apply ContinuousMap.ext
      intro z
      apply Subtype.ext
      exact (punctureDeformationRetract P).fixed 1 z.1 z.2
    rw [hmap]

/-- A point of the quotient boundary skeleton lies in the radial outer
piece. -/
theorem skeleton_mem_outer (P : PairingData) (z : P.skeleton) :
    z.1 ∈ ConstructionTargets.PolygonRadialOpenCover.outerOpen P.Rel := by
  rcases z.2 with ⟨x, hx, hxz⟩
  refine ⟨x, ?_, hxz⟩
  change (1 : ℝ) / 4 < ConstructionTargets.PolygonRadialOpenCover.radius x
  change ‖(x : ℂ)‖ = 1 at hx
  rw [ConstructionTargets.PolygonRadialOpenCover.radius, hx]
  norm_num

/-- Forgetting the redundant outer-membership proof identifies the boundary
subspace of the outer piece with the boundary skeleton in the surface. -/
def outerBoundaryHomeomorphSkeleton (P : PairingData) :
    OuterBoundaryPiece P ≃ₜ P.skeleton where
  toFun z := ⟨z.1.1, (mem_outerBoundarySkeleton_iff P z.1).mp z.2⟩
  invFun z :=
    ⟨⟨z.1, skeleton_mem_outer P z⟩,
      (mem_outerBoundarySkeleton_iff P ⟨z.1, skeleton_mem_outer P z⟩).mpr z.2⟩
  left_inv z := by ext; rfl
  right_inv z := by ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The actual radial outer piece has the homotopy type of the finite wedge
indexed by paired-edge orbits.  The final homeomorphism is the signed one, so
its restriction to every polygon edge is `PairingData.signedWedgeArc`. -/
noncomputable def outerHomotopyEquivWedge (P : PairingData) :
    OuterPiece P ≃ₕ
      PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (PairingOrbit P.pair) :=
  (outerHomotopyEquivBoundary P).trans
    (outerBoundaryHomeomorphSkeleton P).toHomotopyEquiv |>.trans
      P.skeletonHomeomorphWedge.toHomotopyEquiv

/-- Include the surface boundary skeleton into the radial outer piece. -/
def skeletonToOuter (P : PairingData) (z : P.skeleton) : OuterPiece P :=
  ⟨z.1, skeleton_mem_outer P z⟩

/-- On the boundary skeleton, the outer-piece equivalence is exactly the
previously fixed signed skeleton-to-wedge homeomorphism. -/
theorem outerHomotopyEquivWedge_skeleton (P : PairingData) (z : P.skeleton) :
    outerHomotopyEquivWedge P (skeletonToOuter P z) =
      P.skeletonHomeomorphWedge z := by
  change P.skeletonHomeomorphWedge
    ((outerBoundaryHomeomorphSkeleton P)
      ((outerHomotopyEquivBoundary P) (skeletonToOuter P z))) = _
  congr 1
  apply Subtype.ext
  exact congrArg (fun w : OuterPiece P => w.1)
    ((punctureDeformationRetract P).fixed 1 (skeletonToOuter P z)
      ((mem_outerBoundarySkeleton_iff P (skeletonToOuter P z)).mpr z.2))

/-! ### Degree zero of a finite circle wedge -/

/-- Every nonempty indexed wedge of circles is path connected.  The proof
joins each representative to the common wedge point inside its own circle
leg, so it does not choose an ordering of the index type. -/
noncomputable instance finiteWedgePathConnectedSpace
    (L : Type) [Nonempty L] :
    PathConnectedSpace
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge L) := by
  letI : PathConnectedSpace Circle :=
    pathConnectedSpace_iff_univ.mpr (by
      have h : IsPathConnected
          (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
            (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
        ConstructionTargets.CircleHomology.circleHomeomorphSphereOne
          |>.isPathConnected_preimage.mpr isPathConnected_univ
      simpa using h)
  rw [pathConnectedSpace_iff_univ]
  let l₀ : L := Classical.choice (inferInstance : Nonempty L)
  refine ⟨PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l₀ 1,
    Set.mem_univ _, ?_⟩
  intro y _
  refine Quotient.inductionOn y ?_
  rintro ⟨k, w⟩
  have hy : Joined
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle k w)
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle k (1 : Circle)) :=
    ⟨(PathConnectedSpace.joined w 1).somePath.map
      (PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle k)⟩
  rw [PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle_base_eq k l₀] at hy
  exact joinedIn_univ.mpr hy.symm

/-- A canonical wedge point for the orbit-indexed wedge of a pairing datum,
using the positive edge-count witness rather than a chosen orbit
representative. -/
def orbitWedgeBase (P : PairingData) :
    PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (PairingOrbit P.pair) :=
  PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
    (P.orbit ⟨0, P.edgeCount_pos⟩) 1

/-- Additive-group degree-zero homology of the orbit-indexed wedge. -/
noncomputable def finiteWedgeGroupH0IsoInt (P : PairingData) :
    ConstructionTargets.SingularHomologyConcrete.SingularHomology 0
      (TopCat.of
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
          (PairingOrbit P.pair))) ≅ AddCommGrpCat.of ℤ := by
  letI : Nonempty (PairingOrbit P.pair) := ⟨P.orbit ⟨0, P.edgeCount_pos⟩⟩
  letI : Epi (ConstructionTargets.T02A06SphereH0.singularVertexH0Class
      (orbitWedgeBase P)) :=
    ConstructionTargets.T02A06SphereH0.singularVertexH0Class_epi _
  letI : Mono (ConstructionTargets.T02A06SphereH0.singularVertexH0Class
      (orbitWedgeBase P)) :=
    ConstructionTargets.T02A06SphereH0.singularVertexH0Class_mono _
  letI : IsIso (ConstructionTargets.T02A06SphereH0.singularVertexH0Class
      (orbitWedgeBase P)) := isIso_of_mono_of_epi _
  exact (asIso (ConstructionTargets.T02A06SphereH0.singularVertexH0Class
    (orbitWedgeBase P))).symm

/-- Module-category degree-zero homology of the orbit-indexed wedge. -/
noncomputable def finiteWedgeH0IsoInt (P : PairingData) :
    SpaceH
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (PairingOrbit P.pair)) 0
        ≅ ModuleCat.of ℤ ℤ :=
  ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsoOfGroupIso
    (TopCat.of
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (PairingOrbit P.pair)))
    0 (ModuleCat.of ℤ ℤ) (finiteWedgeGroupH0IsoInt P)

/-- The radial outer piece has integral zeroth homology `ℤ`. -/
noncomputable def outerH0IsoInt (P : PairingData) :
    SpaceH (OuterPiece P) 0 ≅ ModuleCat.of ℤ ℤ :=
  ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsoOfGroupIso
    (TopCat.of (OuterPiece P)) 0 (ModuleCat.of ℤ ℤ)
      (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
        (outerHomotopyEquivWedge P) 0 ≪≫ finiteWedgeGroupH0IsoInt P)

/-! ### The degree-one coordinate presentation -/

/-- The map on first homology induced by inclusion of one circle leg in the
finite wedge. -/
noncomputable def finiteWedgeLegH1 {L : Type} (l : L) :
    SpaceH Circle 1 ⟶
      SpaceH (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge L) 1 :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom ⟨PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l,
        PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle l⟩)

/-- The coproduct of one integral generator for every wedge circle maps to
the corresponding positive circle class in wedge homology. -/
noncomputable def finiteWedgeH1Presentation (L : Type) :
    (∐ fun _ : L => ModuleCat.of ℤ ℤ) ⟶
      SpaceH (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge L) 1 :=
  Sigma.desc fun l =>
    ConstructionTargets.CircleHomology.circleH1IsoInt.inv ≫ finiteWedgeLegH1 l

@[simp, reassoc]
theorem sigma_ι_finiteWedgeH1Presentation (L : Type) (l : L) :
    Sigma.ι (fun _ : L => ModuleCat.of ℤ ℤ) l ≫
      finiteWedgeH1Presentation L =
        ConstructionTargets.CircleHomology.circleH1IsoInt.inv ≫
          finiteWedgeLegH1 l := by
  rw [finiteWedgeH1Presentation, Sigma.ι_desc]

/-- For a finite index type, the coproduct source is the requested function
module, with its standard basis orientation. -/
noncomputable def finiteWedgeH1SourceIso (L : Type) [Fintype L]
    [DecidableEq L] :
    (∐ fun _ : L => ModuleCat.of ℤ ℤ) ≅ ModuleCat.of ℤ (L → ℤ) :=
  ModuleCat.coprodIsoDirectSum (fun _ : L => ModuleCat.of ℤ ℤ) ≪≫
    (DirectSum.linearEquivFunOnFintype ℤ L (fun _ => ℤ)).toModuleIso

@[simp]
theorem sigma_ι_finiteWedgeH1SourceIso_hom_apply
    (L : Type) [Fintype L] [DecidableEq L] (l : L) (n : ℤ) :
    (Sigma.ι (fun _ : L => ModuleCat.of ℤ ℤ) l ≫
      (finiteWedgeH1SourceIso L).hom) n = Pi.single l n := by
  classical
  change ((Sigma.ι (fun _ : L => ModuleCat.of ℤ ℤ) l ≫
      (ModuleCat.coprodIsoDirectSum (fun _ : L => ModuleCat.of ℤ ℤ)).hom ≫
      (DirectSum.linearEquivFunOnFintype ℤ L (fun _ => ℤ)).toModuleIso.hom) n) = _
  rw [← Category.assoc, ModuleCat.ι_coprodIsoDirectSum_hom]
  exact DirectSum.linearEquivFunOnFintype_lof (M := fun _ : L => ℤ) ℤ l n

/-- The edge-orbit quotient is finite because every orbit is represented by
one of the finitely many polygon edges. -/
noncomputable instance pairingOrbitFinite (P : PairingData) :
    Finite (PairingOrbit P.pair) :=
  Finite.of_surjective P.orbit Quotient.mk_surjective

noncomputable instance pairingOrbitFintype (P : PairingData) :
    Fintype (PairingOrbit P.pair) := Fintype.ofFinite _

noncomputable instance pairingOrbitDecidableEq (P : PairingData) :
    DecidableEq (PairingOrbit P.pair) := Classical.decEq _

/-- A standard basis vector in the finite orbit-coordinate module. -/
noncomputable def orbitBasis (P : PairingData)
    (l : PairingOrbit P.pair) (n : ℤ) : PairingOrbit P.pair → ℤ := by
  classical
  exact Pi.single l n

/-- The orbit-coordinate map into first homology of the finite wedge.  The
next B4 step proves this explicitly normalized map is an isomorphism. -/
noncomputable def finiteWedgeH1CoordinateMap (P : PairingData) :
    ModuleCat.of ℤ (PairingOrbit P.pair → ℤ) ⟶
      SpaceH
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
          (PairingOrbit P.pair)) 1 := by
  letI : Fintype (PairingOrbit P.pair) := Fintype.ofFinite _
  letI : DecidableEq (PairingOrbit P.pair) := Classical.decEq _
  exact (finiteWedgeH1SourceIso (PairingOrbit P.pair)).inv ≫
    finiteWedgeH1Presentation (PairingOrbit P.pair)

theorem finiteWedgeH1CoordinateMap_single (P : PairingData)
    (l : PairingOrbit P.pair) (n : ℤ) :
    finiteWedgeH1CoordinateMap P (orbitBasis P l n) =
      (ConstructionTargets.CircleHomology.circleH1IsoInt.inv ≫
        finiteWedgeLegH1 l) n := by
  letI : Fintype (PairingOrbit P.pair) := Fintype.ofFinite _
  letI : DecidableEq (PairingOrbit P.pair) := Classical.decEq _
  change finiteWedgeH1CoordinateMap P (Pi.single l n) = _
  rw [← sigma_ι_finiteWedgeH1SourceIso_hom_apply
    (PairingOrbit P.pair) l n]
  rw [finiteWedgeH1CoordinateMap]
  change ((Sigma.ι (fun _ : PairingOrbit P.pair => ModuleCat.of ℤ ℤ) l ≫
    ((finiteWedgeH1SourceIso (PairingOrbit P.pair)).hom ≫
      (finiteWedgeH1SourceIso (PairingOrbit P.pair)).inv ≫
        finiteWedgeH1Presentation (PairingOrbit P.pair))) n) = _
  rw [Iso.hom_inv_id_assoc, sigma_ι_finiteWedgeH1Presentation]

/-! ### Circle-leg collapse maps -/

/-- Collapse every circle leg except `l` to the basepoint.  These maps
separate the degree-one coordinates and are the geometric input for proving
the normalized presentation monic. -/
noncomputable def finiteWedgeCollapse {L : Type} [DecidableEq L] (l : L) :
    PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge L → Circle :=
  Quotient.lift (fun p : L × Circle => if p.1 = l then p.2 else 1) (by
    intro a b hab
    change Relation.EqvGen
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedgeRel L) a b at hab
    rw [PolygonSurfacePiOne.PointWedgeQuotient.eqvGen_finiteWedgeRel_iff] at hab
    rcases hab with rfl | ⟨ha, hb⟩
    · rfl
    · have ha' : a.2 = (1 : Circle) := by
        apply Circle.coe_injective
        simpa using ha
      have hb' : b.2 = (1 : Circle) := by
        apply Circle.coe_injective
        simpa using hb
      simp [ha', hb'])

@[simp]
theorem finiteWedgeCollapse_wedgeCircle_self {L : Type} [DecidableEq L]
    (l : L) (z : Circle) :
    finiteWedgeCollapse l
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l z) = z := by
  simp [finiteWedgeCollapse, PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle]

@[simp]
theorem finiteWedgeCollapse_wedgeCircle_of_ne {L : Type} [DecidableEq L]
    {l k : L} (h : k ≠ l) (z : Circle) :
    finiteWedgeCollapse l
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle k z) = 1 := by
  simp [finiteWedgeCollapse, PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle, h]

/-- The collapse to one circle leg is continuous for the quotient topology
used by `FiniteWedge`. -/
theorem continuous_finiteWedgeCollapse {L : Type} [DecidableEq L] (l : L) :
    Continuous (finiteWedgeCollapse l) := by
  apply continuous_coinduced_dom.mpr
  letI : TopologicalSpace L := ⊥
  letI : DiscreteTopology L := ⟨rfl⟩
  rw [continuous_prod_of_discrete_left]
  intro k
  by_cases h : k = l
  · subst k
    simpa [finiteWedgeCollapse,
      PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle] using
        (continuous_id : Continuous (fun z : Circle => z))
  · simpa [finiteWedgeCollapse,
      PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle, h] using
        (continuous_const : Continuous (fun _ : Circle => (1 : Circle)))

/-- The induced map on first homology from the wedge to one selected circle
coordinate. -/
noncomputable def finiteWedgeCollapseH1 {L : Type} [DecidableEq L] (l : L) :
    SpaceH (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge L) 1 ⟶
      SpaceH Circle 1 :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom ⟨finiteWedgeCollapse l, continuous_finiteWedgeCollapse l⟩)

/-- Collapsing after inclusion of the selected leg induces the identity on
first homology. -/
theorem finiteWedgeLegH1_collapse_self {L : Type} [DecidableEq L] (l : L) :
    finiteWedgeLegH1 l ≫ finiteWedgeCollapseH1 l = 𝟙 (SpaceH Circle 1) := by
  rw [finiteWedgeLegH1, finiteWedgeCollapseH1]
  rw [← Functor.map_comp]
  have hc :
    TopCat.ofHom ⟨PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l,
        PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle l⟩ ≫
      TopCat.ofHom ⟨finiteWedgeCollapse l, continuous_finiteWedgeCollapse l⟩ =
        𝟙 (TopCat.of Circle) := by
    ext z
    exact congrArg ((↑) : Circle → ℂ)
      (finiteWedgeCollapse_wedgeCircle_self l z)
  rw [hc]
  exact CategoryTheory.Functor.map_id _ _

/-- A different circle leg becomes constant after collapse, hence induces
the zero map on positive-degree homology. -/
theorem finiteWedgeLegH1_collapse_of_ne {L : Type} [DecidableEq L]
    {l k : L} (h : k ≠ l) :
    finiteWedgeLegH1 k ≫ finiteWedgeCollapseH1 l = 0 := by
  rw [finiteWedgeLegH1, finiteWedgeCollapseH1, ← Functor.map_comp]
  have hc :
      TopCat.ofHom ⟨PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle k,
          PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle k⟩ ≫
        TopCat.ofHom ⟨finiteWedgeCollapse l,
          continuous_finiteWedgeCollapse l⟩ =
      TopCat.ofHom (ContinuousMap.const Circle (1 : Circle)) := by
    ext z
    exact congrArg ((↑) : Circle → ℂ)
      (finiteWedgeCollapse_wedgeCircle_of_ne h z)
  rw [hc]
  exact ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_const_eq_zero
      (ModuleCat ℤ)
      (ModuleCat.of ℤ ℤ) 1 one_ne_zero 1

/-- The leg inclusions and collapses form the Kronecker-delta matrix on
degree-one circle generators. -/
@[reassoc]
theorem finiteWedgeH1_leg_collapse_matrix {L : Type} [DecidableEq L]
    (k l : L) :
    ConstructionTargets.CircleHomology.circleH1IsoInt.inv ≫
        finiteWedgeLegH1 k ≫ finiteWedgeCollapseH1 l =
      if k = l then ConstructionTargets.CircleHomology.circleH1IsoInt.inv
      else 0 := by
  by_cases h : k = l
  · subst k
    rw [if_pos rfl, finiteWedgeLegH1_collapse_self,
      Category.comp_id]
  · rw [if_neg h, finiteWedgeLegH1_collapse_of_ne h,
      comp_zero]

/-- Read all first-homology coordinates by collapsing to each circle leg. -/
noncomputable def finiteWedgeH1CollapseCoordinates (P : PairingData) :
    SpaceH
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
          (PairingOrbit P.pair)) 1 ⟶
      ModuleCat.of ℤ (PairingOrbit P.pair → ℤ) := by
  exact ModuleCat.ofHom (LinearMap.pi fun l =>
    (finiteWedgeCollapseH1 l ≫
      ConstructionTargets.CircleHomology.circleH1IsoInt.hom).hom)

/-- The coproduct presentation followed by all collapse coordinates is the
standard finite-function coordinate isomorphism. -/
theorem finiteWedgeH1Presentation_collapseCoordinates (P : PairingData) :
    finiteWedgeH1Presentation (PairingOrbit P.pair) ≫
        finiteWedgeH1CollapseCoordinates P =
      (finiteWedgeH1SourceIso (PairingOrbit P.pair)).hom := by
  classical
  letI : Fintype (PairingOrbit P.pair) := Fintype.ofFinite _
  apply Sigma.hom_ext
  intro k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro n
  apply funext
  intro l
  rw [sigma_ι_finiteWedgeH1Presentation_assoc]
  change ((ConstructionTargets.CircleHomology.circleH1IsoInt.inv ≫
      finiteWedgeLegH1 k ≫ finiteWedgeCollapseH1 l ≫
        ConstructionTargets.CircleHomology.circleH1IsoInt.hom) n) = _
  rw [finiteWedgeH1_leg_collapse_matrix_assoc]
  rw [sigma_ι_finiteWedgeH1SourceIso_hom_apply]
  by_cases h : k = l
  · subst l
    rw [if_pos rfl, Iso.inv_hom_id]
    simp
  · rw [if_neg h, zero_comp]
    simp [h]

/-- The collapse-coordinate morphism is a left inverse of the normalized
finite-wedge first-homology coordinate map. -/
theorem finiteWedgeH1CoordinateMap_leftInverse (P : PairingData) :
    finiteWedgeH1CoordinateMap P ≫ finiteWedgeH1CollapseCoordinates P =
      𝟙 (ModuleCat.of ℤ (PairingOrbit P.pair → ℤ)) := by
  classical
  letI : Fintype (PairingOrbit P.pair) := Fintype.ofFinite _
  rw [finiteWedgeH1CoordinateMap, Category.assoc,
    finiteWedgeH1Presentation_collapseCoordinates,
    Iso.inv_hom_id]

/-- The normalized finite-wedge first-homology coordinate map is monic. -/
noncomputable instance finiteWedgeH1CoordinateMap_mono (P : PairingData) :
    Mono (finiteWedgeH1CoordinateMap P) := by
  exact (SplitMono.mk (finiteWedgeH1CollapseCoordinates P)
    (finiteWedgeH1CoordinateMap_leftInverse P)).mono

/-! ### Hurewicz representatives for finite-wedge H1 -/

/-- The module-valued first homology class represented by a based loop in the
orbit-indexed finite wedge.  The existing Hurewicz map is computed in
`AddCommGrp`; the comparison isomorphism transports it back to the module
homology used by the polygon calculation. -/
noncomputable def finiteWedgeModuleHurewicz (P : PairingData) :
    FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
          (PairingOrbit P.pair)) (orbitWedgeBase P) →
      SpaceH
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
          (PairingOrbit P.pair)) 1 :=
  fun g =>
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
          (PairingOrbit P.pair))) 1).inv
      (Multiplicative.toAdd
        (ConstructionTargets.DegreeOneHurewiczMap.fundamentalGroupH1Hom
          (orbitWedgeBase P) g))

/-- Every module-valued first homology class of the finite wedge has a based
loop representative.  This isolates the remaining coordinate-surjectivity
task to showing that such loop classes are generated by the circle legs. -/
theorem finiteWedgeModuleHurewicz_surjective (P : PairingData) :
    Function.Surjective (finiteWedgeModuleHurewicz P) := by
  letI : Nonempty (PairingOrbit P.pair) :=
    ⟨P.orbit ⟨0, P.edgeCount_pos⟩⟩
  intro h
  let e :=
    ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
          (PairingOrbit P.pair))) 1
  obtain ⟨g, hg⟩ :=
    ConstructionTargets.DegreeOneHurewiczSurjective.fundamentalGroupH1Hom_surjective
      (orbitWedgeBase P) (Multiplicative.ofAdd (e.hom h))
  refine ⟨g, ?_⟩
  change e.inv
      (Multiplicative.toAdd
        (ConstructionTargets.DegreeOneHurewiczMap.fundamentalGroupH1Hom
          (orbitWedgeBase P) g)) = h
  rw [hg]
  exact e.hom_inv_id_apply h

/-- To prove that the normalized coordinate map is onto, it suffices to
express every based-loop Hurewicz class as a finite linear combination of the
circle-leg generators.  Degree-one Hurewicz surjectivity then supplies a loop
representing an arbitrary homology class. -/
theorem finiteWedgeH1CoordinateMap_surjective_of_hurewicz_generation
    (P : PairingData)
    (hgenerate : ∀ g,
      ∃ v : PairingOrbit P.pair → ℤ,
        finiteWedgeH1CoordinateMap P v = finiteWedgeModuleHurewicz P g) :
    Function.Surjective (finiteWedgeH1CoordinateMap P) := by
  intro h
  obtain ⟨g, rfl⟩ := finiteWedgeModuleHurewicz_surjective P h
  exact hgenerate g

/-! ### A normalized circle element for finite-wedge words -/

/-- The module-valued Hurewicz class of a based loop, for an arbitrary
space.  This comparison-normalized form is convenient when mapping the
positive circle generator into individual wedge legs. -/
noncomputable def moduleHurewicz {X : Type} [TopologicalSpace X] (x : X) :
    FundamentalGroup X x →
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)) :=
  fun g =>
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of X) 1).inv
      (Multiplicative.toAdd
        (ConstructionTargets.DegreeOneHurewiczMap.fundamentalGroupH1Hom x g))

/-- The comparison-normalized module Hurewicz class is natural under a
continuous map. -/
theorem moduleHurewicz_naturality {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (x : X) (g : FundamentalGroup X x) :
    moduleHurewicz (f x) (FundamentalGroup.map f x g) =
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)) (moduleHurewicz x g) := by
  let eX :=
    ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of X) 1
  let eY :=
    ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of Y) 1
  let a := Multiplicative.toAdd
    (ConstructionTargets.DegreeOneHurewiczMap.fundamentalGroupH1Hom x g)
  apply (AddCommGrpCat.mono_iff_injective eY.hom).mp inferInstance
  have hcomparison := congrArg
    (fun q => q (eX.inv a))
    (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison_naturality
      (TopCat.ofHom f) 1)
  have hhurewicz :=
    ConstructionTargets.DegreeOneHurewiczMap.fundamentalGroupH1Hom_naturality
      f x g
  change eY.hom (eY.inv
      (Multiplicative.toAdd
        (ConstructionTargets.DegreeOneHurewiczMap.fundamentalGroupH1Hom
          (f x) (FundamentalGroup.map f x g)))) = _
  rw [eY.inv_hom_id_apply]
  change _ = eY.hom
    ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)) (eX.inv a))
  have hc : eY.hom
      ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)) (eX.inv a)) =
      (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f)) a := by
    change eY.hom
        ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)) (eX.inv a)) =
      (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
        (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f)) (eX.hom (eX.inv a)) at hcomparison
    rw [eX.inv_hom_id_apply] at hcomparison
    exact hcomparison
  rw [hc]
  exact congrArg Multiplicative.toAdd hhurewicz.symm

/-- A based circle class whose Hurewicz image is the positive generator fixed
by `circleH1IsoInt`.  Choosing it through Hurewicz surjectivity avoids adding
a second, potentially incompatible orientation convention for explicit
circle paths. -/
noncomputable def circlePositiveFundamentalClass :
    FundamentalGroup Circle 1 := by
  letI : PathConnectedSpace Circle :=
    pathConnectedSpace_iff_univ.mpr (by
      have h : IsPathConnected
          (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
            (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
        ConstructionTargets.CircleHomology.circleHomeomorphSphereOne
          |>.isPathConnected_preimage.mpr isPathConnected_univ
      simpa using h)
  let e :=
    ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of Circle) 1
  exact Classical.choose
    (ConstructionTargets.DegreeOneHurewiczSurjective.fundamentalGroupH1Hom_surjective
      (1 : Circle)
      (Multiplicative.ofAdd
        (e.hom (ConstructionTargets.CircleHomology.circleH1IsoInt.inv 1))))

/-- The chosen circle class has exactly the positive module-homology
normalization required by the wedge coordinate presentation. -/
theorem moduleHurewicz_circlePositiveFundamentalClass :
    moduleHurewicz (1 : Circle) circlePositiveFundamentalClass =
      ConstructionTargets.CircleHomology.circleH1IsoInt.inv 1 := by
  letI : PathConnectedSpace Circle :=
    pathConnectedSpace_iff_univ.mpr (by
      have h : IsPathConnected
          (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
            (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
        ConstructionTargets.CircleHomology.circleHomeomorphSphereOne
          |>.isPathConnected_preimage.mpr isPathConnected_univ
      simpa using h)
  let e :=
    ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of Circle) 1
  change e.inv (Multiplicative.toAdd
    (ConstructionTargets.DegreeOneHurewiczMap.fundamentalGroupH1Hom
      (1 : Circle) circlePositiveFundamentalClass)) = _
  rw [show ConstructionTargets.DegreeOneHurewiczMap.fundamentalGroupH1Hom
      (1 : Circle) circlePositiveFundamentalClass =
      Multiplicative.ofAdd
        (e.hom (ConstructionTargets.CircleHomology.circleH1IsoInt.inv 1)) from
    Classical.choose_spec
      (ConstructionTargets.DegreeOneHurewiczSurjective.fundamentalGroupH1Hom_surjective
        (1 : Circle)
        (Multiplicative.ofAdd
          (e.hom (ConstructionTargets.CircleHomology.circleH1IsoInt.inv 1))))]
  exact e.hom_inv_id_apply _

/-- The comparison-normalized Hurewicz map is injective on the circle's
fundamental group. -/
theorem moduleHurewicz_circle_injective :
    Function.Injective (moduleHurewicz (1 : Circle)) := by
  intro p q hpq
  let e :=
    ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of Circle) 1
  have hadd : Multiplicative.toAdd
        (ConstructionTargets.DegreeOneHurewiczMap.fundamentalGroupH1Hom 1 p) =
      Multiplicative.toAdd
        (ConstructionTargets.DegreeOneHurewiczMap.fundamentalGroupH1Hom 1 q) := by
    have h := congrArg (fun z => e.hom z) hpq
    simpa [moduleHurewicz, e] using h
  have hmul :
      ConstructionTargets.DegreeOneHurewiczMap.fundamentalGroupH1Hom 1 p =
        ConstructionTargets.DegreeOneHurewiczMap.fundamentalGroupH1Hom 1 q :=
    Multiplicative.toAdd.injective hadd
  have hab : Abelianization.of p = Abelianization.of q := by
    apply ConstructionTargets.CircleHurewiczIsomorphism.circleAbelianizedFundamentalGroupH1MulEquiv.injective
    change ConstructionTargets.DegreeOneHurewiczMap.abelianizedFundamentalGroupToH1 1
        (Abelianization.of p) =
      ConstructionTargets.DegreeOneHurewiczMap.abelianizedFundamentalGroupToH1 1
        (Abelianization.of q)
    simpa using hmul
  apply ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt.injective
  have hcoord := congrArg
    ConstructionTargets.CircleHurewiczIsomorphism.circleAbelianizedFundamentalGroupMulEquivInt hab
  simpa [ConstructionTargets.CircleHurewiczIsomorphism.circleAbelianizedFundamentalGroupMulEquivInt,
    ConstructionTargets.CircleHurewiczIsomorphism.commGroupAbelianizationMulEquiv]
    using hcoord

/-- The positive circle fundamental class mapped into the `l`th wedge leg. -/
noncomputable def finiteWedgeLegFundamentalClass {L : Type} (l : L) :
    FundamentalGroup
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge L)
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l 1) :=
  FundamentalGroup.map
    ⟨PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l,
      PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle l⟩
    1 circlePositiveFundamentalClass

/-- The leg fundamental class has exactly the positive H1 class used in the
finite-wedge coordinate presentation. -/
theorem finiteWedgeLegFundamentalClass_hurewicz {L : Type} (l : L) :
    moduleHurewicz
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l 1)
        (finiteWedgeLegFundamentalClass l) =
      finiteWedgeLegH1 l
        (ConstructionTargets.CircleHomology.circleH1IsoInt.inv 1) := by
  let f : C(Circle,
      PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge L) :=
    ⟨PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l,
      PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle l⟩
  change moduleHurewicz (f 1)
      (FundamentalGroup.map f 1 circlePositiveFundamentalClass) = _
  rw [moduleHurewicz_naturality,
    moduleHurewicz_circlePositiveFundamentalClass]
  rfl

/-- Changing a fundamental-group basepoint along a literal equality does not
change its comparison-normalized Hurewicz class. -/
theorem moduleHurewicz_cast {X : Type} [TopologicalSpace X] {x y : X}
    (h : x = y) (g : FundamentalGroup X y) :
    moduleHurewicz x (Path.Homotopic.Quotient.cast g h h) =
      moduleHurewicz y g := by
  subst h
  induction g using Quotient.inductionOn with
  | _ p =>
      change moduleHurewicz x
          ((Path.Homotopic.Quotient.mk p).cast rfl rfl) =
        moduleHurewicz x (Path.Homotopic.Quotient.mk p)
      rw [← Path.Homotopic.Quotient.mk_cast]
      have hp : p.cast rfl rfl = p := by
        ext t
        rfl
      rw [hp]

/-- The positive `l`th leg class transported to the single common basepoint
used for words in the orbit-indexed finite wedge. -/
noncomputable def finiteWedgeLegFundamentalClassAtBase (P : PairingData)
    (l : PairingOrbit P.pair) :
    FundamentalGroup
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
        (PairingOrbit P.pair)) (orbitWedgeBase P) :=
  Path.Homotopic.Quotient.cast (finiteWedgeLegFundamentalClass l)
    (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle_base_eq
      (P.orbit ⟨0, P.edgeCount_pos⟩) l)
    (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle_base_eq
      (P.orbit ⟨0, P.edgeCount_pos⟩) l)

/-- Transporting a leg class to the common wedge basepoint preserves its
positive coordinate-presentation H1 class. -/
theorem finiteWedgeLegFundamentalClassAtBase_hurewicz (P : PairingData)
    (l : PairingOrbit P.pair) :
    moduleHurewicz (orbitWedgeBase P)
        (finiteWedgeLegFundamentalClassAtBase P l) =
      finiteWedgeLegH1 l
        (ConstructionTargets.CircleHomology.circleH1IsoInt.inv 1) := by
  rw [finiteWedgeLegFundamentalClassAtBase, moduleHurewicz_cast,
    finiteWedgeLegFundamentalClass_hurewicz]

/-- At the common wedge basepoint, the Hurewicz image of the `l`th leg
fundamental class is literally the normalized coordinate-map image of the
`l`th standard basis vector. -/
theorem finiteWedgeLegFundamentalClassAtBase_hurewicz_eq_coordinate
    (P : PairingData) (l : PairingOrbit P.pair) :
    moduleHurewicz (orbitWedgeBase P)
        (finiteWedgeLegFundamentalClassAtBase P l) =
      finiteWedgeH1CoordinateMap P (orbitBasis P l 1) := by
  rw [finiteWedgeLegFundamentalClassAtBase_hurewicz,
    finiteWedgeH1CoordinateMap_single]
  rfl

/-- The comparison-normalized Hurewicz construction is a group homomorphism
when the additive module target is written multiplicatively.  This is the
algebraic input for passing from words in wedge-leg classes to sums of their
coordinate images. -/
noncomputable def moduleHurewiczHom {X : Type} [TopologicalSpace X] (x : X) :
    FundamentalGroup X x →*
      Multiplicative
        (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
          (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)) where
  toFun g := Multiplicative.ofAdd (moduleHurewicz x g)
  map_one' := by
    change Multiplicative.ofAdd
      ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of X) 1).inv
        (Multiplicative.toAdd
          (ConstructionTargets.DegreeOneHurewiczMap.fundamentalGroupH1Hom x 1))) = 1
    rw [map_one]
    change Multiplicative.ofAdd
      ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of X) 1).inv 0) = 1
    rw [map_zero]
    rfl
  map_mul' g h := by
    change Multiplicative.ofAdd
      ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of X) 1).inv
        (Multiplicative.toAdd
          (ConstructionTargets.DegreeOneHurewiczMap.fundamentalGroupH1Hom x (g * h)))) = _
    rw [map_mul]
    change Multiplicative.ofAdd
      ((ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of X) 1).inv
        (Multiplicative.toAdd
          (ConstructionTargets.DegreeOneHurewiczMap.fundamentalGroupH1Hom x g) +
         Multiplicative.toAdd
          (ConstructionTargets.DegreeOneHurewiczMap.fundamentalGroupH1Hom x h))) = _
    rw [map_add]
    rfl

@[simp]
theorem moduleHurewicz_mul {X : Type} [TopologicalSpace X] (x : X)
    (g h : FundamentalGroup X x) :
    moduleHurewicz x (g * h) =
      moduleHurewicz x g + moduleHurewicz x h := by
  exact congrArg Multiplicative.toAdd (map_mul (moduleHurewiczHom x) g h)

@[simp]
theorem moduleHurewicz_zpow {X : Type} [TopologicalSpace X] (x : X)
    (g : FundamentalGroup X x) (n : ℤ) :
    moduleHurewicz x (g ^ n) = n • moduleHurewicz x g := by
  exact congrArg Multiplicative.toAdd (map_zpow (moduleHurewiczHom x) g n)

/-- Every circle fundamental-group class is an integer power of the positive
class fixed by the homology orientation. -/
theorem circlePositiveFundamentalClass_generates
    (g : FundamentalGroup Circle 1) :
    ∃ n : ℤ, circlePositiveFundamentalClass ^ n = g := by
  let n : ℤ := ConstructionTargets.CircleHomology.circleH1IsoInt.hom
    (moduleHurewicz (1 : Circle) g)
  refine ⟨n, moduleHurewicz_circle_injective ?_⟩
  rw [moduleHurewicz_zpow, moduleHurewicz_circlePositiveFundamentalClass]
  rw [← map_zsmul]
  simp only [smul_eq_mul, mul_one]
  change ConstructionTargets.CircleHomology.circleH1IsoInt.inv n = _
  exact ConstructionTargets.CircleHomology.circleH1IsoInt.hom_inv_id_apply _

/-! ### Algebraic leg-word evaluation -/

/-- A finite word in the common-basepoint positive leg classes, with integer
exponents. -/
abbrev FiniteWedgeLegWord (P : PairingData) :=
  List (PairingOrbit P.pair × ℤ)

/-- Evaluate a leg word in the fundamental group of the finite wedge. -/
noncomputable def finiteWedgeLegWordGroup (P : PairingData)
    (w : FiniteWedgeLegWord P) :
    FundamentalGroup
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
        (PairingOrbit P.pair)) (orbitWedgeBase P) :=
  (w.map fun q => finiteWedgeLegFundamentalClassAtBase P q.1 ^ q.2).prod

/-- The coordinate sum encoded by a leg word, retaining repeated legs. -/
noncomputable def finiteWedgeLegWordCoordinatesList (P : PairingData)
    (w : FiniteWedgeLegWord P) : PairingOrbit P.pair → ℤ :=
  (w.map fun q => q.2 • orbitBasis P q.1 1).sum

/-- Hurewicz evaluation of a finite leg word is the normalized coordinate map
applied to its list-based coordinate sum. -/
theorem finiteWedgeLegWord_hurewicz (P : PairingData)
    (w : FiniteWedgeLegWord P) :
    moduleHurewicz (orbitWedgeBase P) (finiteWedgeLegWordGroup P w) =
      finiteWedgeH1CoordinateMap P (finiteWedgeLegWordCoordinatesList P w) := by
  induction w with
  | nil =>
      change moduleHurewicz (orbitWedgeBase P) 1 =
        finiteWedgeH1CoordinateMap P 0
      have h := moduleHurewicz_mul (orbitWedgeBase P) 1 1
      have hz : moduleHurewicz (orbitWedgeBase P) 1 = 0 := by
        apply add_left_cancel (a := moduleHurewicz (orbitWedgeBase P) 1)
        simpa using h.symm
      simpa using hz
  | cons q w ih =>
      change moduleHurewicz (orbitWedgeBase P)
          (finiteWedgeLegFundamentalClassAtBase P q.1 ^ q.2 *
            finiteWedgeLegWordGroup P w) =
        finiteWedgeH1CoordinateMap P
          (q.2 • orbitBasis P q.1 1 + finiteWedgeLegWordCoordinatesList P w)
      rw [moduleHurewicz_mul, moduleHurewicz_zpow,
        finiteWedgeLegFundamentalClassAtBase_hurewicz_eq_coordinate,
        map_add, map_zsmul, ih]

/-- The canonical map from the free group on the orbit labels to the
common-basepoint fundamental group, sending each generator to its positive
circle-leg class. -/
noncomputable def finiteWedgeLegFreeGroupMap (P : PairingData) :
    FreeGroup (PairingOrbit P.pair) →*
      FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
          (PairingOrbit P.pair)) (orbitWedgeBase P) :=
  FreeGroup.lift (finiteWedgeLegFundamentalClassAtBase P)

/-- Every element in the image of the canonical free-group map has the exact
finite integer-exponent leg-word form used by `finiteWedgeLegWord_hurewicz`. -/
theorem finiteWedgeLegFreeGroupMap_exists_word (P : PairingData)
    (x : FreeGroup (PairingOrbit P.pair)) :
    ∃ w : FiniteWedgeLegWord P,
      finiteWedgeLegWordGroup P w = finiteWedgeLegFreeGroupMap P x := by
  induction x using FreeGroup.induction_on with
  | C1 =>
      exact ⟨[], by simp [finiteWedgeLegWordGroup]⟩
  | of l =>
      exact ⟨[(l, 1)], by
        simp [finiteWedgeLegWordGroup, finiteWedgeLegFreeGroupMap]⟩
  | inv_of l _ =>
      exact ⟨[(l, -1)], by
        simp [finiteWedgeLegWordGroup, finiteWedgeLegFreeGroupMap]⟩
  | mul x y ihx ihy =>
      rcases ihx with ⟨wx, hx⟩
      rcases ihy with ⟨wy, hy⟩
      exact ⟨wx ++ wy, by
        rw [map_mul]
        simpa only [finiteWedgeLegWordGroup, List.map_append, List.prod_append]
          using congrArg₂ (· * ·) hx hy⟩

/-- Surjectivity of the canonical free-group map is precisely the remaining
topological input needed to obtain leg-word generation. -/
theorem finiteWedgeFundamentalGroup_generated_by_legs_of_freeGroup_surjective
    (P : PairingData) (hsurj : Function.Surjective (finiteWedgeLegFreeGroupMap P))
    (g : FundamentalGroup
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
        (PairingOrbit P.pair)) (orbitWedgeBase P)) :
    ∃ w : FiniteWedgeLegWord P, finiteWedgeLegWordGroup P w = g := by
  rcases hsurj g with ⟨x, rfl⟩
  exact finiteWedgeLegFreeGroupMap_exists_word P x

/-! ### Relabelling finite wedges -/

/-- An equivalence of leg labels induces a homeomorphism of the corresponding
finite circle wedges. -/
noncomputable def finiteWedgeHomeomorphOfEquiv {L K : Type*} (e : L ≃ K) :
    PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge L ≃ₜ
      PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge K where
  toFun := Quotient.lift
    (fun p => PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (e p.1) p.2)
    fun p q h => by
      change Relation.EqvGen
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedgeRel L) p q at h
      rw [PolygonSurfacePiOne.PointWedgeQuotient.eqvGen_finiteWedgeRel_iff] at h
      rcases h with rfl | ⟨hp, hq⟩
      · rfl
      · apply Quotient.sound
        change Relation.EqvGen
          (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedgeRel K)
          (e p.1, p.2) (e q.1, q.2)
        rw [PolygonSurfacePiOne.PointWedgeQuotient.eqvGen_finiteWedgeRel_iff]
        exact Or.inr ⟨hp, hq⟩
  invFun := Quotient.lift
    (fun p => PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (e.symm p.1) p.2)
    fun p q h => by
      change Relation.EqvGen
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedgeRel K) p q at h
      rw [PolygonSurfacePiOne.PointWedgeQuotient.eqvGen_finiteWedgeRel_iff] at h
      rcases h with rfl | ⟨hp, hq⟩
      · rfl
      · apply Quotient.sound
        change Relation.EqvGen
          (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedgeRel L)
          (e.symm p.1, p.2) (e.symm q.1, q.2)
        rw [PolygonSurfacePiOne.PointWedgeQuotient.eqvGen_finiteWedgeRel_iff]
        exact Or.inr ⟨hp, hq⟩
  left_inv := by
    rintro ⟨⟨l, z⟩⟩
    change PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (e.symm (e l)) z = _
    rw [e.symm_apply_apply]
    rfl
  right_inv := by
    rintro ⟨⟨k, z⟩⟩
    change PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (e (e.symm k)) z = _
    rw [e.apply_symm_apply]
    rfl
  continuous_toFun := by
    letI : TopologicalSpace L := ⊥
    letI : DiscreteTopology L := ⟨rfl⟩
    apply Continuous.quotient_lift
    rw [continuous_prod_of_discrete_left]
    exact fun l =>
      PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle (e l)
  continuous_invFun := by
    letI : TopologicalSpace K := ⊥
    letI : DiscreteTopology K := ⟨rfl⟩
    apply Continuous.quotient_lift
    rw [continuous_prod_of_discrete_left]
    exact fun k =>
      PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle (e.symm k)

@[simp]
theorem finiteWedgeHomeomorphOfEquiv_wedgeCircle {L K : Type*} (e : L ≃ K)
    (l : L) (z : Circle) :
    finiteWedgeHomeomorphOfEquiv e
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l z) =
      PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (e l) z := rfl

/-- The polygon's orbit-indexed wedge relabelled by the canonical finite
coordinate type. -/
noncomputable def finiteWedgeOrbitHomeomorphFin (P : PairingData) :
    PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (PairingOrbit P.pair) ≃ₜ
      PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
        (Fin (Fintype.card (PairingOrbit P.pair))) :=
  finiteWedgeHomeomorphOfEquiv (Fintype.equivFin (PairingOrbit P.pair))

@[simp]
theorem finiteWedgeOrbitHomeomorphFin_wedgeCircle (P : PairingData)
    (l : PairingOrbit P.pair) (z : Circle) :
    finiteWedgeOrbitHomeomorphFin P
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l z) =
      PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
        (Fintype.equivFin (PairingOrbit P.pair) l) z := rfl

/-! ### Sum-indexed wedge inclusions -/

/-- Include the left family of circle legs into the wedge indexed by a sum. -/
noncomputable def finiteWedgeSumLeft {L K : Type*} :
    PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge L →
      PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (L ⊕ K) :=
  Quotient.lift
    (fun p => PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (.inl p.1) p.2)
    fun p q h => by
      change Relation.EqvGen
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedgeRel L) p q at h
      rw [PolygonSurfacePiOne.PointWedgeQuotient.eqvGen_finiteWedgeRel_iff] at h
      rcases h with rfl | ⟨hp, hq⟩
      · rfl
      · apply Quotient.sound
        change Relation.EqvGen
          (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedgeRel (L ⊕ K))
          (Sum.inl p.1, p.2) (Sum.inl q.1, q.2)
        rw [PolygonSurfacePiOne.PointWedgeQuotient.eqvGen_finiteWedgeRel_iff]
        exact Or.inr ⟨hp, hq⟩

/-- Include the right family of circle legs into the wedge indexed by a sum. -/
noncomputable def finiteWedgeSumRight {L K : Type*} :
    PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge K →
      PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (L ⊕ K) :=
  Quotient.lift
    (fun p => PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (.inr p.1) p.2)
    fun p q h => by
      change Relation.EqvGen
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedgeRel K) p q at h
      rw [PolygonSurfacePiOne.PointWedgeQuotient.eqvGen_finiteWedgeRel_iff] at h
      rcases h with rfl | ⟨hp, hq⟩
      · rfl
      · apply Quotient.sound
        change Relation.EqvGen
          (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedgeRel (L ⊕ K))
          (Sum.inr p.1, p.2) (Sum.inr q.1, q.2)
        rw [PolygonSurfacePiOne.PointWedgeQuotient.eqvGen_finiteWedgeRel_iff]
        exact Or.inr ⟨hp, hq⟩

@[simp]
theorem finiteWedgeSumLeft_wedgeCircle {L K : Type*} (l : L) (z : Circle) :
    finiteWedgeSumLeft (K := K)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l z) =
      PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (.inl l) z := rfl

@[simp]
theorem finiteWedgeSumRight_wedgeCircle {L K : Type*} (k : K) (z : Circle) :
    finiteWedgeSumRight (L := L)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle k z) =
      PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (.inr k) z := rfl

theorem continuous_finiteWedgeSumLeft {L K : Type*} :
    Continuous (finiteWedgeSumLeft (L := L) (K := K)) := by
  letI : TopologicalSpace L := ⊥
  letI : DiscreteTopology L := ⟨rfl⟩
  apply Continuous.quotient_lift
  rw [continuous_prod_of_discrete_left]
  exact fun l =>
    PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle (Sum.inl l)

theorem continuous_finiteWedgeSumRight {L K : Type*} :
    Continuous (finiteWedgeSumRight (L := L) (K := K)) := by
  letI : TopologicalSpace K := ⊥
  letI : DiscreteTopology K := ⟨rfl⟩
  apply Continuous.quotient_lift
  rw [continuous_prod_of_discrete_left]
  exact fun k =>
    PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle (Sum.inr k)

theorem finiteWedgeSum_base_eq {L K : Type*} (l : L) (k : K) :
    finiteWedgeSumLeft (K := K)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l 1) =
      finiteWedgeSumRight (L := L)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle k 1) := by
  exact PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle_base_eq
    (Sum.inl l) (Sum.inr k)

/-- Descend the two sum-family inclusions through the point-wedge quotient. -/
noncomputable def pointWedgeToFiniteWedgeSum {L K : Type*} (l : L) (k : K) :
    ConstructionTargets.PointWedgeQuotient.Wedge
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l 1)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle k 1) →
      PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (L ⊕ K) :=
  Quotient.lift (Sum.elim finiteWedgeSumLeft finiteWedgeSumRight) fun a b h => by
    induction h with
    | rel a b h =>
        cases h
        exact finiteWedgeSum_base_eq l k
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem continuous_pointWedgeToFiniteWedgeSum {L K : Type*} (l : L) (k : K) :
    Continuous (pointWedgeToFiniteWedgeSum l k) := by
  apply Continuous.quotient_lift
  rw [continuous_sum_dom]
  exact ⟨continuous_finiteWedgeSumLeft, continuous_finiteWedgeSumRight⟩

@[simp]
theorem pointWedgeToFiniteWedgeSum_left {L K : Type*} (l₀ : L) (k₀ : K)
    (x : PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge L) :
    pointWedgeToFiniteWedgeSum l₀ k₀
        (ConstructionTargets.PointWedgeQuotient.quotientMap
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l₀ 1)
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle k₀ 1) (.inl x)) =
      finiteWedgeSumLeft x := rfl

@[simp]
theorem pointWedgeToFiniteWedgeSum_right {L K : Type*} (l₀ : L) (k₀ : K)
    (y : PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge K) :
    pointWedgeToFiniteWedgeSum l₀ k₀
        (ConstructionTargets.PointWedgeQuotient.quotientMap
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l₀ 1)
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle k₀ 1) (.inr y)) =
      finiteWedgeSumRight y := rfl

/-- Send a sum-indexed finite wedge to the binary point wedge of its two
subfamilies. -/
noncomputable def finiteWedgeSumToPointWedge {L K : Type*} (l₀ : L) (k₀ : K) :
    PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (L ⊕ K) →
      ConstructionTargets.PointWedgeQuotient.Wedge
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l₀ 1)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle k₀ 1) :=
  Quotient.lift
    (fun p => match p.1 with
      | .inl l => ConstructionTargets.PointWedgeQuotient.quotientMap
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l₀ 1)
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle k₀ 1)
          (.inl (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l p.2))
      | .inr k => ConstructionTargets.PointWedgeQuotient.quotientMap
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l₀ 1)
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle k₀ 1)
          (.inr (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle k p.2)))
    fun p q h => by
      change Relation.EqvGen
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedgeRel (L ⊕ K)) p q at h
      rw [PolygonSurfacePiOne.PointWedgeQuotient.eqvGen_finiteWedgeRel_iff] at h
      rcases h with rfl | ⟨hp, hq⟩
      · rfl
      · cases p with
        | mk sp zp =>
          cases q with
          | mk sq zq =>
            have hzp : zp = 1 := Subtype.ext hp
            have hzq : zq = 1 := Subtype.ext hq
            subst zp
            subst zq
            let qmap := ConstructionTargets.PointWedgeQuotient.quotientMap
              (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l₀ 1)
              (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle k₀ 1)
            have hb : ∀ s : L ⊕ K,
                (match s with
                  | .inl l => qmap (.inl
                      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l 1))
                  | .inr k => qmap (.inr
                      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle k 1))) =
                  qmap (.inl
                    (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l₀ 1)) := by
              rintro (l | k)
              · exact congrArg (fun x => qmap (.inl x))
                  (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle_base_eq l l₀)
              · calc
                  qmap (.inr
                      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle k 1)) =
                      qmap (.inr
                        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle k₀ 1)) :=
                    congrArg (fun x => qmap (.inr x))
                      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle_base_eq k k₀)
                  _ = qmap (.inl
                      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l₀ 1)) :=
                    (Quotient.sound (Relation.EqvGen.rel _ _
                      ConstructionTargets.PointWedgeQuotient.Rel.base)).symm
            exact (hb sp).trans (hb sq).symm

theorem continuous_finiteWedgeSumToPointWedge {L K : Type*} (l₀ : L) (k₀ : K) :
    Continuous (finiteWedgeSumToPointWedge l₀ k₀) := by
  letI : TopologicalSpace (L ⊕ K) := ⊥
  letI : DiscreteTopology (L ⊕ K) := ⟨rfl⟩
  apply Continuous.quotient_lift
  rw [continuous_prod_of_discrete_left]
  rintro (l | k)
  · exact (ConstructionTargets.PointWedgeQuotient.continuous_quotientMap _ _).comp
      (continuous_inl.comp
        (PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle l))
  · exact (ConstructionTargets.PointWedgeQuotient.continuous_quotientMap _ _).comp
      (continuous_inr.comp
        (PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle k))

theorem pointWedgeToFiniteWedgeSum_finiteWedgeSumToPointWedge
    {L K : Type*} (l₀ : L) (k₀ : K)
    (x : PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (L ⊕ K)) :
    pointWedgeToFiniteWedgeSum l₀ k₀ (finiteWedgeSumToPointWedge l₀ k₀ x) = x := by
  refine Quotient.inductionOn x ?_
  rintro ⟨l | k, z⟩ <;> rfl

theorem finiteWedgeSumToPointWedge_pointWedgeToFiniteWedgeSum
    {L K : Type*} (l₀ : L) (k₀ : K)
    (x : ConstructionTargets.PointWedgeQuotient.Wedge
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l₀ 1)
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle k₀ 1)) :
    finiteWedgeSumToPointWedge l₀ k₀ (pointWedgeToFiniteWedgeSum l₀ k₀ x) = x := by
  refine Quotient.inductionOn x ?_
  rintro (x | y)
  · refine Quotient.inductionOn x ?_
    rintro ⟨l, z⟩
    rfl
  · refine Quotient.inductionOn y ?_
    rintro ⟨k, z⟩
    rfl

/-- A finite wedge indexed by a sum is the binary point wedge of the two
subfamily wedges, with chosen representatives of their common basepoints. -/
noncomputable def finiteWedgeSumHomeomorphPointWedge {L K : Type*}
    (l₀ : L) (k₀ : K) :
    PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (L ⊕ K) ≃ₜ
      ConstructionTargets.PointWedgeQuotient.Wedge
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l₀ 1)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle k₀ 1) where
  toFun := finiteWedgeSumToPointWedge l₀ k₀
  invFun := pointWedgeToFiniteWedgeSum l₀ k₀
  left_inv := pointWedgeToFiniteWedgeSum_finiteWedgeSumToPointWedge l₀ k₀
  right_inv := finiteWedgeSumToPointWedge_pointWedgeToFiniteWedgeSum l₀ k₀
  continuous_toFun := continuous_finiteWedgeSumToPointWedge l₀ k₀
  continuous_invFun := continuous_pointWedgeToFiniteWedgeSum l₀ k₀

/-- Split the labels of a nonempty successor finite type into its first labels
and its last label. -/
def finSuccEquivSumUnit (n : ℕ) : Fin (n + 1) ≃ Fin n ⊕ Unit :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl (Fin n)) finOneEquiv)

@[simp]
theorem finSuccEquivSumUnit_castSucc (n : ℕ) (i : Fin n) :
    finSuccEquivSumUnit n i.castSucc = Sum.inl i := by
  simp [finSuccEquivSumUnit]

@[simp]
theorem finSuccEquivSumUnit_last (n : ℕ) :
    finSuccEquivSumUnit n (Fin.last n) = Sum.inr () := by
  simp [finSuccEquivSumUnit]

/-- A wedge of `n + 1` circles, with `n` nonempty, is the point wedge of the
first `n` circles and the final circle. -/
noncomputable def finiteWedgeFinSuccHomeomorphPointWedge (n : ℕ) :
    PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin ((n + 1) + 1)) ≃ₜ
      ConstructionTargets.PointWedgeQuotient.Wedge
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1) :=
  (finiteWedgeHomeomorphOfEquiv (finSuccEquivSumUnit (n + 1))).trans
    (finiteWedgeSumHomeomorphPointWedge (0 : Fin (n + 1)) ())

@[simp]
theorem finiteWedgeFinSuccHomeomorphPointWedge_castSucc (n : ℕ)
    (i : Fin (n + 1)) (z : Circle) :
    finiteWedgeFinSuccHomeomorphPointWedge n
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle i.castSucc z) =
      ConstructionTargets.PointWedgeQuotient.quotientMap
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1)
        (.inl (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle i z)) := by
  change finiteWedgeSumHomeomorphPointWedge (0 : Fin (n + 1)) ()
      (finiteWedgeHomeomorphOfEquiv (finSuccEquivSumUnit (n + 1))
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle i.castSucc z)) = _
  rw [finiteWedgeHomeomorphOfEquiv_wedgeCircle,
    finSuccEquivSumUnit_castSucc]
  rfl

@[simp]
theorem finiteWedgeFinSuccHomeomorphPointWedge_last (n : ℕ) (z : Circle) :
    finiteWedgeFinSuccHomeomorphPointWedge n
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (Fin.last (n + 1)) z) =
      ConstructionTargets.PointWedgeQuotient.quotientMap
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1)
        (.inr (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () z)) := by
  change finiteWedgeSumHomeomorphPointWedge (0 : Fin (n + 1)) ()
      (finiteWedgeHomeomorphOfEquiv (finSuccEquivSumUnit (n + 1))
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (Fin.last (n + 1)) z)) = _
  rw [finiteWedgeHomeomorphOfEquiv_wedgeCircle,
    finSuccEquivSumUnit_last]
  rfl

/-- A wedge with a unique label is just its single circle.  This is the
geometric base case for the successor-point-wedge induction. -/
noncomputable def finiteWedgeSubsingletonHomeomorphCircle
    {L : Type} [Subsingleton L] (l : L) :
    PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge L ≃ₜ Circle := by
  classical
  exact
    { toFun := finiteWedgeCollapse l
      invFun := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l
      left_inv := by
        intro x
        refine Quotient.inductionOn x ?_
        rintro ⟨k, z⟩
        have hk : k = l := Subsingleton.elim _ _
        subst k
        change PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l
            (finiteWedgeCollapse l
              (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l z)) = _
        rw [finiteWedgeCollapse_wedgeCircle_self]
        rfl
      right_inv := fun z => finiteWedgeCollapse_wedgeCircle_self l z
      continuous_toFun := continuous_finiteWedgeCollapse l
      continuous_invFun :=
        PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle l }

@[simp]
theorem finiteWedgeSubsingletonHomeomorphCircle_wedgeCircle
    {L : Type} [Subsingleton L] (l k : L) (z : Circle) :
    finiteWedgeSubsingletonHomeomorphCircle l
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle k z) = z := by
  classical
  have hk : k = l := Subsingleton.elim _ _
  subst k
  exact finiteWedgeCollapse_wedgeCircle_self l z

/-- The one-circle finite wedge in the standard finite-coordinate family. -/
noncomputable def finiteWedgeFinOneHomeomorphCircle :
    PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin 1) ≃ₜ Circle :=
  finiteWedgeSubsingletonHomeomorphCircle 0

/-! ### Pointed contractible base neighborhoods -/

/-- The local datum required by the generic point-wedge van Kampen theorem. -/
structure PointedContractibleNeighborhood (X : Type*) [TopologicalSpace X]
    (x₀ : X) where
  carrier : Set X
  isOpen : IsOpen carrier
  mem : x₀ ∈ carrier
  contraction :
    ConstructionTargets.PointedPuncturedCircleContraction.PointedContraction
      carrier ⟨x₀, mem⟩

/-- A homeomorphism restricts to a homeomorphism from the preimage of a set
onto that set. -/
def homeomorphPreimageSet {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (S : Set Y) :
    {x : X // e x ∈ S} ≃ₜ S where
  toFun x := ⟨e x.1, x.2⟩
  invFun y := ⟨e.symm y.1, by rw [e.apply_symm_apply]; exact y.2⟩
  left_inv x := by ext; exact e.symm_apply_apply x.1
  right_inv y := by ext; exact e.apply_symm_apply y.1
  continuous_toFun := Continuous.subtype_mk
    (e.continuous.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    (e.symm.continuous.comp continuous_subtype_val) _

/-- Pull a pointed contractible open neighborhood backward through a
homeomorphism. -/
noncomputable def PointedContractibleNeighborhood.preimageHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x₀ : X} (e : X ≃ₜ Y)
    (P : PointedContractibleNeighborhood Y (e x₀)) :
    PointedContractibleNeighborhood X x₀ where
  carrier := e ⁻¹' P.carrier
  isOpen := P.isOpen.preimage e.continuous
  mem := P.mem
  contraction :=
    ConstructionTargets.PointWedgeVanKampen.PointedContraction.homeomorphSymm
      (homeomorphPreimageSet e P.carrier) P.contraction

/-- The standard punctured-circle neighborhood as packaged local data. -/
def circlePointedContractibleNeighborhood :
    PointedContractibleNeighborhood Circle 1 where
  carrier := ConstructionTargets.PointWedgeVanKampen.circleBaseNeighborhood
  isOpen := ConstructionTargets.PointWedgeVanKampen.circleBaseNeighborhood_isOpen
  mem := ConstructionTargets.PointWedgeVanKampen.circleBase_mem
  contraction :=
    ConstructionTargets.PointWedgeVanKampen.circleBaseNeighborhood_contraction

/-- The contractible base neighborhood for the one-circle finite wedge. -/
noncomputable def finiteWedgeFinOnePointedContractibleNeighborhood :
    PointedContractibleNeighborhood
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin 1))
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle 0 1) :=
  circlePointedContractibleNeighborhood.preimageHomeomorph
    finiteWedgeFinOneHomeomorphCircle

/-- Contractible pointed neighborhoods on two spaces combine to one on their
point wedge.  The carrier is the restricted open wedge of the two carriers. -/
noncomputable def pointWedgePointedContractibleNeighborhood
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x₀ : X} {y₀ : Y}
    (PX : PointedContractibleNeighborhood X x₀)
    (PY : PointedContractibleNeighborhood Y y₀) :
    PointedContractibleNeighborhood
      (ConstructionTargets.PointWedgeQuotient.Wedge x₀ y₀)
      (ConstructionTargets.PointWedgeQuotient.quotientMap x₀ y₀ (.inl x₀)) := by
  let U := ConstructionTargets.PointWedgeRestrictedOpenQuotient.restrictedOpen x₀ y₀
    PX.carrier PY.carrier
  have hU : IsOpen U :=
    ConstructionTargets.PointWedgeRestrictedOpenQuotient.restrictedOpen_isOpen
      PX.isOpen PY.isOpen PX.mem PY.mem
  have hb : ConstructionTargets.PointWedgeQuotient.quotientMap x₀ y₀ (.inl x₀) ∈ U :=
    ⟨.inl x₀, PX.mem, rfl⟩
  let e : U ≃ₜ ConstructionTargets.PointWedgeQuotient.Wedge
      (⟨x₀, PX.mem⟩ : PX.carrier) (⟨y₀, PY.mem⟩ : PY.carrier) :=
    ConstructionTargets.PointWedgeRestrictedOpenQuotient.restrictedOpenHomeomorphWedge
      PX.isOpen PY.isOpen PX.mem PY.mem
  let h := ConstructionTargets.PointWedgeVanKampen.wedgePointedContraction
    PX.contraction PY.contraction
  have he : e ⟨_, hb⟩ =
      ConstructionTargets.PointWedgeQuotient.quotientMap
        (⟨x₀, PX.mem⟩ : PX.carrier) (⟨y₀, PY.mem⟩ : PY.carrier)
        (.inl ⟨x₀, PX.mem⟩) := by
    exact ConstructionTargets.PointWedgeRestrictedOpenQuotient.restrictedOpenHomeomorphWedge_left
      _ _ _ _ _ _
  rw [← he] at h
  exact
    { carrier := U
      isOpen := hU
      mem := hb
      contraction :=
        ConstructionTargets.PointWedgeVanKampen.PointedContraction.homeomorphSymm e h }

/-- The one-circle wedge indexed by `Unit`, used as the new final leg in a
successor split. -/
noncomputable def finiteWedgeUnitPointedContractibleNeighborhood :
    PointedContractibleNeighborhood
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge Unit)
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1) :=
  circlePointedContractibleNeighborhood.preimageHomeomorph
    (finiteWedgeSubsingletonHomeomorphCircle ())

/-- Every nonempty standard finite wedge has a pointed contractible open
neighborhood, obtained by adjoining its circles one at a time. -/
noncomputable def finiteWedgeFinPointedContractibleNeighborhood :
    (n : ℕ) → PointedContractibleNeighborhood
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin (n + 1)))
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
  | 0 => finiteWedgeFinOnePointedContractibleNeighborhood
  | n + 1 => by
      let old := finiteWedgeFinPointedContractibleNeighborhood n
      let last := finiteWedgeUnitPointedContractibleNeighborhood
      let combined := pointWedgePointedContractibleNeighborhood old last
      let e := finiteWedgeFinSuccHomeomorphPointWedge n
      have he : e
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
            (0 : Fin ((n + 1) + 1)) 1) =
          ConstructionTargets.PointWedgeQuotient.quotientMap
            (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
            (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1)
            (.inl (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
              (0 : Fin (n + 1)) 1)) := by
        simpa using finiteWedgeFinSuccHomeomorphPointWedge_castSucc n
          (0 : Fin (n + 1)) 1
      rw [← he] at combined
      exact combined.preimageHomeomorph e

/-- The two pointed neighborhood packages supplied to van Kampen at a
successor split, exposed without the recursive implementation details. -/
noncomputable def finiteWedgeFinSuccPointWedgeNeighborhoods (n : ℕ) :
    PointedContractibleNeighborhood
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin (n + 1)))
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1) ×
      PointedContractibleNeighborhood
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge Unit)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1) :=
  (finiteWedgeFinPointedContractibleNeighborhood n,
    finiteWedgeUnitPointedContractibleNeighborhood)

/-- The left outer comparison in the generic point-wedge reconstruction is
literally in the left coproduct factor, not merely in the kernel of the right
projection. -/
theorem genericPointWedgeOuterLeftComparison_mem_inl
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y]
    (x₀ : X) (y₀ : Y) (M : Set Y) (N : Set X)
    (hM : IsOpen M) (hN : IsOpen N) (hy : y₀ ∈ M) (hx : x₀ ∈ N)
    (cM : ConstructionTargets.PointedPuncturedCircleContraction.PointedContraction
      M ⟨y₀, hy⟩)
    (cN : ConstructionTargets.PointedPuncturedCircleContraction.PointedContraction
      N ⟨x₀, hx⟩) :
    let l := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeActualLeft
      x₀ y₀ M N
    let l' := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeCoordinateLeft x₀
    let eK := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let eL := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeLeftGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let aL := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeLeftSpanIso
      x₀ y₀ M N hM hN hy hx cM cN
    let Q := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeIdentityCoordinateSpan x₀ y₀
    let z := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeOverlapBase x₀ y₀ M N
    ∃ a : FundamentalGroup X x₀,
      (ConstructionTargets.GenericSpanPseudoCoconeTransport.reverseLeftComparison
        l l' eK eL aL Q.left).inv.app z = Monoid.Coprod.inl a := by
  dsimp only
  simp only [ConstructionTargets.PointWedgeVanKampen.genericPointWedgeOverlapBase]
  rw [ConstructionTargets.PointWedgeVanKampen.genericPointWedgeIdentityOuterLeftComparison_app,
    ConstructionTargets.PointWedgeVanKampen.genericPointWedgeIdentityOuterLeftRoundTrip_eq_map,
    ConstructionTargets.PointWedgeVanKampen.genericPointWedgeIdentityOuterLeftSpanFactor_eq_map]
  simp only [CategoryTheory.SingleObj.comp_as_mul]
  rw [eq_of_heq
      (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeIdentityCoordinateSpan_left_map
        x₀ y₀ _),
    eq_of_heq
      (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeIdentityCoordinateSpan_left_map
        x₀ y₀ _)]
  rw [← (Monoid.Coprod.inl
    (N := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightGroup y₀)).map_mul]
  exact ⟨_, rfl⟩

/-- The reconstruction conjugator for the successor finite-wedge split. -/
noncomputable def finiteWedgeSuccessorRightBaseElement (n : ℕ) :=
  let P := finiteWedgeFinSuccPointWedgeNeighborhoods n
  let x₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1
  let y₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1
  ConstructionTargets.PointWedgeVanKampen.genericPointWedgeIdentityGlobalRightBaseElement
    x₀ y₀ P.2.carrier P.1.carrier P.2.isOpen P.1.isOpen
      P.2.mem P.1.mem P.2.contraction P.1.contraction

/-- The named outer-right factor in the successor reconstruction
conjugator. -/
noncomputable def finiteWedgeSuccessorOuterRightElement (n : ℕ) :
    Monoid.Coprod
      (FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin (n + 1)))
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1))
      (FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge Unit)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1)) := by
  let P := finiteWedgeFinSuccPointWedgeNeighborhoods n
  let x₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1
  let y₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1
  let r := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeActualRight
    x₀ y₀ P.2.carrier P.1.carrier
  let r' := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeCoordinateRight y₀
  let eK := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeOverlapGroupoidEquivalence
    x₀ y₀ P.2.carrier P.1.carrier P.2.isOpen P.1.isOpen
      P.2.mem P.1.mem P.2.contraction P.1.contraction
  let eR := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightGroupoidEquivalence
    x₀ y₀ P.2.carrier P.1.carrier P.2.isOpen P.1.isOpen
      P.2.mem P.1.mem P.2.contraction P.1.contraction
  let aR := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightSpanIso
    x₀ y₀ P.2.carrier P.1.carrier P.2.isOpen P.1.isOpen
      P.2.mem P.1.mem P.2.contraction P.1.contraction
  let Q := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeIdentityCoordinateSpan x₀ y₀
  let z := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeOverlapBase
    x₀ y₀ P.2.carrier P.1.carrier
  exact (ConstructionTargets.GenericSpanPseudoCoconeTransport.reverseRightComparison
    r r' eK eR aR Q.right).hom.app z

/-- The successor right-base element is the named outer-right comparison
followed, in single-object multiplication order, by an old-factor element. -/
theorem finiteWedgeSuccessorRightBase_eq_outerRight_mul_inl (n : ℕ) :
    ∃ a : FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin (n + 1)))
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1),
      finiteWedgeSuccessorRightBaseElement n =
        finiteWedgeSuccessorOuterRightElement n * Monoid.Coprod.inl a := by
  let P := finiteWedgeFinSuccPointWedgeNeighborhoods n
  let x₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1
  let y₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1
  obtain ⟨a, ha⟩ := genericPointWedgeOuterLeftComparison_mem_inl
    x₀ y₀ P.2.carrier P.1.carrier P.2.isOpen P.1.isOpen
      P.2.mem P.1.mem P.2.contraction P.1.contraction
  refine ⟨a, ?_⟩
  rw [finiteWedgeSuccessorRightBaseElement,
    ConstructionTargets.PointWedgeVanKampen.genericPointWedgeIdentityGlobalRightBaseElement_eq_outerComparisons]
  change _ = finiteWedgeSuccessorOuterRightElement n * Monoid.Coprod.inl a
  rw [CategoryTheory.SingleObj.comp_as_mul, ha]
  rfl

/-- The exact left-factor condition needed for partial normalization. -/
def finiteWedgeRightBaseInOldFactor (n : ℕ) : Prop :=
  ∃ a : FundamentalGroup
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin (n + 1)))
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1),
    finiteWedgeSuccessorRightBaseElement n = Monoid.Coprod.inl a

/-- It is enough to factor the single outer-right comparison through the old
factor; the other outer comparison is already there structurally. -/
theorem finiteWedgeRightBaseInOldFactor_of_outerRightInOldFactor (n : ℕ)
    (h : ∃ b : FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin (n + 1)))
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1),
      finiteWedgeSuccessorOuterRightElement n = Monoid.Coprod.inl b) :
    finiteWedgeRightBaseInOldFactor n := by
  obtain ⟨a, ha⟩ := finiteWedgeSuccessorRightBase_eq_outerRight_mul_inl n
  obtain ⟨b, hb⟩ := h
  refine ⟨b * a, ?_⟩
  rw [ha, hb, map_mul]

/-- The exact remaining connector square after specializing generic van Kampen
to the successor finite-wedge neighborhoods. -/
def finiteWedgeRightConnectorSquare (n : ℕ) : Prop := by
  let P := finiteWedgeFinSuccPointWedgeNeighborhoods n
  let x₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1
  let y₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1
  let r := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeActualRight
    x₀ y₀ P.2.carrier P.1.carrier
  let eK := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeOverlapGroupoidEquivalence
    x₀ y₀ P.2.carrier P.1.carrier P.2.isOpen P.1.isOpen
      P.2.mem P.1.mem P.2.contraction P.1.contraction
  let eR := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightGroupoidEquivalence
    x₀ y₀ P.2.carrier P.1.carrier P.2.isOpen P.1.isOpen
      P.2.mem P.1.mem P.2.contraction P.1.contraction
  let z := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeOverlapBase
    x₀ y₀ P.2.carrier P.1.carrier
  exact
    ((ConstructionTargets.PointWedgeVanKampen.genericPointWedgeConnectors y₀).connector
      ((eK.functor ⋙ eK.inverse ⋙ r ⋙ eR.functor).obj z)).hom ≫
        (eK.funInvIdAssoc (r ⋙ eR.functor)).hom.app z =
      ((ConstructionTargets.PointWedgeVanKampen.genericPointWedgeConnectors y₀).connector
        ((r ⋙ eR.functor).obj z)).hom

/-- For the successor finite wedge, triviality of the reconstruction
conjugator's right projection is exactly the named connector square above. -/
theorem finiteWedgeRightProjection_eq_one_iff_connectorSquare (n : ℕ) : by
    let P := finiteWedgeFinSuccPointWedgeNeighborhoods n
    let x₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1
    let y₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1
    exact ConstructionTargets.PointWedgeVanKampen.genericPointWedgeFreeProductRightProjection
      x₀ y₀
      (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeIdentityGlobalRightBaseElement
        x₀ y₀ P.2.carrier P.1.carrier P.2.isOpen P.1.isOpen
          P.2.mem P.1.mem P.2.contraction P.1.contraction) = 1 ↔
      finiteWedgeRightConnectorSquare n := by
  exact ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightBase_rightProjection_eq_one_iff_connectorSquare
    _ _ _ _ _ _ _ _ _ _

/-- Left-factor membership implies the connector square.  This is the valid
direction; trivial right projection alone does not characterize `inl`. -/
theorem finiteWedgeRightConnectorSquare_of_inOldFactor (n : ℕ)
    (h : finiteWedgeRightBaseInOldFactor n) :
    finiteWedgeRightConnectorSquare n := by
  rcases h with ⟨a, ha⟩
  apply (finiteWedgeRightProjection_eq_one_iff_connectorSquare n).mp
  exact ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightBase_inl_implies_rightProjection_eq_one
    _ _ _ _ _ _ _ _ _ _ a ha

/-! ### Algebraic word extraction from a point-wedge computation -/

/-- Evaluate a word whose letters come from the two factors of a coproduct. -/
def coprodLegWordValue {A B G : Type*} [Group A] [Group B] [Group G]
    (left : A → G) (right : B → G) (w : List (A ⊕ B)) : G :=
  (w.map (Sum.elim left right)).prod

/-- Once a group equivalence with a free product has the expected values on
the two leg maps, every source element is a finite word in those legs.  This
is the algebraic induction used at each successor step of the finite wedge. -/
theorem exists_coprodLegWord_of_mulEquiv
    {A B G : Type*} [Group A] [Group B] [Group G]
    (E : G ≃* Monoid.Coprod A B) (left : A → G) (right : B → G)
    (hleft : ∀ a, E (left a) = Monoid.Coprod.inl a)
    (hright : ∀ b, E (right b) = Monoid.Coprod.inr b)
    (x : G) :
    ∃ w : List (A ⊕ B), coprodLegWordValue left right w = x := by
  suffices ∀ y : Monoid.Coprod A B,
      ∃ w : List (A ⊕ B), coprodLegWordValue left right w = E.symm y by
    simpa using this (E x)
  intro y
  induction y using Monoid.Coprod.induction_on with
  | inl a =>
      refine ⟨[.inl a], ?_⟩
      apply E.injective
      simp [coprodLegWordValue, hleft]
  | inr b =>
      refine ⟨[.inr b], ?_⟩
      apply E.injective
      simp [coprodLegWordValue, hright]
  | mul u v hu hv =>
      rcases hu with ⟨wu, hu⟩
      rcases hv with ⟨wv, hv⟩
      refine ⟨wu ++ wv, ?_⟩
      simp only [coprodLegWordValue, List.map_append, List.prod_append]
      change coprodLegWordValue left right wu *
          coprodLegWordValue left right wv = E.symm (u * v)
      rw [hu, hv, map_mul]

/-- The generic van Kampen computation supplies literal leg words as soon as
its remaining right-base conjugator is known to lie in the left factor. -/
theorem genericPointWedge_exists_legWord_of_rightBase_inl
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y]
    (x₀ : X) (y₀ : Y) (M : Set Y) (N : Set X)
    (hM : IsOpen M) (hN : IsOpen N) (hy : y₀ ∈ M) (hx : x₀ ∈ N)
    (cM : ConstructionTargets.PointedPuncturedCircleContraction.PointedContraction
      M ⟨y₀, hy⟩)
    (cN : ConstructionTargets.PointedPuncturedCircleContraction.PointedContraction
      N ⟨x₀, hx⟩)
    (a : FundamentalGroup X x₀)
    (ha : ConstructionTargets.PointWedgeVanKampen.genericPointWedgeIdentityGlobalRightBaseElement
          x₀ y₀ M N hM hN hy hx cM cN = Monoid.Coprod.inl a)
    (g : FundamentalGroup
      (ConstructionTargets.PointWedgeQuotient.Wedge x₀ y₀)
      (ConstructionTargets.PointWedgeQuotient.quotientMap x₀ y₀ (.inl x₀))) :
    ∃ w : List (FundamentalGroup X x₀ ⊕ FundamentalGroup Y y₀),
      coprodLegWordValue
          (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeLeftLegMap x₀ y₀)
          (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightLegMap x₀ y₀)
          w = g := by
  have hcoords :=
    ConstructionTargets.PointWedgeVanKampen.genericPointWedgePartiallyNormalized_legCoordinates
        x₀ y₀ M N hM hN hy hx cM cN a ha
  exact exists_coprodLegWord_of_mulEquiv
    (ConstructionTargets.PointWedgeVanKampen.genericPointWedgePartiallyNormalizedFundamentalGroupEquiv
        x₀ y₀ M N hM hN hy hx cM cN a)
    (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeLeftLegMap x₀ y₀)
    (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightLegMap x₀ y₀)
    hcoords.1 hcoords.2 g

end

end ConstructionTargets.PolygonSurfaceHomology
