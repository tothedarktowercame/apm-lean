import Mathlib
import ConstructionTargets.PolygonSurfacePiOne
import ConstructionTargets.PolygonOverlapHomotopyEquivCircle
import ConstructionTargets.SingularHomologyConcrete
import ConstructionTargets.IntegralSingularHomologyComparison
import ConstructionTargets.CircleHomology
import ConstructionTargets.T02A06SphereH0
import ConstructionTargets.CoefficientSigmaConstFinsuppComparison

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

end

end ConstructionTargets.PolygonSurfaceHomology
