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

/-! ### The ordered polygon boundary loop -/

/-- The unit circle regarded as the boundary of the polygon disk. -/
def circleToPolygonDisk (z : Circle) : ConstructionTargets.Surfaces.Disk :=
  ⟨(z : ℂ), by
    rw [Metric.mem_closedBall, dist_zero_right, Circle.norm_coe]⟩

theorem continuous_circleToPolygonDisk : Continuous circleToPolygonDisk :=
  continuous_subtype_val.subtype_mk _

/-- The positively oriented geometric boundary circle, with its image
remembered as a point of the quotient boundary skeleton. -/
def polygonBoundarySkeletonLoop (P : PairingData) : C(Circle, P.skeleton) where
  toFun z :=
    ⟨P.quotientMap (circleToPolygonDisk z),
      ⟨circleToPolygonDisk z, by
        change ‖(z : ℂ)‖ = 1
        exact Circle.norm_coe z, rfl⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact P.continuous_quotientMap.comp continuous_circleToPolygonDisk

/-- The ordered boundary loop in the fixed orbit-indexed wedge coordinates. -/
noncomputable def polygonBoundaryWedgeLoop (P : PairingData) :
    C(Circle,
      PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
        (PairingOrbit P.pair)) :=
  (⟨P.skeletonHomeomorphWedge, P.skeletonHomeomorphWedge.continuous⟩ :
    C(P.skeleton,
      PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
        (PairingOrbit P.pair))).comp (polygonBoundarySkeletonLoop P)

/-- On the `i`th polygon interval the ordered boundary loop is exactly the
signed wedge arc fixed by the pairing data. -/
theorem polygonBoundaryWedgeLoop_edgePoint (P : PairingData)
    (i : Fin P.edgeCount) (t : Set.Icc (0 : ℝ) 1) :
    polygonBoundaryWedgeLoop P
        (PolygonSurfacePiOne.edgePointCircle P.edgeCount i t) =
      P.signedWedgeArc i t := by
  change P.skeletonHomeomorphWedge
      (polygonBoundarySkeletonLoop P
        (PolygonSurfacePiOne.edgePointCircle P.edgeCount i t)) = _
  rw [← P.skeletonHomeomorphWedge_skeletonArc i t]
  congr 1

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

/-- The ordered boundary loop is based at the fixed common wedge point. -/
theorem polygonBoundaryWedgeLoop_one (P : PairingData) :
    polygonBoundaryWedgeLoop P 1 = orbitWedgeBase P := by
  let t : Set.Icc (0 : ℝ) 1 := ⟨0, by simp⟩
  let i : Fin P.edgeCount := ⟨0, P.edgeCount_pos⟩
  have he : PolygonSurfacePiOne.edgePointCircle P.edgeCount i t = (1 : Circle) := by
    apply Subtype.ext
    simp [PolygonSurfacePiOne.edgePointCircle,
      ConstructionTargets.Surfaces.edgePoint, i, t]
  rw [← he, polygonBoundaryWedgeLoop_edgePoint]
  have ht : PolygonSurfacePiOne.circleArc t = (1 : Circle) :=
    (PolygonSurfacePiOne.circleArc_eq_one_iff t).2 (Or.inl (by rfl))
  have hr : PolygonSurfacePiOne.circleArc
      (PolygonSurfacePiOne.reverseIcc t) = (1 : Circle) := by
    apply (PolygonSurfacePiOne.circleArc_eq_one_iff _).2
    right
    simp [PolygonSurfacePiOne.reverseIcc, t]
  change P.signedWedgeArc i t =
    PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (P.orbit i) 1
  cases hs : P.sign i
  · rw [P.signedWedgeArc_of_not_sign i t hs, hr]
  · rw [P.signedWedgeArc_of_sign i t hs, ht]

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

/-- The actual ordered polygon boundary, based at the common wedge point and
applied to the fixed positive circle class. -/
noncomputable def polygonBoundaryFundamentalClass (P : PairingData) :
    FundamentalGroup
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
        (PairingOrbit P.pair)) (orbitWedgeBase P) :=
  Path.Homotopic.Quotient.cast
    (FundamentalGroup.map (polygonBoundaryWedgeLoop P)
      1 circlePositiveFundamentalClass)
    (polygonBoundaryWedgeLoop_one P).symm
    (polygonBoundaryWedgeLoop_one P).symm

/-- Naturality computes the normalized Hurewicz class of the geometric
boundary as the map induced by the explicit boundary circle. -/
theorem polygonBoundaryFundamentalClass_hurewicz (P : PairingData) :
    moduleHurewicz (orbitWedgeBase P) (polygonBoundaryFundamentalClass P) =
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (polygonBoundaryWedgeLoop P)))
        (ConstructionTargets.CircleHomology.circleH1IsoInt.inv 1) := by
  rw [polygonBoundaryFundamentalClass, moduleHurewicz_cast,
    moduleHurewicz_naturality, moduleHurewicz_circlePositiveFundamentalClass]

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

/-- The ordered polygon boundary as a signed word in its paired-edge orbit
labels.  Each geometric edge occurs once and contributes according to the
orientation fixed by `P.sign`. -/
noncomputable def polygonBoundaryLegWord (P : PairingData) :
    FiniteWedgeLegWord P :=
  List.ofFn fun i : Fin P.edgeCount =>
    (P.orbit i, if P.sign i then (1 : ℤ) else -1)

/-- The coordinate sum of the ordered signed boundary word is precisely the
attaching degree vector fixed at the start of the calculation. -/
theorem polygonBoundaryLegWord_coordinates (P : PairingData) :
    finiteWedgeLegWordCoordinatesList P (polygonBoundaryLegWord P) =
      attachingDegree P := by
  classical
  ext l
  simp [finiteWedgeLegWordCoordinatesList, polygonBoundaryLegWord,
    attachingDegree, edgeOrbitContribution, edgeAttachingDegree,
    orbitBasis, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  by_cases ho : P.orbit i = l
  · subst l
    by_cases hs : P.sign i <;> simp [hs]
  · by_cases hs : P.sign i <;> simp [ho, hs]

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

/-- The signed polygon word has Hurewicz image equal to the normalized
coordinate-map image of the attaching degree vector. -/
theorem polygonBoundaryLegWord_hurewicz (P : PairingData) :
    moduleHurewicz (orbitWedgeBase P)
        (finiteWedgeLegWordGroup P (polygonBoundaryLegWord P)) =
      finiteWedgeH1CoordinateMap P (attachingDegree P) := by
  rw [finiteWedgeLegWord_hurewicz, polygonBoundaryLegWord_coordinates]

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

/-- Dually, the complete outer-right comparison is literally in the right
coproduct factor. -/
theorem genericPointWedgeOuterRightComparison_mem_inr
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y]
    (x₀ : X) (y₀ : Y) (M : Set Y) (N : Set X)
    (hM : IsOpen M) (hN : IsOpen N) (hy : y₀ ∈ M) (hx : x₀ ∈ N)
    (cM : ConstructionTargets.PointedPuncturedCircleContraction.PointedContraction
      M ⟨y₀, hy⟩)
    (cN : ConstructionTargets.PointedPuncturedCircleContraction.PointedContraction
      N ⟨x₀, hx⟩) :
    let r := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeActualRight
      x₀ y₀ M N
    let r' := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeCoordinateRight y₀
    let eK := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeOverlapGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let eR := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightGroupoidEquivalence
      x₀ y₀ M N hM hN hy hx cM cN
    let aR := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightSpanIso
      x₀ y₀ M N hM hN hy hx cM cN
    let Q := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeIdentityCoordinateSpan x₀ y₀
    let z := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeOverlapBase x₀ y₀ M N
    ∃ b : FundamentalGroup Y y₀,
      (ConstructionTargets.GenericSpanPseudoCoconeTransport.reverseRightComparison
        r r' eK eR aR Q.right).hom.app z = Monoid.Coprod.inr b := by
  dsimp only
  simp only [ConstructionTargets.PointWedgeVanKampen.genericPointWedgeOverlapBase]
  rw [ConstructionTargets.PointWedgeVanKampen.genericPointWedgeIdentityOuterRightComparison_app,
    ConstructionTargets.PointWedgeVanKampen.genericPointWedgeIdentityOuterRightSpanFactor_eq_map,
    ConstructionTargets.PointWedgeVanKampen.genericPointWedgeIdentityOuterRightRoundTrip_eq_map]
  simp only [CategoryTheory.SingleObj.comp_as_mul]
  rw [eq_of_heq
      (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeIdentityCoordinateSpan_right_map
        x₀ y₀ _),
    eq_of_heq
      (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeIdentityCoordinateSpan_right_map
        x₀ y₀ _)]
  rw [← (Monoid.Coprod.inr
    (M := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeLeftGroup x₀)).map_mul]
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

/-- The named successor outer-right comparison has a literal right-factor
coordinate. -/
theorem finiteWedgeSuccessorOuterRight_mem_inr (n : ℕ) :
    ∃ b : FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge Unit)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1),
      finiteWedgeSuccessorOuterRightElement n = Monoid.Coprod.inr b := by
  let P := finiteWedgeFinSuccPointWedgeNeighborhoods n
  let x₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1
  let y₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1
  simpa [finiteWedgeSuccessorOuterRightElement] using
    genericPointWedgeOuterRightComparison_mem_inr
      x₀ y₀ P.2.carrier P.1.carrier P.2.isOpen P.1.isOpen
        P.2.mem P.1.mem P.2.contraction P.1.contraction

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

/-- The same remaining obstruction in endpoint-transport form: the overlap
counit component must be exactly the transport determined by the two
installed right connectors. -/
def finiteWedgeRightConnectorTransport (n : ℕ) : Prop := by
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
    (eK.funInvIdAssoc (r ⋙ eR.functor)).hom.app z =
      ((ConstructionTargets.PointWedgeVanKampen.genericPointWedgeConnectors y₀).connector
        ((eK.functor ⋙ eK.inverse ⋙ r ⋙ eR.functor).obj z)).inv ≫
      ((ConstructionTargets.PointWedgeVanKampen.genericPointWedgeConnectors y₀).connector
        ((r ⋙ eR.functor).obj z)).hom

/-- The literal target-side inverse-unit connector square at the fixed right
cover base. -/
def finiteWedgeRightBaseTargetUnitSquare (n : ℕ) : Prop := by
  let P := finiteWedgeFinSuccPointWedgeNeighborhoods n
  let x₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1
  let y₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1
  let eR := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightGroupoidEquivalence
    x₀ y₀ P.2.carrier P.1.carrier P.2.isOpen P.1.isOpen
      P.2.mem P.1.mem P.2.contraction P.1.contraction
  let b := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightBase
    x₀ y₀ P.1.carrier
  exact
    ((ConstructionTargets.PointWedgeVanKampen.genericPointWedgeConnectors y₀).connector
      (eR.functor.obj (eR.inverse.obj (eR.functor.obj b)))).hom ≫
        eR.functor.map (eR.unitIso.inv.app b) =
      ((ConstructionTargets.PointWedgeVanKampen.genericPointWedgeConnectors y₀).connector
        (eR.functor.obj b)).hom

/-- The target-side square with the inverse unit rewritten as the right
equivalence counit.  This is the literal endpoint equation left after the
equivalence triangle identity. -/
def finiteWedgeRightBaseCounitSquare (n : ℕ) : Prop := by
  let P := finiteWedgeFinSuccPointWedgeNeighborhoods n
  let x₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1
  let y₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1
  let eR := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightGroupoidEquivalence
    x₀ y₀ P.2.carrier P.1.carrier P.2.isOpen P.1.isOpen
      P.2.mem P.1.mem P.2.contraction P.1.contraction
  let b := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightBase
    x₀ y₀ P.1.carrier
  exact
    ((ConstructionTargets.PointWedgeVanKampen.genericPointWedgeConnectors y₀).connector
      (eR.functor.obj (eR.inverse.obj (eR.functor.obj b)))).hom ≫
        eR.counitIso.hom.app (eR.functor.obj b) =
      ((ConstructionTargets.PointWedgeVanKampen.genericPointWedgeConnectors y₀).connector
        (eR.functor.obj b)).hom

/-- The remaining counit obstruction expressed at the common connector
base: its chosen connector normal form must be the identity. -/
def finiteWedgeRightBaseCounitNormalFormTrivial (n : ℕ) : Prop := by
  let P := finiteWedgeFinSuccPointWedgeNeighborhoods n
  let x₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1
  let y₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1
  let eR := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightGroupoidEquivalence
    x₀ y₀ P.2.carrier P.1.carrier P.2.isOpen P.1.isOpen
      P.2.mem P.1.mem P.2.contraction P.1.contraction
  let b := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightBase
    x₀ y₀ P.1.carrier
  exact
    (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeConnectors y₀).normalForm
        (eR.counitIso.hom.app (eR.functor.obj b)) =
      𝟙 (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeConnectors y₀).base

/-- The literal finite-wedge counit square is exactly triviality of its
connector normal form. -/
theorem finiteWedgeRightBaseCounitSquare_iff_normalFormTrivial (n : ℕ) :
    finiteWedgeRightBaseCounitSquare n ↔
      finiteWedgeRightBaseCounitNormalFormTrivial n := by
  unfold finiteWedgeRightBaseCounitSquare
  unfold finiteWedgeRightBaseCounitNormalFormTrivial
  exact ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightBase_counit_connectorSquare_iff_normalForm
    _ _ _ _ _ _ _ _ _ _

/-- The coherent source-side inverse-unit square induced at the same base. -/
def finiteWedgeCoherentRightSourceUnitSquare (n : ℕ) : Prop := by
  let P := finiteWedgeFinSuccPointWedgeNeighborhoods n
  let x₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1
  let y₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1
  let eR := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightGroupoidEquivalence
    x₀ y₀ P.2.carrier P.1.carrier P.2.isOpen P.1.isOpen
      P.2.mem P.1.mem P.2.contraction P.1.contraction
  let b := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightBase
    x₀ y₀ P.1.carrier
  let source := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeCoherentRightSourceConnectors
    x₀ y₀ P.2.carrier P.1.carrier P.2.isOpen P.1.isOpen
      P.2.mem P.1.mem P.2.contraction P.1.contraction
  exact
    (source.connector (eR.inverse.obj (eR.functor.obj b))).hom ≫
        eR.unitIso.inv.app b = (source.connector b).hom

/-- The generic connector transport construction specializes without any
endpoint casts to the finite-wedge successor packages. -/
theorem finiteWedgeCoherentRightSourceUnitSquare_of_target (n : ℕ)
    (h : finiteWedgeRightBaseTargetUnitSquare n) :
    finiteWedgeCoherentRightSourceUnitSquare n := by
  unfold finiteWedgeRightBaseTargetUnitSquare at h
  unfold finiteWedgeCoherentRightSourceUnitSquare
  exact ConstructionTargets.PointWedgeVanKampen.genericPointWedgeCoherentRightSourceConnectors_rightBase_unitInv_of_target
    _ _ _ _ _ _ _ _ _ _ h

/-- The counit formulation implies the coherent source connector square at
the successor right base. -/
theorem finiteWedgeCoherentRightSourceUnitSquare_of_counit (n : ℕ)
    (h : finiteWedgeRightBaseCounitSquare n) :
    finiteWedgeCoherentRightSourceUnitSquare n := by
  unfold finiteWedgeRightBaseCounitSquare at h
  unfold finiteWedgeCoherentRightSourceUnitSquare
  exact ConstructionTargets.PointWedgeVanKampen.genericPointWedgeCoherentRightSourceConnectors_rightBase_unitInv_of_counit
    _ _ _ _ _ _ _ _ _ _ h

/-- Triviality of the based counit normal form supplies the coherent source
inverse-unit square needed by the installed connector comparison. -/
theorem finiteWedgeCoherentRightSourceUnitSquare_of_counitNormalFormTrivial
    (n : ℕ) (h : finiteWedgeRightBaseCounitNormalFormTrivial n) :
    finiteWedgeCoherentRightSourceUnitSquare n :=
  finiteWedgeCoherentRightSourceUnitSquare_of_counit n
    ((finiteWedgeRightBaseCounitSquare_iff_normalFormTrivial n).mpr h)

/-- The same reduction at an arbitrary right-piece endpoint, in particular
the shifted overlap endpoint used by the installed connector transport. -/
theorem finiteWedgeCoherentRightSourceUnitSquare_at_of_counitNormalForm
    (n : ℕ) :
    let P := finiteWedgeFinSuccPointWedgeNeighborhoods n
    let x₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1
    let y₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1
    let eR := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightGroupoidEquivalence
      x₀ y₀ P.2.carrier P.1.carrier P.2.isOpen P.1.isOpen
        P.2.mem P.1.mem P.2.contraction P.1.contraction
    let source := ConstructionTargets.PointWedgeVanKampen.genericPointWedgeCoherentRightSourceConnectors
      x₀ y₀ P.2.carrier P.1.carrier P.2.isOpen P.1.isOpen
        P.2.mem P.1.mem P.2.contraction P.1.contraction
    ∀ A : FundamentalGroupoid
        (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightPiece
          x₀ y₀ P.1.carrier),
      (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeConnectors y₀).normalForm
          (eR.counitIso.hom.app (eR.functor.obj A)) =
        𝟙 (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeConnectors y₀).base →
      (source.connector (eR.inverse.obj (eR.functor.obj A))).hom ≫
          eR.unitIso.inv.app A = (source.connector A).hom := by
  dsimp only
  intro A h
  exact ConstructionTargets.PointWedgeVanKampen.genericPointWedgeCoherentRightSourceConnectors_unitInv_of_counit_normalForm
    _ _ _ _ _ _ _ _ _ _ A h

/-- Endpoint transport and connector-square formulations are exactly
equivalent, with the direction fixed by left cancellation. -/
theorem finiteWedgeRightConnectorTransport_iff_connectorSquare (n : ℕ) :
    finiteWedgeRightConnectorTransport n ↔ finiteWedgeRightConnectorSquare n := by
  exact ConstructionTargets.PointWedgeVanKampen.eq_connectorTransport_iff_connectorSquare
    _ _

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

/-- For this particular outer-right factor, the connector square does imply
old-factor membership: the factor is already known to be an `inr`, so its
trivial right projection forces it to be the identity. -/
theorem finiteWedgeSuccessorOuterRight_mem_inl_of_connectorSquare (n : ℕ)
    (h : finiteWedgeRightConnectorSquare n) :
    ∃ b : FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin (n + 1)))
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1),
      finiteWedgeSuccessorOuterRightElement n = Monoid.Coprod.inl b := by
  have hp := (finiteWedgeRightProjection_eq_one_iff_connectorSquare n).mpr h
  obtain ⟨a, ha⟩ := finiteWedgeSuccessorRightBase_eq_outerRight_mul_inl n
  obtain ⟨b, hb⟩ := finiteWedgeSuccessorOuterRight_mem_inr n
  change ConstructionTargets.PointWedgeVanKampen.genericPointWedgeFreeProductRightProjection
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1)
      (finiteWedgeSuccessorRightBaseElement n) = 1 at hp
  have hb1 : b = 1 := by
    simpa [ha, hb] using hp
  refine ⟨1, ?_⟩
  rw [hb, hb1]
  simp

/-- Thus the specialized connector square is sufficient for the complete
successor right-base factorization, using the two structural factor lemmas. -/
theorem finiteWedgeRightBaseInOldFactor_of_connectorSquare (n : ℕ)
    (h : finiteWedgeRightConnectorSquare n) :
    finiteWedgeRightBaseInOldFactor n :=
  finiteWedgeRightBaseInOldFactor_of_outerRightInOldFactor n
    (finiteWedgeSuccessorOuterRight_mem_inl_of_connectorSquare n h)

/-- Left-factor membership implies the connector square.  This is the valid
direction; trivial right projection alone does not characterize `inl`. -/
theorem finiteWedgeRightConnectorSquare_of_inOldFactor (n : ℕ)
    (h : finiteWedgeRightBaseInOldFactor n) :
    finiteWedgeRightConnectorSquare n := by
  rcases h with ⟨a, ha⟩
  apply (finiteWedgeRightProjection_eq_one_iff_connectorSquare n).mp
  exact ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightBase_inl_implies_rightProjection_eq_one
    _ _ _ _ _ _ _ _ _ _ a ha

/-- The structural left/right factorization upgrades the projection
calculation to the exact old-factor criterion needed for normalization. -/
theorem finiteWedgeRightBaseInOldFactor_iff_connectorSquare (n : ℕ) :
    finiteWedgeRightBaseInOldFactor n ↔ finiteWedgeRightConnectorSquare n :=
  ⟨finiteWedgeRightConnectorSquare_of_inOldFactor n,
    finiteWedgeRightBaseInOldFactor_of_connectorSquare n⟩

/-- Exact endpoint-transport criterion for the old-factor membership needed
by partial normalization. -/
theorem finiteWedgeRightBaseInOldFactor_iff_connectorTransport (n : ℕ) :
    finiteWedgeRightBaseInOldFactor n ↔ finiteWedgeRightConnectorTransport n :=
  (finiteWedgeRightBaseInOldFactor_iff_connectorSquare n).trans
    (finiteWedgeRightConnectorTransport_iff_connectorSquare n).symm

/-- The installed successor connector square holds: the overlap comparison
is literal endpoint transport in the right-piece connector system. -/
theorem finiteWedgeRightConnectorSystemComparison (n : ℕ) :
    finiteWedgeRightConnectorSquare n := by
  apply (finiteWedgeRightProjection_eq_one_iff_connectorSquare n).mp
  let P := finiteWedgeFinSuccPointWedgeNeighborhoods n
  let x₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1
  let y₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1
  exact ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightBase_rightProjection_eq_one
    x₀ y₀ P.2.carrier P.1.carrier P.2.isOpen P.1.isOpen
      P.2.mem P.1.mem P.2.contraction P.1.contraction

/-- The successor reconstruction conjugator lies in the old finite-wedge
factor, which is the hypothesis required by partial normalization. -/
theorem finiteWedgePointWedge_rightBase_inl (n : ℕ) :
    finiteWedgeRightBaseInOldFactor n :=
  finiteWedgeRightBaseInOldFactor_of_connectorSquare n
    (finiteWedgeRightConnectorSystemComparison n)

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

/-- At every successor split, the point-wedge fundamental group is generated
by words from the old finite wedge and the final one-circle wedge. -/
theorem finiteWedgeFinSuccPointWedge_exists_legWord (n : ℕ)
    (g : FundamentalGroup
      (ConstructionTargets.PointWedgeQuotient.Wedge
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1))
      (ConstructionTargets.PointWedgeQuotient.quotientMap
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1)
        (.inl (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
          (0 : Fin (n + 1)) 1)))) :
    ∃ w : List
        (FundamentalGroup
            (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin (n + 1)))
            (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1) ⊕
          FundamentalGroup
            (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge Unit)
            (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1)),
      coprodLegWordValue
          (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeLeftLegMap
            (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
            (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1))
          (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightLegMap
            (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
            (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1)) w = g := by
  let P := finiteWedgeFinSuccPointWedgeNeighborhoods n
  rcases finiteWedgePointWedge_rightBase_inl n with ⟨a, ha⟩
  exact genericPointWedge_exists_legWord_of_rightBase_inl
    _ _ P.2.carrier P.1.carrier P.2.isOpen P.1.isOpen
      P.2.mem P.1.mem P.2.contraction P.1.contraction a ha g

/-- A homeomorphism transports the based fundamental group.  This local
version keeps the successor-wedge induction independent of later closure
modules that use the same construction. -/
noncomputable def fundamentalGroupEquivOfHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) where
  toFun := FundamentalGroup.map ⟨e, e.continuous⟩ x
  invFun := FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩
    (e.symm_apply_apply x)
  left_inv p := by
    induction p using Path.Homotopic.Quotient.ind with
    | mk p =>
      rw [FundamentalGroup.map_apply]
      change (FundamentalGroup.mapOfEq _ _)
        (Path.Homotopic.Quotient.mk (p.map e.continuous)) = _
      rw [FundamentalGroup.mapOfEq_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl p using 1
      ext t
      exact e.symm_apply_apply (p t)
  right_inv p := by
    induction p using Path.Homotopic.Quotient.ind with
    | mk p =>
      rw [FundamentalGroup.mapOfEq_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl p using 1
      ext t
      exact e.apply_symm_apply (p t)
  map_mul' := map_mul _

/-- The successor splitting homeomorphism, including its basepoint
identification, induces the based fundamental-group equivalence used to pull
point-wedge words back to the finite wedge. -/
noncomputable def finiteWedgeFinSuccFundamentalGroupEquiv (n : ℕ) :
    FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin ((n + 1) + 1)))
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
          (0 : Fin ((n + 1) + 1)) 1) ≃*
      FundamentalGroup
        (ConstructionTargets.PointWedgeQuotient.Wedge
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1))
        (ConstructionTargets.PointWedgeQuotient.quotientMap
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1)
          (.inl (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
            (0 : Fin (n + 1)) 1))) := by
  let e := finiteWedgeFinSuccHomeomorphPointWedge n
  have he : e (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
      (0 : Fin ((n + 1) + 1)) 1) =
      ConstructionTargets.PointWedgeQuotient.quotientMap
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1)
        (.inl (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
          (0 : Fin (n + 1)) 1)) := by
    simpa using finiteWedgeFinSuccHomeomorphPointWedge_castSucc n
      (0 : Fin (n + 1)) 1
  rw [← he]
  exact fundamentalGroupEquivOfHomeomorph e _

/-- The old-wedge inclusion into a successor wedge, obtained by pulling the
literal left point-wedge leg back through the splitting homeomorphism. -/
noncomputable def finiteWedgeFinSuccOldInclusion (n : ℕ) : C(
    PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin (n + 1)),
    PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin ((n + 1) + 1))) :=
  ⟨fun x => (finiteWedgeFinSuccHomeomorphPointWedge n).symm
      (ConstructionTargets.PointWedgeQuotient.quotientMap
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1) (.inl x)),
    (finiteWedgeFinSuccHomeomorphPointWedge n).symm.continuous.comp
      ((ConstructionTargets.PointWedgeQuotient.continuous_quotientMap _ _).comp
        continuous_inl)⟩

/-- The final-circle inclusion into a successor wedge, pulled back from the
literal right point-wedge leg. -/
noncomputable def finiteWedgeFinSuccLastInclusion (n : ℕ) : C(
    PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge Unit,
    PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin ((n + 1) + 1))) :=
  ⟨fun x => (finiteWedgeFinSuccHomeomorphPointWedge n).symm
      (ConstructionTargets.PointWedgeQuotient.quotientMap
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1) (.inr x)),
    (finiteWedgeFinSuccHomeomorphPointWedge n).symm.continuous.comp
      ((ConstructionTargets.PointWedgeQuotient.continuous_quotientMap _ _).comp
        continuous_inr)⟩

@[simp]
theorem finiteWedgeFinSuccOldInclusion_wedgeCircle (n : ℕ)
    (i : Fin (n + 1)) (z : Circle) :
    finiteWedgeFinSuccOldInclusion n
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle i z) =
      PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle i.castSucc z := by
  apply (finiteWedgeFinSuccHomeomorphPointWedge n).injective
  simp [finiteWedgeFinSuccOldInclusion]

@[simp]
theorem finiteWedgeFinSuccLastInclusion_wedgeCircle (n : ℕ) (z : Circle) :
    finiteWedgeFinSuccLastInclusion n
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () z) =
      PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (Fin.last (n + 1)) z := by
  apply (finiteWedgeFinSuccHomeomorphPointWedge n).injective
  simp [finiteWedgeFinSuccLastInclusion]

/-- The old-factor inclusion is based at the common zeroth-circle point. -/
theorem finiteWedgeFinSuccOldInclusion_base (n : ℕ) :
    finiteWedgeFinSuccOldInclusion n
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1) =
      PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
        (0 : Fin ((n + 1) + 1)) 1 := by
  simpa using finiteWedgeFinSuccOldInclusion_wedgeCircle n (0 : Fin (n + 1)) 1

/-- The final-factor inclusion has the same common wedge basepoint. -/
theorem finiteWedgeFinSuccLastInclusion_base (n : ℕ) :
    finiteWedgeFinSuccLastInclusion n
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1) =
      PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
        (0 : Fin ((n + 1) + 1)) 1 := by
  rw [finiteWedgeFinSuccLastInclusion_wedgeCircle]
  exact PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle_base_eq _ _

/-- The old factor's based fundamental-group map into the successor wedge. -/
noncomputable def finiteWedgeFinSuccOldFundamentalGroupMap (n : ℕ) :
    FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin (n + 1)))
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1) →*
      FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin ((n + 1) + 1)))
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
          (0 : Fin ((n + 1) + 1)) 1) :=
  FundamentalGroup.mapOfEq (finiteWedgeFinSuccOldInclusion n)
    (finiteWedgeFinSuccOldInclusion_base n)

/-- The final factor's based fundamental-group map into the successor wedge. -/
noncomputable def finiteWedgeFinSuccLastFundamentalGroupMap (n : ℕ) :
    FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge Unit)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1) →*
      FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin ((n + 1) + 1)))
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
          (0 : Fin ((n + 1) + 1)) 1) :=
  FundamentalGroup.mapOfEq (finiteWedgeFinSuccLastInclusion n)
    (finiteWedgeFinSuccLastInclusion_base n)

/-- An arbitrary circle loop inserted in the `i`th leg of a standard finite
wedge and transported to its common zeroth-leg basepoint. -/
noncomputable def finiteWedgeFinLegMap (n : ℕ) (i : Fin (n + 1)) :
    FundamentalGroup Circle 1 →*
      FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin (n + 1)))
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1) :=
  FundamentalGroup.mapOfEq
    ⟨PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle i,
      PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle i⟩
    (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle_base_eq i 0)

/-- An arbitrary circle loop inserted in the unique leg of the `Unit`-indexed
wedge, at its literal basepoint. -/
noncomputable def finiteWedgeUnitLegMap :
    FundamentalGroup Circle 1 →*
      FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge Unit)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1) :=
  FundamentalGroup.map
    ⟨PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (),
      PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle ()⟩ 1

/-- The arbitrary-loop leg map is the literal leg map followed by the common
basepoint cast. -/
theorem finiteWedgeFinLegMap_apply (n : ℕ) (i : Fin (n + 1))
    (g : FundamentalGroup Circle 1) :
    finiteWedgeFinLegMap n i g =
      Path.Homotopic.Quotient.cast
        (FundamentalGroup.map
          ⟨PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle i,
            PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle i⟩ 1 g)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle_base_eq 0 i)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle_base_eq 0 i) := by
  induction g using Path.Homotopic.Quotient.ind with
  | mk p =>
      rw [finiteWedgeFinLegMap, FundamentalGroup.mapOfEq_apply,
        FundamentalGroup.map_apply]
      rfl

/-- The arbitrary-loop leg map specializes to the previously fixed positive
fundamental class. -/
theorem finiteWedgeFinLegMap_positive (n : ℕ) (i : Fin (n + 1)) :
    finiteWedgeFinLegMap n i circlePositiveFundamentalClass =
      Path.Homotopic.Quotient.cast (finiteWedgeLegFundamentalClass i)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle_base_eq 0 i)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle_base_eq 0 i) := by
  exact finiteWedgeFinLegMap_apply n i circlePositiveFundamentalClass

/-- Words whose letters are arbitrary circle loops assigned to finite-wedge
labels.  Integer-exponent words arise later by circle generation. -/
abbrev FiniteWedgeFinLoopWord (n : ℕ) :=
  List (Fin (n + 1) × FundamentalGroup Circle 1)

/-- Evaluate an arbitrary-loop leg word at the common finite-wedge basepoint. -/
noncomputable def finiteWedgeFinLoopWordValue (n : ℕ)
    (w : FiniteWedgeFinLoopWord n) :
    FundamentalGroup
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin (n + 1)))
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1) :=
  (w.map fun q => finiteWedgeFinLegMap n q.1 q.2).prod

/-- The installed old-factor map preserves arbitrary loop letters and sends
their labels through `Fin.castSucc`. -/
theorem finiteWedgeFinSuccOldFundamentalGroupMap_leg (n : ℕ)
    (i : Fin (n + 1)) (g : FundamentalGroup Circle 1) :
    finiteWedgeFinSuccOldFundamentalGroupMap n (finiteWedgeFinLegMap n i g) =
      finiteWedgeFinLegMap (n + 1) i.castSucc g := by
  induction g using Path.Homotopic.Quotient.ind with
  | mk p =>
      rw [finiteWedgeFinLegMap, finiteWedgeFinSuccOldFundamentalGroupMap,
        FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply,
        finiteWedgeFinLegMap, FundamentalGroup.mapOfEq_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl
        ((p.map (PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle
          i.castSucc)).cast _ _) using 1

/-- The installed final-factor map preserves arbitrary loop letters and sends
the unique label to `Fin.last`. -/
theorem finiteWedgeFinSuccLastFundamentalGroupMap_leg (n : ℕ)
    (g : FundamentalGroup Circle 1) :
    finiteWedgeFinSuccLastFundamentalGroupMap n (finiteWedgeUnitLegMap g) =
      finiteWedgeFinLegMap (n + 1) (Fin.last (n + 1)) g := by
  induction g using Path.Homotopic.Quotient.ind with
  | mk p =>
      rw [finiteWedgeUnitLegMap, FundamentalGroup.map_apply,
        finiteWedgeFinSuccLastFundamentalGroupMap]
      change (FundamentalGroup.mapOfEq (finiteWedgeFinSuccLastInclusion n) _)
          (Path.Homotopic.Quotient.mk
            (p.map (PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle ()))) = _
      rw [FundamentalGroup.mapOfEq_apply, finiteWedgeFinLegMap,
        FundamentalGroup.mapOfEq_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl
        ((p.map (PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle
          (Fin.last (n + 1)))).cast _ _) using 1

/-- Mapping the installed old-factor inclusion across the splitting
homeomorphism recovers the literal left point-wedge leg map. -/
theorem finiteWedgeFinSuccOldFundamentalGroupMap_comparison (n : ℕ)
    (a : FundamentalGroup
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin (n + 1)))
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)) :
    finiteWedgeFinSuccFundamentalGroupEquiv n
        (finiteWedgeFinSuccOldFundamentalGroupMap n a) =
      ConstructionTargets.PointWedgeVanKampen.genericPointWedgeLeftLegMap
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1) a := by
  induction a using Path.Homotopic.Quotient.ind with
  | mk p =>
      rw [finiteWedgeFinSuccOldFundamentalGroupMap,
        FundamentalGroup.mapOfEq_apply]
      change finiteWedgeFinSuccFundamentalGroupEquiv n
          (Path.Homotopic.Quotient.mk
            ((p.map (finiteWedgeFinSuccOldInclusion n).continuous).cast _ _)) = _
      change FundamentalGroup.map
          ⟨finiteWedgeFinSuccHomeomorphPointWedge n,
            (finiteWedgeFinSuccHomeomorphPointWedge n).continuous⟩ _
          (Path.Homotopic.Quotient.mk
            ((p.map (finiteWedgeFinSuccOldInclusion n).continuous).cast _ _)) = _
      rw [FundamentalGroup.map_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl
        (p.map (ConstructionTargets.PointWedgePointedContractionDescent.includeLeft
          (x₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
            (0 : Fin (n + 1)) 1)
          (y₀ := PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1)).continuous) using 1
      ext t
      change finiteWedgeFinSuccHomeomorphPointWedge n
          (((p.map (finiteWedgeFinSuccOldInclusion n).continuous).cast _ _) t) = _
      rw [show ((p.map (finiteWedgeFinSuccOldInclusion n).continuous).cast _ _) t =
          (p.map (finiteWedgeFinSuccOldInclusion n).continuous) t by
        exact congrFun (Path.cast_coe _ _ _) t]
      change finiteWedgeFinSuccHomeomorphPointWedge n
          (finiteWedgeFinSuccOldInclusion n (p t)) =
        ConstructionTargets.PointWedgeQuotient.quotientMap
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1) (.inl (p t))
      simp [finiteWedgeFinSuccOldInclusion]

/-- In the pullback orientation used by the split-word theorem, the literal
left leg is exactly the installed old-factor map. -/
theorem finiteWedgeFinSuccOldFundamentalGroupMap_eq_transport (n : ℕ)
    (a : FundamentalGroup
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin (n + 1)))
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)) :
    (finiteWedgeFinSuccFundamentalGroupEquiv n).symm
        (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeLeftLegMap
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1) a) =
      finiteWedgeFinSuccOldFundamentalGroupMap n a := by
  apply (finiteWedgeFinSuccFundamentalGroupEquiv n).injective
  rw [MulEquiv.apply_symm_apply,
    finiteWedgeFinSuccOldFundamentalGroupMap_comparison]

/-- Mapping the installed final-factor inclusion across the splitting
homeomorphism recovers the literal right point-wedge leg map, including its
quotient basepoint transport. -/
theorem finiteWedgeFinSuccLastFundamentalGroupMap_comparison (n : ℕ)
    (a : FundamentalGroup
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge Unit)
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1)) :
    finiteWedgeFinSuccFundamentalGroupEquiv n
        (finiteWedgeFinSuccLastFundamentalGroupMap n a) =
      ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightLegMap
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1) a := by
  induction a using Path.Homotopic.Quotient.ind with
  | mk p =>
      rw [finiteWedgeFinSuccLastFundamentalGroupMap,
        FundamentalGroup.mapOfEq_apply]
      change finiteWedgeFinSuccFundamentalGroupEquiv n
          (Path.Homotopic.Quotient.mk
            ((p.map (finiteWedgeFinSuccLastInclusion n).continuous).cast _ _)) = _
      change FundamentalGroup.map
          ⟨finiteWedgeFinSuccHomeomorphPointWedge n,
            (finiteWedgeFinSuccHomeomorphPointWedge n).continuous⟩ _
          (Path.Homotopic.Quotient.mk
            ((p.map (finiteWedgeFinSuccLastInclusion n).continuous).cast _ _)) = _
      rw [FundamentalGroup.map_apply,
        ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightLegMap,
        FundamentalGroup.mapOfEq_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl
        ((p.map ((ConstructionTargets.PointWedgeQuotient.continuous_quotientMap
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1)).comp
            continuous_inr)).cast _ _) using 1
      ext t
      change finiteWedgeFinSuccHomeomorphPointWedge n
          (((p.map (finiteWedgeFinSuccLastInclusion n).continuous).cast _ _) t) = _
      rw [show ((p.map (finiteWedgeFinSuccLastInclusion n).continuous).cast _ _) t =
          (p.map (finiteWedgeFinSuccLastInclusion n).continuous) t by
        exact congrFun (Path.cast_coe _ _ _) t]
      rw [show ((p.map ((ConstructionTargets.PointWedgeQuotient.continuous_quotientMap
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1)).comp
            continuous_inr)).cast _ _) t =
          (p.map ((ConstructionTargets.PointWedgeQuotient.continuous_quotientMap
            (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
            (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1)).comp
              continuous_inr)) t by
        exact congrFun (Path.cast_coe _ _ _) t]
      change finiteWedgeFinSuccHomeomorphPointWedge n
          (finiteWedgeFinSuccLastInclusion n (p t)) =
        ConstructionTargets.PointWedgeQuotient.quotientMap
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1) (.inr (p t))
      simp [finiteWedgeFinSuccLastInclusion]

/-- In the pullback orientation used by the split-word theorem, the literal
right leg is exactly the installed final-factor map. -/
theorem finiteWedgeFinSuccLastFundamentalGroupMap_eq_transport (n : ℕ)
    (a : FundamentalGroup
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge Unit)
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1)) :
    (finiteWedgeFinSuccFundamentalGroupEquiv n).symm
        (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightLegMap
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1) a) =
      finiteWedgeFinSuccLastFundamentalGroupMap n a := by
  apply (finiteWedgeFinSuccFundamentalGroupEquiv n).injective
  rw [MulEquiv.apply_symm_apply,
    finiteWedgeFinSuccLastFundamentalGroupMap_comparison]

/-- Pulling the point-wedge word theorem through the successor homeomorphism
gives a word theorem on the finite wedge.  Its letters are still grouped into
the old wedge and final circle; the next induction step expands the old
letters into individually labelled circle legs. -/
theorem finiteWedgeFinSucc_exists_splitLegWord (n : ℕ)
    (g : FundamentalGroup
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin ((n + 1) + 1)))
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
        (0 : Fin ((n + 1) + 1)) 1)) :
    ∃ w : List
        (FundamentalGroup
            (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin (n + 1)))
            (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1) ⊕
          FundamentalGroup
            (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge Unit)
            (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1)),
      coprodLegWordValue
          (fun a => (finiteWedgeFinSuccFundamentalGroupEquiv n).symm
            (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeLeftLegMap
              (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
              (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1) a))
          (fun b => (finiteWedgeFinSuccFundamentalGroupEquiv n).symm
            (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightLegMap
              (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
              (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1) b)) w = g := by
  rcases finiteWedgeFinSuccPointWedge_exists_legWord n
      (finiteWedgeFinSuccFundamentalGroupEquiv n g) with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  apply (finiteWedgeFinSuccFundamentalGroupEquiv n).injective
  calc
    finiteWedgeFinSuccFundamentalGroupEquiv n
        (coprodLegWordValue
          (fun a => (finiteWedgeFinSuccFundamentalGroupEquiv n).symm
            (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeLeftLegMap
              (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
              (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1) a))
          (fun b => (finiteWedgeFinSuccFundamentalGroupEquiv n).symm
            (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightLegMap
              (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
              (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1) b)) w) =
        coprodLegWordValue
          (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeLeftLegMap
            (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
            (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1))
          (ConstructionTargets.PointWedgeVanKampen.genericPointWedgeRightLegMap
            (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)
            (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1)) w := by
          clear hw g
          induction w with
          | nil => simp [coprodLegWordValue]
          | cons x w ih =>
              cases x <;>
                simp only [coprodLegWordValue, List.map_cons, List.prod_cons,
                  map_mul, Sum.elim_inl, Sum.elim_inr] <;>
                change _ * (finiteWedgeFinSuccFundamentalGroupEquiv n)
                    (coprodLegWordValue _ _ w) = _ * coprodLegWordValue _ _ w <;>
                rw [MulEquiv.apply_symm_apply, ih]
    _ = finiteWedgeFinSuccFundamentalGroupEquiv n g := hw

/-- The transported split word can be stated entirely with the installed
old- and final-factor maps on the successor finite wedge. -/
theorem finiteWedgeFinSucc_exists_installedSplitLegWord (n : ℕ)
    (g : FundamentalGroup
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin ((n + 1) + 1)))
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
        (0 : Fin ((n + 1) + 1)) 1)) :
    ∃ w : List
        (FundamentalGroup
            (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin (n + 1)))
            (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1) ⊕
          FundamentalGroup
            (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge Unit)
            (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1)),
      coprodLegWordValue
          (finiteWedgeFinSuccOldFundamentalGroupMap n)
          (finiteWedgeFinSuccLastFundamentalGroupMap n) w = g := by
  rcases finiteWedgeFinSucc_exists_splitLegWord n g with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  simpa only [finiteWedgeFinSuccOldFundamentalGroupMap_eq_transport,
    finiteWedgeFinSuccLastFundamentalGroupMap_eq_transport] using hw

/-- The one-leg finite wedge has the based fundamental group of the circle. -/
noncomputable def finiteWedgeFinOneFundamentalGroupEquiv :
    FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin 1))
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin 1) 1) ≃*
      FundamentalGroup Circle 1 := by
  simpa [finiteWedgeFinOneHomeomorphCircle] using
    (fundamentalGroupEquivOfHomeomorph finiteWedgeFinOneHomeomorphCircle
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin 1) 1))

/-- Under the one-circle identification, the unique arbitrary-loop leg map
is the identity map on the circle fundamental group. -/
theorem finiteWedgeFinOneFundamentalGroupEquiv_leg
    (g : FundamentalGroup Circle 1) :
    finiteWedgeFinOneFundamentalGroupEquiv (finiteWedgeFinLegMap 0 0 g) = g := by
  induction g using Path.Homotopic.Quotient.ind with
  | mk p =>
      rw [finiteWedgeFinLegMap, FundamentalGroup.mapOfEq_apply]
      change FundamentalGroup.map
          ⟨finiteWedgeFinOneHomeomorphCircle,
            finiteWedgeFinOneHomeomorphCircle.continuous⟩ _
          (Path.Homotopic.Quotient.mk
            ((p.map
              (PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle
                (0 : Fin 1))).cast _ _)) = _
      rw [FundamentalGroup.map_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl p using 1

/-- Every loop on the one-leg finite wedge is a one-letter labelled leg word. -/
theorem finiteWedgeFinOne_exists_legWord
    (g : FundamentalGroup
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin 1))
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin 1) 1)) :
    ∃ w : FiniteWedgeFinLoopWord 0,
      finiteWedgeFinLoopWordValue 0 w = g := by
  refine ⟨[((0 : Fin 1), finiteWedgeFinOneFundamentalGroupEquiv g)], ?_⟩
  apply finiteWedgeFinOneFundamentalGroupEquiv.injective
  simp [finiteWedgeFinLoopWordValue,
    finiteWedgeFinOneFundamentalGroupEquiv_leg]

/-- The uniquely labelled `Unit` wedge has the based fundamental group of the
circle. -/
noncomputable def finiteWedgeUnitFundamentalGroupEquiv :
    FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge Unit)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1) ≃*
      FundamentalGroup Circle 1 := by
  simpa using
    (fundamentalGroupEquivOfHomeomorph
      (finiteWedgeSubsingletonHomeomorphCircle ())
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1))

theorem finiteWedgeUnitFundamentalGroupEquiv_leg
    (g : FundamentalGroup Circle 1) :
    finiteWedgeUnitFundamentalGroupEquiv (finiteWedgeUnitLegMap g) = g := by
  induction g using Path.Homotopic.Quotient.ind with
  | mk p =>
      rw [finiteWedgeUnitLegMap, FundamentalGroup.map_apply]
      change FundamentalGroup.map
          ⟨finiteWedgeSubsingletonHomeomorphCircle (),
            (finiteWedgeSubsingletonHomeomorphCircle ()).continuous⟩ _
          (Path.Homotopic.Quotient.mk
            (p.map
              (PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle ()))) = _
      rw [FundamentalGroup.map_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl p using 1

/-- Every loop in the final `Unit` factor is an arbitrary circle-loop leg. -/
theorem finiteWedgeUnitLegMap_surjective
    (g : FundamentalGroup
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge Unit)
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1)) :
    ∃ a, finiteWedgeUnitLegMap a = g := by
  refine ⟨finiteWedgeUnitFundamentalGroupEquiv g, ?_⟩
  apply finiteWedgeUnitFundamentalGroupEquiv.injective
  simp [finiteWedgeUnitFundamentalGroupEquiv_leg]

/-- Relabelling an old-factor word by `Fin.castSucc` realizes its image under
the installed old-factor map. -/
theorem finiteWedgeFinSucc_oldLoopWordValue (n : ℕ)
    (w : FiniteWedgeFinLoopWord n) :
    finiteWedgeFinLoopWordValue (n + 1)
        (w.map fun q => (q.1.castSucc, q.2)) =
      finiteWedgeFinSuccOldFundamentalGroupMap n
        (finiteWedgeFinLoopWordValue n w) := by
  induction w with
  | nil => simp [finiteWedgeFinLoopWordValue]
  | cons q w ih =>
      simp only [List.map_cons, finiteWedgeFinLoopWordValue, List.prod_cons,
        map_mul]
      rw [finiteWedgeFinSuccOldFundamentalGroupMap_leg]
      change finiteWedgeFinLegMap (n + 1) q.1.castSucc q.2 *
          finiteWedgeFinLoopWordValue (n + 1)
            (w.map fun q => (q.1.castSucc, q.2)) =
        finiteWedgeFinLegMap (n + 1) q.1.castSucc q.2 *
          finiteWedgeFinSuccOldFundamentalGroupMap n
            (finiteWedgeFinLoopWordValue n w)
      rw [ih]

/-- Substitute labelled words for every old/final letter of an installed
successor split word. -/
theorem finiteWedgeFinSucc_expand_splitWord (n : ℕ)
    (hold : ∀ g, ∃ w : FiniteWedgeFinLoopWord n,
      finiteWedgeFinLoopWordValue n w = g)
    (w : List
      (FundamentalGroup
          (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin (n + 1)))
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1) ⊕
        FundamentalGroup
          (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge Unit)
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1))) :
    ∃ v : FiniteWedgeFinLoopWord (n + 1),
      finiteWedgeFinLoopWordValue (n + 1) v =
        coprodLegWordValue
          (finiteWedgeFinSuccOldFundamentalGroupMap n)
          (finiteWedgeFinSuccLastFundamentalGroupMap n) w := by
  induction w with
  | nil =>
      refine ⟨[], ?_⟩
      simp [finiteWedgeFinLoopWordValue, coprodLegWordValue]
  | cons q w ih =>
      rcases ih with ⟨vw, hvw⟩
      cases q with
      | inl a =>
          rcases hold a with ⟨wa, hwa⟩
          refine ⟨(wa.map fun q => (q.1.castSucc, q.2)) ++ vw, ?_⟩
          rw [finiteWedgeFinLoopWordValue, List.map_append, List.prod_append]
          change finiteWedgeFinLoopWordValue (n + 1)
              (wa.map fun q => (q.1.castSucc, q.2)) *
              finiteWedgeFinLoopWordValue (n + 1) vw = _
          rw [finiteWedgeFinSucc_oldLoopWordValue, hwa, hvw]
          rfl
      | inr b =>
          rcases finiteWedgeUnitLegMap_surjective b with ⟨a, ha⟩
          refine ⟨((Fin.last (n + 1), a) :: vw), ?_⟩
          simp only [finiteWedgeFinLoopWordValue, List.map_cons, List.prod_cons]
          rw [← finiteWedgeFinSuccLastFundamentalGroupMap_leg n a, ha]
          change finiteWedgeFinSuccLastFundamentalGroupMap n b *
              finiteWedgeFinLoopWordValue (n + 1) vw =
            finiteWedgeFinSuccLastFundamentalGroupMap n b *
              coprodLegWordValue
                (finiteWedgeFinSuccOldFundamentalGroupMap n)
                (finiteWedgeFinSuccLastFundamentalGroupMap n) w
          rw [hvw]

/-- If old finite-wedge loops have labelled words, successor loops do too. -/
theorem finiteWedgeFinSucc_exists_legWord (n : ℕ)
    (hold : ∀ g, ∃ w : FiniteWedgeFinLoopWord n,
      finiteWedgeFinLoopWordValue n w = g)
    (g : FundamentalGroup
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin ((n + 1) + 1)))
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
        (0 : Fin ((n + 1) + 1)) 1)) :
    ∃ w : FiniteWedgeFinLoopWord (n + 1),
      finiteWedgeFinLoopWordValue (n + 1) w = g := by
  rcases finiteWedgeFinSucc_exists_installedSplitLegWord n g with ⟨w, hw⟩
  rcases finiteWedgeFinSucc_expand_splitWord n hold w with ⟨v, hv⟩
  exact ⟨v, hv.trans hw⟩

/-- Every loop in a nonempty standard finite wedge is a finite word in its
individually labelled circle legs. -/
theorem finiteWedgeFin_exists_legWord (n : ℕ)
    (g : FundamentalGroup
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin (n + 1)))
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)) :
    ∃ w : FiniteWedgeFinLoopWord n,
      finiteWedgeFinLoopWordValue n w = g := by
  induction n with
  | zero => exact finiteWedgeFinOne_exists_legWord g
  | succ n ih => exact finiteWedgeFinSucc_exists_legWord n ih g

/-- Integer-exponent words in the positive generators of a standard finite
wedge. -/
abbrev FiniteWedgeFinGeneratorWord (n : ℕ) := List (Fin (n + 1) × ℤ)

noncomputable def finiteWedgeFinGeneratorWordValue (n : ℕ)
    (w : FiniteWedgeFinGeneratorWord n) :
    FundamentalGroup
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin (n + 1)))
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1) :=
  (w.map fun q =>
    finiteWedgeFinLegMap n q.1 circlePositiveFundamentalClass ^ q.2).prod

/-- Replace every arbitrary circle-loop letter by an integer power of the
fixed positive circle class. -/
theorem finiteWedgeFinLoopWord_exists_generatorWord (n : ℕ)
    (w : FiniteWedgeFinLoopWord n) :
    ∃ u : FiniteWedgeFinGeneratorWord n,
      finiteWedgeFinGeneratorWordValue n u =
        finiteWedgeFinLoopWordValue n w := by
  induction w with
  | nil =>
      exact ⟨[], by simp [finiteWedgeFinGeneratorWordValue,
        finiteWedgeFinLoopWordValue]⟩
  | cons q w ih =>
      rcases circlePositiveFundamentalClass_generates q.2 with ⟨z, hz⟩
      rcases ih with ⟨u, hu⟩
      refine ⟨(q.1, z) :: u, ?_⟩
      simp only [finiteWedgeFinGeneratorWordValue, finiteWedgeFinLoopWordValue,
        List.map_cons, List.prod_cons]
      rw [← map_zpow, hz]
      change finiteWedgeFinLegMap n q.1 q.2 *
          finiteWedgeFinGeneratorWordValue n u =
        finiteWedgeFinLegMap n q.1 q.2 * finiteWedgeFinLoopWordValue n w
      rw [hu]

/-- Every finite-wedge loop is an integer-exponent word in the fixed positive
leg generators. -/
theorem finiteWedgeFin_exists_generatorWord (n : ℕ)
    (g : FundamentalGroup
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin (n + 1)))
      (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1)) :
    ∃ w : FiniteWedgeFinGeneratorWord n,
      finiteWedgeFinGeneratorWordValue n w = g := by
  rcases finiteWedgeFin_exists_legWord n g with ⟨w, hw⟩
  rcases finiteWedgeFinLoopWord_exists_generatorWord n w with ⟨u, hu⟩
  exact ⟨u, hu.trans hw⟩

/-- The canonical free-group map for the standard `Fin`-labelled wedge. -/
noncomputable def finiteWedgeFinLegFreeGroupMap (n : ℕ) :
    FreeGroup (Fin (n + 1)) →*
      FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin (n + 1)))
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (n + 1)) 1) :=
  FreeGroup.lift (fun i =>
    finiteWedgeFinLegMap n i circlePositiveFundamentalClass)

/-- A generator word is the image of the corresponding product in the free
group. -/
theorem finiteWedgeFinGeneratorWord_in_freeGroupImage (n : ℕ)
    (w : FiniteWedgeFinGeneratorWord n) :
    ∃ x : FreeGroup (Fin (n + 1)),
      finiteWedgeFinLegFreeGroupMap n x =
        finiteWedgeFinGeneratorWordValue n w := by
  induction w with
  | nil => exact ⟨1, by simp [finiteWedgeFinGeneratorWordValue]⟩
  | cons q w ih =>
      rcases ih with ⟨x, hx⟩
      refine ⟨FreeGroup.of q.1 ^ q.2 * x, ?_⟩
      rw [map_mul, map_zpow, hx]
      simp [finiteWedgeFinLegFreeGroupMap,
        finiteWedgeFinGeneratorWordValue]

/-- The canonical free-group map onto a nonempty finite circle wedge is
surjective. -/
theorem finiteWedgeFinLegFreeGroupMap_surjective (n : ℕ) :
    Function.Surjective (finiteWedgeFinLegFreeGroupMap n) := by
  intro g
  rcases finiteWedgeFin_exists_generatorWord n g with ⟨w, hw⟩
  rcases finiteWedgeFinGeneratorWord_in_freeGroupImage n w with ⟨x, hx⟩
  exact ⟨x, hx.trans hw⟩

/-- The same leg map indexed by an arbitrary positive finite cardinal, with
its proof-carrying zero coordinate made explicit. -/
noncomputable def finiteWedgeFinLegMapCard (N : ℕ) (hN : 0 < N)
    (i : Fin N) :
    FundamentalGroup Circle 1 →*
      FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin N))
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle ⟨0, hN⟩ 1) :=
  FundamentalGroup.mapOfEq
    ⟨PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle i,
      PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle i⟩
    (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle_base_eq i ⟨0, hN⟩)

noncomputable def finiteWedgeFinLegFreeGroupMapCard (N : ℕ) (hN : 0 < N) :
    FreeGroup (Fin N) →*
      FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin N))
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle ⟨0, hN⟩ 1) :=
  FreeGroup.lift (fun i =>
    finiteWedgeFinLegMapCard N hN i circlePositiveFundamentalClass)

/-- Surjectivity in the proof-carrying positive-cardinality presentation. -/
theorem finiteWedgeFinLegFreeGroupMapCard_surjective (N : ℕ) (hN : 0 < N) :
    Function.Surjective (finiteWedgeFinLegFreeGroupMapCard N hN) := by
  cases N with
  | zero => omega
  | succ n =>
      simpa [finiteWedgeFinLegFreeGroupMapCard, finiteWedgeFinLegMapCard,
        finiteWedgeFinLegFreeGroupMap, finiteWedgeFinLegMap] using
        finiteWedgeFinLegFreeGroupMap_surjective n

/-- A finite coordinate labelling chosen so that the polygon's distinguished
orbit is sent to coordinate zero. -/
theorem pairingOrbitCard_pos (P : PairingData) :
    0 < Fintype.card (PairingOrbit P.pair) :=
  Fintype.card_pos_iff.mpr ⟨P.orbit ⟨0, P.edgeCount_pos⟩⟩

def pairingOrbitFinZero (P : PairingData) :
    Fin (Fintype.card (PairingOrbit P.pair)) :=
  ⟨0, pairingOrbitCard_pos P⟩

noncomputable def pairingOrbitEquivFinZero (P : PairingData) :
    PairingOrbit P.pair ≃ Fin (Fintype.card (PairingOrbit P.pair)) :=
  (Fintype.equivFin (PairingOrbit P.pair)).trans
    (Equiv.swap
      (Fintype.equivFin (PairingOrbit P.pair)
        (P.orbit ⟨0, P.edgeCount_pos⟩)) (pairingOrbitFinZero P))

@[simp]
theorem pairingOrbitEquivFinZero_base (P : PairingData) :
    pairingOrbitEquivFinZero P (P.orbit ⟨0, P.edgeCount_pos⟩) =
      pairingOrbitFinZero P := by
  simp [pairingOrbitEquivFinZero]

/-- Relabel the orbit-indexed wedge while preserving the selected based
fundamental-group point exactly. -/
noncomputable def finiteWedgeOrbitHomeomorphFinZero (P : PairingData) :
    PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (PairingOrbit P.pair) ≃ₜ
      PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
        (Fin (Fintype.card (PairingOrbit P.pair))) :=
  finiteWedgeHomeomorphOfEquiv (pairingOrbitEquivFinZero P)

@[simp]
theorem finiteWedgeOrbitHomeomorphFinZero_wedgeCircle (P : PairingData)
    (l : PairingOrbit P.pair) (z : Circle) :
    finiteWedgeOrbitHomeomorphFinZero P
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l z) =
      PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
        (pairingOrbitEquivFinZero P l) z := rfl

theorem finiteWedgeOrbitHomeomorphFinZero_base (P : PairingData) :
    finiteWedgeOrbitHomeomorphFinZero P (orbitWedgeBase P) =
      PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
        (pairingOrbitFinZero P) 1 := by
  simp [orbitWedgeBase]

/-- The based fundamental group of the orbit-indexed wedge transported to
finite coordinates with the distinguished orbit at zero. -/
noncomputable def finiteWedgeOrbitFundamentalGroupEquivFin (P : PairingData) :
    FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (PairingOrbit P.pair))
        (orbitWedgeBase P) ≃*
      FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
          (Fin (Fintype.card (PairingOrbit P.pair))))
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
          (pairingOrbitFinZero P) 1) := by
  let e := finiteWedgeOrbitHomeomorphFinZero P
  have he : e (orbitWedgeBase P) =
      PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
        (pairingOrbitFinZero P) 1 :=
    finiteWedgeOrbitHomeomorphFinZero_base P
  rw [← he]
  exact fundamentalGroupEquivOfHomeomorph e (orbitWedgeBase P)

/-- A homeomorphism with a separately specified target basepoint induces a
group equivalence whose forward map is definitionally `mapOfEq`. -/
noncomputable def fundamentalGroupEquivOfHomeomorphEq
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) (y : Y) (h : e x = y) :
    FundamentalGroup X x ≃* FundamentalGroup Y y := by
  have hs : e.symm y = x := by rw [← h, e.symm_apply_apply]
  exact
    { toFun := FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ h
      invFun := FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩ hs
      left_inv := by
        intro p
        induction p using Path.Homotopic.Quotient.ind with
        | mk p =>
            rw [FundamentalGroup.mapOfEq_apply,
              FundamentalGroup.mapOfEq_apply]
            apply Path.Homotopic.Quotient.eq.mpr
            convert Path.Homotopic.refl p using 1
            ext t
            rw [show (((p.map e.continuous).cast _ _).map
                e.symm.continuous).cast _ _ t =
                e.symm (e (p t)) by
              rw [congrFun (Path.cast_coe _ _ _) t]
              change e.symm (((p.map e.continuous).cast _ _) t) = _
              rw [congrFun (Path.cast_coe _ _ _) t]
              rfl]
            exact e.symm_apply_apply (p t)
      right_inv := by
        intro p
        induction p using Path.Homotopic.Quotient.ind with
        | mk p =>
            rw [FundamentalGroup.mapOfEq_apply,
              FundamentalGroup.mapOfEq_apply]
            apply Path.Homotopic.Quotient.eq.mpr
            convert Path.Homotopic.refl p using 1
            ext t
            rw [show (((p.map e.symm.continuous).cast _ _).map
                e.continuous).cast _ _ t =
                e (e.symm (p t)) by
              rw [congrFun (Path.cast_coe _ _ _) t]
              change e (((p.map e.symm.continuous).cast _ _) t) = _
              rw [congrFun (Path.cast_coe _ _ _) t]
              rfl]
            exact e.apply_symm_apply (p t)
      map_mul' := map_mul _ }

/-- The orbit relabelling equivalence in the explicit based-map presentation. -/
noncomputable def finiteWedgeOrbitFundamentalGroupEquivFinExplicit
    (P : PairingData) :
    FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (PairingOrbit P.pair))
        (orbitWedgeBase P) ≃*
      FundamentalGroup
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
          (Fin (Fintype.card (PairingOrbit P.pair))))
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
          (pairingOrbitFinZero P) 1) :=
  fundamentalGroupEquivOfHomeomorphEq
    (finiteWedgeOrbitHomeomorphFinZero P) (orbitWedgeBase P)
    (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle
      (pairingOrbitFinZero P) 1)
    (finiteWedgeOrbitHomeomorphFinZero_base P)

/-- Explicit orbit relabelling carries an arbitrary based circle loop in an
orbit leg to the corresponding finite-coordinate leg. -/
theorem finiteWedgeOrbitFundamentalGroupEquivFinExplicit_legMap
    (P : PairingData) (l : PairingOrbit P.pair)
    (g : FundamentalGroup Circle 1) :
    finiteWedgeOrbitFundamentalGroupEquivFinExplicit P
        (Path.Homotopic.Quotient.cast
          (FundamentalGroup.map
            ⟨PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle l,
              PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle l⟩
            1 g)
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle_base_eq
            (P.orbit ⟨0, P.edgeCount_pos⟩) l)
          (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle_base_eq
            (P.orbit ⟨0, P.edgeCount_pos⟩) l)) =
      finiteWedgeFinLegMapCard (Fintype.card (PairingOrbit P.pair))
        (pairingOrbitCard_pos P) (pairingOrbitEquivFinZero P l)
        g := by
  induction g using Path.Homotopic.Quotient.ind with
  | mk p =>
      rw [FundamentalGroup.map_apply]
      unfold finiteWedgeOrbitFundamentalGroupEquivFinExplicit
        fundamentalGroupEquivOfHomeomorphEq
      change FundamentalGroup.mapOfEq
          ⟨finiteWedgeOrbitHomeomorphFinZero P,
            (finiteWedgeOrbitHomeomorphFinZero P).continuous⟩
          (finiteWedgeOrbitHomeomorphFinZero_base P)
          ((Path.Homotopic.Quotient.mk _).cast _ _) = _
      rw [← Path.Homotopic.Quotient.mk_cast,
        FundamentalGroup.mapOfEq_apply]
      rw [finiteWedgeFinLegMapCard, FundamentalGroup.mapOfEq_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl
        ((p.map
          (PolygonSurfacePiOne.PointWedgeQuotient.continuous_wedgeCircle
            (pairingOrbitEquivFinZero P l))).cast _ _) using 1

/-- The positive generators are identified by the explicit based orbit
relabeling. -/
theorem finiteWedgeOrbitFundamentalGroupEquivFinExplicit_leg
    (P : PairingData) (l : PairingOrbit P.pair) :
    finiteWedgeOrbitFundamentalGroupEquivFinExplicit P
        (finiteWedgeLegFundamentalClassAtBase P l) =
      finiteWedgeFinLegMapCard (Fintype.card (PairingOrbit P.pair))
        (pairingOrbitCard_pos P) (pairingOrbitEquivFinZero P l)
        circlePositiveFundamentalClass := by
  simpa [finiteWedgeLegFundamentalClassAtBase,
    finiteWedgeLegFundamentalClass] using
    finiteWedgeOrbitFundamentalGroupEquivFinExplicit_legMap P l
      circlePositiveFundamentalClass

/-- Relabelling the orbit generators before applying the finite-coordinate
map agrees with applying the orbit map and then transporting fundamental
groups. -/
theorem finiteWedgeOrbitFreeGroupMapComparison (P : PairingData)
    (x : FreeGroup (PairingOrbit P.pair)) :
    finiteWedgeOrbitFundamentalGroupEquivFinExplicit P
        (finiteWedgeLegFreeGroupMap P x) =
      finiteWedgeFinLegFreeGroupMapCard
          (Fintype.card (PairingOrbit P.pair)) (pairingOrbitCard_pos P)
        (FreeGroup.map (pairingOrbitEquivFinZero P) x) := by
  induction x using FreeGroup.induction_on with
  | C1 =>
      simp only [map_one]
      rfl
  | of l =>
      simpa [finiteWedgeLegFreeGroupMap,
        finiteWedgeFinLegFreeGroupMapCard] using
        finiteWedgeOrbitFundamentalGroupEquivFinExplicit_leg P l
  | inv_of l _ =>
      simp only [map_inv]
      have h :
          finiteWedgeOrbitFundamentalGroupEquivFinExplicit P
              (finiteWedgeLegFreeGroupMap P (FreeGroup.of l)) =
            finiteWedgeFinLegFreeGroupMapCard
                (Fintype.card (PairingOrbit P.pair)) (pairingOrbitCard_pos P)
              (FreeGroup.map (pairingOrbitEquivFinZero P) (FreeGroup.of l)) := by
        simpa [finiteWedgeLegFreeGroupMap,
          finiteWedgeFinLegFreeGroupMapCard] using
          finiteWedgeOrbitFundamentalGroupEquivFinExplicit_leg P l
      exact congrArg (fun z => z⁻¹) h
  | mul x y hx hy =>
      simp only [map_mul]
      rw [hx, hy]
      rfl

/-- The canonical positive-leg map onto the orbit-indexed finite wedge is
surjective. -/
theorem finiteWedgeLegFreeGroupMap_surjective (P : PairingData) :
    Function.Surjective (finiteWedgeLegFreeGroupMap P) := by
  intro g
  obtain ⟨y, hy⟩ :=
    finiteWedgeFinLegFreeGroupMapCard_surjective
      (Fintype.card (PairingOrbit P.pair)) (pairingOrbitCard_pos P)
      (finiteWedgeOrbitFundamentalGroupEquivFinExplicit P g)
  obtain ⟨x, rfl⟩ := FreeGroup.map_surjective
    (pairingOrbitEquivFinZero P).surjective y
  refine ⟨x, (finiteWedgeOrbitFundamentalGroupEquivFinExplicit P).injective ?_⟩
  rw [finiteWedgeOrbitFreeGroupMapComparison, hy]

/-- Every based-loop Hurewicz class is in the normalized finite-wedge
coordinate image. -/
theorem finiteWedgeHurewicz_generated_by_coordinates (P : PairingData)
    (g : FundamentalGroup
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
        (PairingOrbit P.pair)) (orbitWedgeBase P)) :
    ∃ v : PairingOrbit P.pair → ℤ,
      finiteWedgeH1CoordinateMap P v = finiteWedgeModuleHurewicz P g := by
  obtain ⟨w, hw⟩ :=
    finiteWedgeFundamentalGroup_generated_by_legs_of_freeGroup_surjective P
      (finiteWedgeLegFreeGroupMap_surjective P) g
  refine ⟨finiteWedgeLegWordCoordinatesList P w, ?_⟩
  rw [← hw]
  simpa [finiteWedgeModuleHurewicz, moduleHurewicz] using
    (finiteWedgeLegWord_hurewicz P w).symm

/-- The normalized finite-wedge first-homology coordinate map is onto. -/
theorem finiteWedgeH1CoordinateMap_surjective (P : PairingData) :
    Function.Surjective (finiteWedgeH1CoordinateMap P) :=
  finiteWedgeH1CoordinateMap_surjective_of_hurewicz_generation P
    (finiteWedgeHurewicz_generated_by_coordinates P)

noncomputable instance finiteWedgeH1CoordinateMap_epi (P : PairingData) :
    Epi (finiteWedgeH1CoordinateMap P) :=
  (ModuleCat.epi_iff_surjective (finiteWedgeH1CoordinateMap P)).mpr
    (finiteWedgeH1CoordinateMap_surjective P)

/-- The normalized coordinates give the required finite-wedge H₁
isomorphism, with the positive leg basis fixed. -/
noncomputable def finiteWedgeH1CoordinateIso (P : PairingData) :
    ModuleCat.of ℤ (PairingOrbit P.pair → ℤ) ≅
      SpaceH
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
          (PairingOrbit P.pair)) 1 := by
  letI : IsIso (finiteWedgeH1CoordinateMap P) :=
    isIso_of_mono_of_epi (finiteWedgeH1CoordinateMap P)
  exact asIso (finiteWedgeH1CoordinateMap P)

/-- B4 in degree one: transport the fixed positive-leg coordinates from the
finite wedge to the radial outer piece. -/
noncomputable def outerH1IsoCoordinates (P : PairingData) :
    SpaceH (OuterPiece P) 1 ≅ ModuleCat.of ℤ (PairingOrbit P.pair → ℤ) :=
  ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsoOfGroupIso
    (TopCat.of (OuterPiece P)) 1
    (ModuleCat.of ℤ (PairingOrbit P.pair → ℤ))
    (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
        (outerHomotopyEquivWedge P) 1 ≪≫
      (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of
          (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
            (PairingOrbit P.pair))) 1).symm ≪≫
      ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
        (finiteWedgeH1CoordinateIso P).symm)

/-! ### Higher homology of finite wedges -/

/-- Mayer--Vietoris preserves higher-homology vanishing when two pointed
spaces are joined at contractible base neighborhoods.  This is the induction
step used for finite wedges of circles. -/
theorem pointWedgeHigherHomologyIsZero
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (x₀ : X) (y₀ : Y)
    (PX : PointedContractibleNeighborhood X x₀)
    (PY : PointedContractibleNeighborhood Y y₀)
    (n : ℕ) (hn : 2 ≤ n)
    (hX : IsZero (SpaceH X n)) (hY : IsZero (SpaceH Y n)) :
    IsZero (SpaceH (ConstructionTargets.PointWedgeQuotient.Wedge x₀ y₀) n) := by
  let p := ConstructionTargets.GenericPointWedgeOpenCoverComparison.genericPointWedgeCoverPackage
    x₀ y₀ PY.carrier PX.carrier PY.isOpen PX.isOpen PY.mem PX.mem
      PY.contraction PX.contraction
  let U := ConstructionTargets.PointWedgeQuotient.leftOpen
    x₀ y₀ PY.carrier
  let V := ConstructionTargets.PointWedgeQuotient.rightOpen
    x₀ y₀ PX.carrier
  let GH (k : ℕ) (Z : Type) [TopologicalSpace Z] :=
    ConstructionTargets.SingularHomologyConcrete.SingularHomology k (TopCat.of Z)
  have hI (k : ℕ) (hk : k ≠ 0) : IsZero (GH k (U ∩ V : Set _)) :=
    (ConstructionTargets.SingularHomologyConcrete.contractibleHigherHomology_isZero
      Unit k hk).of_iso
      (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
        p.intersectionEquiv k)
  have hIso : IsIso
      (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow U V n) := by
    have hm : Mono
        (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow U V n) :=
      (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionMayerVietoris_exact_pieces
        U V p.leftOpen_isOpen p.rightOpen_isOpen p.union_eq_univ n).mono_g_iff.mpr
          ((hI n (by omega)).eq_of_src _ _)
    have heq : n - 1 + 1 = n := by omega
    have he : Epi
        (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow U V n) := by
      rw [← heq]
      exact
        (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionMayerVietoris_exact_union
          U V p.leftOpen_isOpen p.rightOpen_isOpen p.union_eq_univ (n - 1)).epi_f_iff.mpr
            ((hI (n - 1) (by omega)).eq_of_tgt _ _)
    letI := hm
    letI := he
    exact isIso_of_mono_of_epi _
  letI := hIso
  have underlyingIsZero {A : ModuleCat ℤ} (hA : IsZero A) :
      IsZero
        (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.obj A) := by
    rw [IsZero.iff_id_eq_zero]
    rw [← ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map_id,
      ← ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map_zero]
    exact congrArg
      (ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.map)
      (hA.eq_of_src _ _)
  have hUG : IsZero (GH n U) :=
    (underlyingIsZero hX).of_iso
      (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of X) n).symm |>.of_iso
      (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
        p.leftEquiv n)
  have hVG : IsZero (GH n V) :=
    (underlyingIsZero hY).of_iso
      (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of Y) n).symm |>.of_iso
      (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
        p.rightEquiv n)
  have hW : IsZero (GH n (ConstructionTargets.PointWedgeQuotient.Wedge x₀ y₀)) := by
    have hp : IsZero (GH n U ⊞ GH n V) :=
      (biprod_isZero_iff _ _).mpr ⟨hUG, hVG⟩
    exact hp.of_iso
      (asIso (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow
        U V n)).symm
  exact
    ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsZeroOfGroupIsZero
      (TopCat.of (ConstructionTargets.PointWedgeQuotient.Wedge x₀ y₀)) n hW

/-- Integral homology transport along a homotopy equivalence, in the module
presentation used by the polygon calculation. -/
noncomputable def spaceHHomotopyEquivIso
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (n : ℕ) : SpaceH X n ≅ SpaceH Y n :=
  ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsoOfGroupIso
    (TopCat.of X) n (SpaceH Y n)
    (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv e n ≪≫
      (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
        (TopCat.of Y) n).symm)

/-- Every nonempty standard finite wedge of circles has zero integral
homology above degree one. -/
theorem finiteWedgeFinHigherHomologyIsZero :
    ∀ (m n : ℕ), 2 ≤ n →
      IsZero (SpaceH
        (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge (Fin (m + 1))) n)
  | 0, n, hn => by
      have hc : IsZero (SpaceH Circle n) :=
        ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsZeroOfGroupIsZero
          (TopCat.of Circle) n
          (ConstructionTargets.BoundaryTorusMayerVietoris.circleHomology_isZero_of_one_lt
            n (by omega))
      exact hc.of_iso
        (spaceHHomotopyEquivIso finiteWedgeFinOneHomeomorphCircle.toHomotopyEquiv n)
  | m + 1, n, hn => by
      let P := finiteWedgeFinSuccPointWedgeNeighborhoods m
      have hold := finiteWedgeFinHigherHomologyIsZero m n hn
      have hlast : IsZero
          (SpaceH
            (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge Unit) n) := by
        have hc : IsZero (SpaceH Circle n) :=
          ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsZeroOfGroupIsZero
            (TopCat.of Circle) n
            (ConstructionTargets.BoundaryTorusMayerVietoris.circleHomology_isZero_of_one_lt
              n (by omega))
        exact hc.of_iso
          (spaceHHomotopyEquivIso
            (finiteWedgeSubsingletonHomeomorphCircle ()).toHomotopyEquiv n)
      have hw := pointWedgeHigherHomologyIsZero
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle (0 : Fin (m + 1)) 1)
        (PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle () 1)
        P.1 P.2 n hn hold hlast
      exact hw.of_iso
        (spaceHHomotopyEquivIso
          (finiteWedgeFinSuccHomeomorphPointWedge m).toHomotopyEquiv n)

/-- B4 above degree one for the polygon's orbit-indexed finite wedge. -/
theorem finiteWedgeHigherHomologyIsZero (P : PairingData) (n : ℕ) (hn : 2 ≤ n) :
    IsZero (SpaceH
      (PolygonSurfacePiOne.PointWedgeQuotient.FiniteWedge
        (PairingOrbit P.pair)) n) := by
  generalize hc :
    Fintype.card (PairingOrbit P.pair) = c
  cases c with
  | zero =>
      exfalso
      have := pairingOrbitCard_pos P
      omega
  | succ m =>
      have hfin := finiteWedgeFinHigherHomologyIsZero m n hn
      let e := finiteWedgeOrbitHomeomorphFin P
      rw [hc] at e
      exact hfin.of_iso (spaceHHomotopyEquivIso e.toHomotopyEquiv n)

/-- B4 above degree one, transported from the finite wedge to the radial
outer piece. -/
theorem outerHigherHomologyIsZero (P : PairingData) (n : ℕ) (hn : 2 ≤ n) :
    IsZero (SpaceH (OuterPiece P) n) :=
  (finiteWedgeHigherHomologyIsZero P n hn).of_iso
    (spaceHHomotopyEquivIso (outerHomotopyEquivWedge P) n)

/-! ### Radial Mayer--Vietoris segment -/

/-- The literal intersection of the two radial cover members, identified
with the annular overlap model used by B5. -/
def radialIntersectionHomeomorphOverlap (P : PairingData) :
    {q // q ∈ (openCover P).inner ∩ (openCover P).outer} ≃ₜ OverlapPiece P :=
  Homeomorph.setCongr (openCover P).overlap_eq.symm

/-- The positive circle in the literal intersection: radius one half with
the standard counterclockwise circle parameter. -/
def radialIntersectionPositiveCircle (P : PairingData) :
    C(Circle, {q // q ∈ (openCover P).inner ∩ (openCover P).outer}) :=
  (⟨(radialIntersectionHomeomorphOverlap P).symm,
      (radialIntersectionHomeomorphOverlap P).symm.continuous⟩ :
    C(OverlapPiece P,
      {q // q ∈ (openCover P).inner ∩ (openCover P).outer})).comp
    (overlapHomotopyEquivCircle P).invFun

/-- The chosen intersection circle is exactly the inverse of the positive
overlap-to-circle equivalence. -/
theorem radialIntersectionPositiveCircle_toOverlap (P : PairingData)
    (z : Circle) :
    radialIntersectionHomeomorphOverlap P
        (radialIntersectionPositiveCircle P z) =
      (overlapHomotopyEquivCircle P).invFun z := by
  rfl

/-- After forgetting the inner-membership proof, the chosen intersection
circle is the quotient of the literal radius-one-half circle. -/
theorem radialIntersectionPositiveCircle_val (P : PairingData) (z : Circle) :
    (radialIntersectionPositiveCircle P z).1 =
      ConstructionTargets.PolygonRadialOpenCover.quotientMap P.Rel
        (ConstructionTargets.PolygonAnnulusRadialMaps.halfCircleMap z).1 := by
  rfl

/-- The same positive overlap circle included in the outer radial member. -/
def radialOverlapCircleInOuter (P : PairingData) : C(Circle, OuterPiece P) :=
  (⟨fun q => ⟨q.1, q.2.2⟩, by fun_prop⟩ :
    C({q // q ∈ (openCover P).inner ∩ (openCover P).outer}, OuterPiece P)).comp
    (radialIntersectionPositiveCircle P)

/-- The outer-member loop retains the literal radius-one-half quotient
representative, fixing its orientation before homology is applied. -/
theorem radialOverlapCircleInOuter_val (P : PairingData) (z : Circle) :
    (radialOverlapCircleInOuter P z).1 =
      ConstructionTargets.PolygonRadialOpenCover.quotientMap P.Rel
        (ConstructionTargets.PolygonAnnulusRadialMaps.halfCircleMap z).1 := by
  exact radialIntersectionPositiveCircle_val P z

/-- The radius-one-half representative regarded in the source of the outer
radial quotient. -/
def halfCircleOuter (z : Circle) :
    ConstructionTargets.PolygonOuterRadialDeformation.Outer :=
  ⟨(ConstructionTargets.PolygonAnnulusRadialMaps.halfCircleMap z).1,
    (ConstructionTargets.PolygonAnnulusRadialMaps.halfCircleMap z).2.2⟩

/-- At time one, radial deformation of the half-radius representative is the
unit boundary point with the same positive circle parameter. -/
theorem radialHomotopy_one_halfCircle (z : Circle) :
    (ConstructionTargets.PolygonOuterRadialDeformation.radialHomotopy
      (1, halfCircleOuter z)).1 = circleToPolygonDisk z := by
  apply Subtype.ext
  simp [ConstructionTargets.PolygonOuterRadialDeformation.radialHomotopy,
    ConstructionTargets.PolygonOuterRadialDeformation.scale,
    halfCircleOuter, ConstructionTargets.PolygonAnnulusRadialMaps.halfCircleMap,
    ConstructionTargets.PolygonRadialOpenCover.radius, circleToPolygonDisk]

/-- The radial outer deformation carries the positive overlap circle to the
ordered polygon boundary loop. -/
theorem outerHomotopyEquivWedge_radialOverlapCircle (P : PairingData)
    (z : Circle) :
    outerHomotopyEquivWedge P (radialOverlapCircleInOuter P z) =
      polygonBoundaryWedgeLoop P z := by
  change P.skeletonHomeomorphWedge
      ((outerBoundaryHomeomorphSkeleton P)
        ((outerHomotopyEquivBoundary P) (radialOverlapCircleInOuter P z))) =
    P.skeletonHomeomorphWedge (polygonBoundarySkeletonLoop P z)
  congr 1
  apply Subtype.ext
  change
    (ConstructionTargets.PolygonOuterOpenDeformation.outerOpenHomotopy P.Rel
      (fun {_ _} h => pairingRel_radius P h)
      (fun {_ _} h => pairingRel_boundary P h)
      (1, radialOverlapCircleInOuter P z)).1 =
      P.quotientMap (circleToPolygonDisk z)
  simp only [ConstructionTargets.PolygonOuterOpenDeformation.outerOpenHomotopy]
  rw [show
    (ConstructionTargets.PolygonOuterRestrictedEqvGen.outerQuotientHomeomorph
      P.Rel (fun {_ _} h => pairingRel_radius P h)).symm
        (radialOverlapCircleInOuter P z) =
      Quotient.mk _ (halfCircleOuter z) by
        apply (ConstructionTargets.PolygonOuterRestrictedEqvGen.outerQuotientHomeomorph
          P.Rel (fun {_ _} h => pairingRel_radius P h)).injective
        rw [Homeomorph.apply_symm_apply,
          ConstructionTargets.PolygonOuterRestrictedEqvGen.outerQuotientHomeomorph_mk]
        apply Subtype.ext
        exact radialOverlapCircleInOuter_val P z]
  rw [ConstructionTargets.PolygonOuterRadialQuotientDeformation.quotientHomotopy_mk,
    ConstructionTargets.PolygonOuterRestrictedEqvGen.outerQuotientHomeomorph_mk]
  change P.quotientMap
      (ConstructionTargets.PolygonOuterRadialDeformation.radialHomotopy
        (1, halfCircleOuter z)).1 = _
  rw [radialHomotopy_one_halfCircle]

/-- Degree-one integral singular homology map induced by a continuous map,
in the additive-group presentation used by the production MV sequence. -/
noncomputable def singularH1Map {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    ConstructionTargets.SingularHomologyConcrete.SingularHomology 1
        (TopCat.of X) ⟶
      ConstructionTargets.SingularHomologyConcrete.SingularHomology 1
        (TopCat.of Y) :=
  HomologicalComplex.homologyMap
    (((AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ)).map (TopCat.toSSet.map (TopCat.ofHom f))) 1

theorem singularH1Map_comp {X Y Z : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) :
    singularH1Map (g.comp f) = singularH1Map f ≫ singularH1Map g := by
  change HomologicalComplex.homologyMap
      (((AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).map
        (TopCat.toSSet.map (TopCat.ofHom f ≫ TopCat.ofHom g))) 1 = _
  rw [Functor.map_comp, Functor.map_comp]
  simp only [singularH1Map]
  exact HomologicalComplex.homologyMap_comp _ _ 1

/-- The pointwise radial comparison is equality of the corresponding
continuous circle maps. -/
theorem outerHomotopyEquivWedge_comp_radialOverlapCircle (P : PairingData) :
    (outerHomotopyEquivWedge P).toFun.comp (radialOverlapCircleInOuter P) =
      polygonBoundaryWedgeLoop P := by
  apply ContinuousMap.ext
  exact outerHomotopyEquivWedge_radialOverlapCircle P

/-- Functorial degree-one homology therefore identifies the included overlap
circle with the ordered signed polygon boundary loop. -/
theorem radialOverlapCircle_h1_eq_boundaryLoop_h1 (P : PairingData) :
    singularH1Map
        ((outerHomotopyEquivWedge P).toFun.comp
          (radialOverlapCircleInOuter P)) =
      singularH1Map (polygonBoundaryWedgeLoop P) := by
  rw [outerHomotopyEquivWedge_comp_radialOverlapCircle]

/-- Expanded through functoriality, the same comparison is a commuting H₁
triangle from the positive overlap circle through the outer member. -/
theorem radialOverlapCircle_h1_naturality (P : PairingData) :
    singularH1Map (radialOverlapCircleInOuter P) ≫
        singularH1Map (outerHomotopyEquivWedge P).toFun =
      singularH1Map (polygonBoundaryWedgeLoop P) := by
  rw [← singularH1Map_comp, radialOverlapCircle_h1_eq_boundaryLoop_h1]

/-- Positive integral coordinates on the actual intersection object occurring
in the production Mayer--Vietoris sequence. -/
noncomputable def radialIntersectionH1GroupIsoInt (P : PairingData) :
    ConstructionTargets.SingularHomologyConcrete.SingularHomology 1
        (TopCat.of {q // q ∈ (openCover P).inner ∩ (openCover P).outer}) ≅
      AddCommGrpCat.of ℤ :=
  ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
      (radialIntersectionHomeomorphOverlap P).toHomotopyEquiv 1 ≪≫
    ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
      (overlapHomotopyEquivCircle P) 1 ≪≫
    circleGroupH1IsoInt

theorem singularHomologyIsoOfHomotopyEquiv_inv_h1
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
      e 1).inv = singularH1Map e.invFun := by
  apply (cancel_mono
    (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
      e 1).hom).1
  rw [Iso.inv_hom_id]
  rw [ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv_hom]
  change 𝟙 (ConstructionTargets.SingularHomologyConcrete.SingularHomology 1
      (TopCat.of Y)) =
    singularH1Map e.invFun ≫ singularH1Map e.toFun
  rw [← singularH1Map_comp]
  change 𝟙 (ConstructionTargets.SingularHomologyConcrete.SingularHomology 1
      (TopCat.of Y)) =
    ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
      (AddCommGrpCat.of ℤ)).map
        (TopCat.ofHom (e.toFun.comp e.invFun))
  rw [ConstructionTargets.SingularHomologyConcrete.singularHomology_map_eq_of_topCatHomotopy
    (ConstructionTargets.SingularHomologyConcrete.continuousMapHomotopyCylinder
      (Classical.choice e.right_inv))
    (ConstructionTargets.SingularHomologyConcrete.continuousMapHomotopyCylinder_zero
      (Classical.choice e.right_inv))
    (ConstructionTargets.SingularHomologyConcrete.continuousMapHomotopyCylinder_one
      (Classical.choice e.right_inv))]
  have h : TopCat.ofHom (ContinuousMap.id Y) = 𝟙 (TopCat.of Y) := by rfl
  rw [h]
  exact ((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 1).obj
    (AddCommGrpCat.of ℤ)).map_id (TopCat.of Y) |>.symm

/-- The element selected by the intersection coordinate is precisely the
positive circle class mapped through the explicit intersection circle. -/
theorem radialIntersectionPositiveGenerator_eq (P : PairingData) :
    (radialIntersectionH1GroupIsoInt P).inv 1 =
      singularH1Map (radialIntersectionPositiveCircle P)
        (circleGroupH1IsoInt.inv 1) := by
  change ((ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
      (radialIntersectionHomeomorphOverlap P).toHomotopyEquiv 1 ≪≫
    ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
      (overlapHomotopyEquivCircle P) 1 ≪≫ circleGroupH1IsoInt).inv) 1 = _
  rw [Iso.trans_inv, Iso.trans_inv,
    singularHomologyIsoOfHomotopyEquiv_inv_h1,
    singularHomologyIsoOfHomotopyEquiv_inv_h1]
  rw [Category.assoc, ← singularH1Map_comp]
  rfl

/-- Fixed orbit coordinates on the outer term of the production sequence. -/
noncomputable def radialOuterH1GroupIsoCoordinates (P : PairingData) :
    ConstructionTargets.SingularHomologyConcrete.SingularHomology 1
        (TopCat.of (OuterPiece P)) ≅
      AddCommGrpCat.of (PairingOrbit P.pair → ℤ) :=
  (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
      (TopCat.of (OuterPiece P)) 1).symm ≪≫
    ConstructionTargets.IntegralSingularHomologyComparison.forgetIntModules.mapIso
      (outerH1IsoCoordinates P)

/-- B6 before coordinate transport: exactness at the two radial pieces in
every degree. -/
theorem radialMVPiecesExact (P : PairingData) (n : ℕ) :
    (ShortComplex.mk
      (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionIntersectionArrow
        (openCover P).inner (openCover P).outer n)
      (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow
        (openCover P).inner (openCover P).outer n)
      (by
        rw [← ConstructionTargets.ProductionOpenCoverMayerVietoris.booleanIntersectionArrow_eq_production,
          ← ConstructionTargets.ProductionOpenCoverMayerVietoris.booleanReassemblyArrow_eq_production
            (openCover P).inner (openCover P).outer
            (openCover P).inner_open (openCover P).outer_open (openCover P).cover]
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        have hz :
            HomologicalComplex.homologyMap
                (ConstructionTargets.BooleanTwoCoverScaffold.shortComplex
                  (openCover P).inner (openCover P).outer).f n ≫
              HomologicalComplex.homologyMap
                (ConstructionTargets.BooleanTwoCoverScaffold.shortComplex
                  (openCover P).inner (openCover P).outer).g n = 0 := by
          rw [← HomologicalComplex.homologyMap_comp,
            (ConstructionTargets.BooleanTwoCoverScaffold.shortComplex
              (openCover P).inner (openCover P).outer).zero,
            HomologicalComplex.homologyMap_zero]
        simpa only [Category.assoc, zero_comp, comp_zero] using
          congrArg (fun k ↦
            (ConstructionTargets.ProductionOpenCoverMayerVietoris.booleanIntersectionProductionHomologyIso
              (openCover P).inner (openCover P).outer n).inv ≫ k ≫
            (ConstructionTargets.ProductionOpenCoverMayerVietoris.booleanUnionProductionHomologyIso
              (openCover P).inner (openCover P).outer
              (openCover P).inner_open (openCover P).outer_open
              (openCover P).cover n).hom) hz)).Exact :=
  ConstructionTargets.ProductionOpenCoverMayerVietoris.productionMayerVietoris_exact_pieces
    (openCover P).inner (openCover P).outer
    (openCover P).inner_open (openCover P).outer_open (openCover P).cover n

/-- The remaining production exactness witness at the surface term.  Its
inferred type retains the canonical connecting morphism and its zero proof. -/
noncomputable def radialMVUnionExact (P : PairingData) (n : ℕ) :=
  ConstructionTargets.ProductionOpenCoverMayerVietoris.productionMayerVietoris_exact_union
    (openCover P).inner (openCover P).outer
    (openCover P).inner_open (openCover P).outer_open (openCover P).cover n

/-- The remaining production exactness witness at the next intersection
term, completing the named radial long-exact-sequence fragment. -/
noncomputable def radialMVIntersectionExact (P : PairingData) (n : ℕ) :=
  ConstructionTargets.ProductionOpenCoverMayerVietoris.productionMayerVietoris_exact_intersection
    (openCover P).inner (openCover P).outer
    (openCover P).inner_open (openCover P).outer_open (openCover P).cover n

/-- The inner degree-one group in the radial sequence is zero. -/
theorem radialInnerH1GroupIsZero (P : PairingData) :
    IsZero
      (ConstructionTargets.SingularHomologyConcrete.SingularHomology 1
        (TopCat.of (InnerPiece P))) :=
  (ConstructionTargets.SingularHomologyConcrete.pointHigherHomology_isZero 1
    (by omega)).of_iso
      (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
        (innerHomotopyEquivPoint P) 1)

/-- The one nonzero degree-one map left after removing the contractible inner
summand, expressed in the fixed positive-overlap and outer-orbit coordinates.
This is the morphism computed geometrically in B7. -/
noncomputable def radialMVBoundaryGroup (P : PairingData) :
    AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of (PairingOrbit P.pair → ℤ) :=
  (radialIntersectionH1GroupIsoInt P).inv ≫
    ConstructionTargets.ProductionOpenCoverMayerVietoris.productionIntersectionArrow
      (openCover P).inner (openCover P).outer 1 ≫
    (biprod.snd :
      ConstructionTargets.SingularHomologyConcrete.SingularHomology 1
          (TopCat.of (InnerPiece P)) ⊞
        ConstructionTargets.SingularHomologyConcrete.SingularHomology 1
          (TopCat.of (OuterPiece P)) ⟶
      ConstructionTargets.SingularHomologyConcrete.SingularHomology 1
        (TopCat.of (OuterPiece P))) ≫
    (radialOuterH1GroupIsoCoordinates P).hom

/-- Projection away from a zero first summand is an isomorphism. -/
noncomputable def biprodSndIsoOfIsZero {A B : AddCommGrpCat}
    (hA : IsZero A) : A ⊞ B ≅ B where
  hom := biprod.snd
  inv := biprod.inr
  hom_inv_id := by
    apply biprod.hom_ext
    · exact hA.eq_of_tgt _ _
    · simp
  inv_hom_id := by simp

theorem radialMVPieces_comp_zero (P : PairingData) :
    ConstructionTargets.ProductionOpenCoverMayerVietoris.productionIntersectionArrow
        (openCover P).inner (openCover P).outer 1 ≫
      ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow
        (openCover P).inner (openCover P).outer 1 = 0 := by
  rw [← ConstructionTargets.ProductionOpenCoverMayerVietoris.booleanIntersectionArrow_eq_production,
    ← ConstructionTargets.ProductionOpenCoverMayerVietoris.booleanReassemblyArrow_eq_production
      (openCover P).inner (openCover P).outer
      (openCover P).inner_open (openCover P).outer_open (openCover P).cover]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hz :
      HomologicalComplex.homologyMap
          (ConstructionTargets.BooleanTwoCoverScaffold.shortComplex
            (openCover P).inner (openCover P).outer).f 1 ≫
        HomologicalComplex.homologyMap
          (ConstructionTargets.BooleanTwoCoverScaffold.shortComplex
            (openCover P).inner (openCover P).outer).g 1 = 0 := by
    rw [← HomologicalComplex.homologyMap_comp,
      (ConstructionTargets.BooleanTwoCoverScaffold.shortComplex
        (openCover P).inner (openCover P).outer).zero,
      HomologicalComplex.homologyMap_zero]
  simpa only [Category.assoc, zero_comp, comp_zero] using
    congrArg (fun k ↦
      (ConstructionTargets.ProductionOpenCoverMayerVietoris.booleanIntersectionProductionHomologyIso
        (openCover P).inner (openCover P).outer 1).inv ≫ k ≫
      (ConstructionTargets.ProductionOpenCoverMayerVietoris.booleanUnionProductionHomologyIso
        (openCover P).inner (openCover P).outer
        (openCover P).inner_open (openCover P).outer_open
        (openCover P).cover 1).hom) hz

/-- The degree-one radial pieces segment after deleting the zero inner
summand and applying the fixed overlap and outer coordinates. -/
noncomputable def radialMVReducedPieces (P : PairingData) :
    ShortComplex AddCommGrpCat :=
  ShortComplex.mk (radialMVBoundaryGroup P)
    ((radialOuterH1GroupIsoCoordinates P).inv ≫ biprod.inr ≫
      ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow
        (openCover P).inner (openCover P).outer 1)
    (by
      simp only [radialMVBoundaryGroup, Category.assoc,
        Iso.hom_inv_id_assoc]
      calc
        _ = (radialIntersectionH1GroupIsoInt P).inv ≫
              ConstructionTargets.ProductionOpenCoverMayerVietoris.productionIntersectionArrow
                (openCover P).inner (openCover P).outer 1 ≫
              ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow
                (openCover P).inner (openCover P).outer 1 := by
            simpa only [biprodSndIsoOfIsZero] using
              congrArg (fun k ↦
                (radialIntersectionH1GroupIsoInt P).inv ≫
                  ConstructionTargets.ProductionOpenCoverMayerVietoris.productionIntersectionArrow
                    (openCover P).inner (openCover P).outer 1 ≫ k)
                ((biprodSndIsoOfIsZero
                  (radialInnerH1GroupIsZero P)).hom_inv_id_assoc
                    (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow
                      (openCover P).inner (openCover P).outer 1))
        _ = 0 := by
          simpa only [Category.assoc, comp_zero] using
            congrArg (fun k ↦ (radialIntersectionH1GroupIsoInt P).inv ≫ k)
              (radialMVPieces_comp_zero P))

/-- B6 at the middle term, transported through the zero inner summand and
the fixed degree-one coordinates. -/
theorem radialMVReducedPiecesExact (P : PairingData) :
    (radialMVReducedPieces P).Exact := by
  apply ShortComplex.exact_of_iso ?_ (radialMVPiecesExact P 1)
  exact ShortComplex.isoMk
    (radialIntersectionH1GroupIsoInt P)
    ((biprodSndIsoOfIsZero (radialInnerH1GroupIsZero P)) ≪≫
      radialOuterH1GroupIsoCoordinates P)
    (Iso.refl _)
    (by
      simpa only [radialMVReducedPieces, radialMVBoundaryGroup,
        Iso.trans_hom, Category.comp_id] using
        (radialIntersectionH1GroupIsoInt P).hom_inv_id_assoc
          (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionIntersectionArrow
            (openCover P).inner (openCover P).outer 1 ≫
            ((biprodSndIsoOfIsZero (radialInnerH1GroupIsZero P)) ≪≫
              radialOuterH1GroupIsoCoordinates P).hom))
    (by
      simpa only [radialMVReducedPieces, Category.comp_id] using
        (((biprodSndIsoOfIsZero (radialInnerH1GroupIsZero P)) ≪≫
          radialOuterH1GroupIsoCoordinates P).hom_inv_id_assoc
            (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow
              (openCover P).inner (openCover P).outer 1)))

/-- A proof-relevant exactness package exposing the two arrows while hiding
only the proof that their composite is zero. -/
def HasExactArrows {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : Prop :=
  ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).Exact

theorem hasExactArrows_of_exact {C : Type*} [Category C] [HasZeroMorphisms C]
    {S : ShortComplex C} (hS : S.Exact) : HasExactArrows S.f S.g :=
  ⟨S.zero, by simpa only using hS⟩

/-- B6: the degree-two/degree-one radial Mayer--Vietoris fragment.  The
middle short complex is in the fixed integer/orbit coordinates; the adjacent
packages expose the production connecting, reassembly, and intersection
arrows in their long-exact-sequence order. -/
theorem radialMVSegment (P : PairingData) :
    (radialMVReducedPieces P).Exact ∧
      HasExactArrows
        (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionReassemblyArrow
          (openCover P).inner (openCover P).outer 1)
        (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionConnecting
          (openCover P).inner (openCover P).outer
          (openCover P).inner_open (openCover P).outer_open (openCover P).cover 0) ∧
      HasExactArrows
        (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionConnecting
          (openCover P).inner (openCover P).outer
          (openCover P).inner_open (openCover P).outer_open (openCover P).cover 1)
        (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionIntersectionArrow
          (openCover P).inner (openCover P).outer 1) := by
  exact ⟨radialMVReducedPiecesExact P,
    hasExactArrows_of_exact (radialMVUnionExact P 0),
    hasExactArrows_of_exact (radialMVIntersectionExact P 1)⟩

/-! ### Attaching-map coordinates -/

/-- The algebraic attaching boundary in the additive-group category used by
the production Mayer--Vietoris sequence. -/
def attachingBoundaryGroup (P : PairingData) :
    AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of (PairingOrbit P.pair → ℤ) :=
  AddCommGrpCat.ofHom (attachingBoundary P).toAddMonoidHom

@[simp] theorem attachingBoundaryGroup_apply (P : PairingData) (n : ℤ) :
    attachingBoundaryGroup P n = n • attachingDegree P := rfl

/-- Additive homomorphisms out of the infinite cyclic group are determined
by the positive generator. -/
theorem addCommGrpHom_int_ext {A : AddCommGrpCat}
    (f g : AddCommGrpCat.of ℤ ⟶ A) (h : f 1 = g 1) : f = g := by
  apply ConcreteCategory.hom_ext
  intro n
  calc
    f n = n • f 1 := by
      simpa using (map_zsmul f.hom n (1 : ℤ))
    _ = n • g 1 := congrArg (fun x ↦ n • x) h
    _ = g n := by
      simpa using (map_zsmul g.hom n (1 : ℤ)).symm

/-- B7 is reduced exactly to the image of the positive overlap generator;
no coordinate or sign information is discarded. -/
theorem radialMV_boundary_eq_iff_one (P : PairingData) :
    radialMVBoundaryGroup P = attachingBoundaryGroup P ↔
      radialMVBoundaryGroup P 1 = attachingDegree P := by
  constructor
  · intro h
    rw [h]
    rw [attachingBoundaryGroup_apply]
    simp
  · intro h
    apply addCommGrpHom_int_ext
    exact h.trans (by
      simpa using (attachingBoundaryGroup_apply P 1).symm)

/-- The uncoordinatized outer-piece H₁ class obtained by including the
positive overlap generator into the outer member of the radial cover. -/
noncomputable def radialOuterBoundaryGenerator (P : PairingData) :
    ConstructionTargets.SingularHomologyConcrete.SingularHomology 1
      (TopCat.of (OuterPiece P)) :=
  (biprod.snd : _ ⟶
    ConstructionTargets.SingularHomologyConcrete.SingularHomology 1
      (TopCat.of (OuterPiece P)))
    (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionIntersectionArrow
      (openCover P).inner (openCover P).outer 1
      ((radialIntersectionH1GroupIsoInt P).inv 1))

/-- The raw outer-piece class whose fixed coordinates are the signed
attaching-degree vector. -/
noncomputable def attachingOuterClass (P : PairingData) :
    ConstructionTargets.SingularHomologyConcrete.SingularHomology 1
      (TopCat.of (OuterPiece P)) :=
  (radialOuterH1GroupIsoCoordinates P).inv (attachingDegree P)

theorem radialMVBoundaryGroup_one_formula (P : PairingData) :
    radialMVBoundaryGroup P 1 =
      (radialOuterH1GroupIsoCoordinates P).hom
        (radialOuterBoundaryGenerator P) := by
  change (radialOuterH1GroupIsoCoordinates P).hom.hom
    (radialOuterBoundaryGenerator P) = _
  rfl

/-- The remaining generator computation can equivalently be carried out
before outer-piece coordinates are applied. -/
theorem radialMVBoundaryGroup_one_iff_outerClass (P : PairingData) :
    radialMVBoundaryGroup P 1 = attachingDegree P ↔
      radialOuterBoundaryGenerator P = attachingOuterClass P := by
  rw [radialMVBoundaryGroup_one_formula]
  constructor
  · intro h
    apply_fun (radialOuterH1GroupIsoCoordinates P).inv at h
    simpa [attachingOuterClass] using h
  · intro h
    rw [h, attachingOuterClass]
    simp

/-- The unsigned inclusion-induced H₁ map from the radial intersection to
the outer cover member.  The production MV arrow uses its negative. -/
noncomputable def radialIntersectionToOuterH1 (P : PairingData) :
    ConstructionTargets.SingularHomologyConcrete.SingularHomology 1
        (TopCat.of {q // q ∈ (openCover P).inner ∩ (openCover P).outer}) ⟶
      ConstructionTargets.SingularHomologyConcrete.SingularHomology 1
        (TopCat.of (OuterPiece P)) :=
  HomologicalComplex.homologyMap
    (((AlgebraicTopology.SSet.singularChainComplexFunctor AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ)).map
      (TopCat.toSSet.map
        (ConstructionTargets.SingularExcision.topologicalSubspaceInclusion
          (Set.inter_subset_right)))) 1

/-- The chosen intersection generator is carried by the unsigned outer
inclusion to the explicit positive overlap circle class. -/
theorem radialIntersectionToOuterH1_positiveGenerator_eq (P : PairingData) :
    radialIntersectionToOuterH1 P
        ((radialIntersectionH1GroupIsoInt P).inv 1) =
      singularH1Map (radialOverlapCircleInOuter P)
        (circleGroupH1IsoInt.inv 1) := by
  rw [radialIntersectionPositiveGenerator_eq]
  change singularH1Map
      (⟨fun q => ⟨q.1, q.2.2⟩, by fun_prop⟩ :
        C({q // q ∈ (openCover P).inner ∩ (openCover P).outer}, OuterPiece P))
      (singularH1Map (radialIntersectionPositiveCircle P)
        (circleGroupH1IsoInt.inv 1)) = _
  change (singularH1Map (radialIntersectionPositiveCircle P) ≫
      singularH1Map
        (⟨fun q => ⟨q.1, q.2.2⟩, by fun_prop⟩ :
          C({q // q ∈ (openCover P).inner ∩ (openCover P).outer}, OuterPiece P)))
      (circleGroupH1IsoInt.inv 1) = _
  rw [← singularH1Map_comp]
  rfl

/-- After applying the fixed outer deformation coordinates, the chosen
intersection generator becomes the H₁ class of the ordered polygon boundary
loop. -/
theorem radialIntersectionToOuterH1_generator_eq_boundaryLoop (P : PairingData) :
    singularH1Map (outerHomotopyEquivWedge P).toFun
        (radialIntersectionToOuterH1 P
          ((radialIntersectionH1GroupIsoInt P).inv 1)) =
      singularH1Map (polygonBoundaryWedgeLoop P)
        (circleGroupH1IsoInt.inv 1) := by
  rw [radialIntersectionToOuterH1_positiveGenerator_eq]
  change (singularH1Map (radialOverlapCircleInOuter P) ≫
      singularH1Map (outerHomotopyEquivWedge P).toFun)
      (circleGroupH1IsoInt.inv 1) = _
  rw [radialOverlapCircle_h1_naturality]

/-- The outer projection of the production intersection arrow is literally
the negative outer inclusion, fixing the MV sign before the geometric loop
calculation begins. -/
theorem radialIntersectionArrow_snd (P : PairingData) :
    ConstructionTargets.ProductionOpenCoverMayerVietoris.productionIntersectionArrow
          (openCover P).inner (openCover P).outer 1 ≫
        (Limits.biprod.snd :
          (ConstructionTargets.SingularHomologyConcrete.SingularHomology 1
              (TopCat.of (InnerPiece P)) ⊞
            ConstructionTargets.SingularHomologyConcrete.SingularHomology 1
              (TopCat.of (OuterPiece P))) ⟶
          ConstructionTargets.SingularHomologyConcrete.SingularHomology 1
            (TopCat.of (OuterPiece P))) =
      -radialIntersectionToOuterH1 P := by
  change Limits.biprod.lift _ (-radialIntersectionToOuterH1 P) ≫
      Limits.biprod.snd = -radialIntersectionToOuterH1 P
  simp

theorem radialOuterBoundaryGenerator_eq_neg_inclusion (P : PairingData) :
    radialOuterBoundaryGenerator P =
      -radialIntersectionToOuterH1 P
        ((radialIntersectionH1GroupIsoInt P).inv 1) := by
  change
    (ConstructionTargets.ProductionOpenCoverMayerVietoris.productionIntersectionArrow
          (openCover P).inner (openCover P).outer 1 ≫ Limits.biprod.snd)
        ((radialIntersectionH1GroupIsoInt P).inv 1) = _
  have h := congrArg ConcreteCategory.hom (radialIntersectionArrow_snd P)
  have hx := congrArg
    (fun f => f ((radialIntersectionH1GroupIsoInt P).inv 1)) h
  simpa using hx

/-- Consequently the remaining raw B7 equality is exactly the statement
that the unsigned outer inclusion has the negative attaching class. -/
theorem radialOuterBoundaryGenerator_eq_attachingOuterClass_iff (P : PairingData) :
    radialOuterBoundaryGenerator P = attachingOuterClass P ↔
      radialIntersectionToOuterH1 P
          ((radialIntersectionH1GroupIsoInt P).inv 1) =
        -attachingOuterClass P := by
  rw [radialOuterBoundaryGenerator_eq_neg_inclusion]
  constructor <;> intro h
  · simpa only [neg_eq_iff_eq_neg] using h
  · simpa only [neg_eq_iff_eq_neg] using h

end

end ConstructionTargets.PolygonSurfaceHomology
