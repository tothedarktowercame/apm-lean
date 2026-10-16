import ConstructionTargets.PolygonSurfaceHomology
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Data.ZMod.Basic

/-! Compiled closure infrastructure for t94J09. -/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.t94J09Closure

open ConstructionTargets.PolygonSurfacePiOne
open ConstructionTargets.PolygonSurfaceHomology

/-- The standard one-vertex twelve-gon for the nonorientable genus-six
surface. -/
def n6PairingData : PairingData :=
  nonorientableStandardPairingData 6 (by omega)

/-! ## The frozen fourteen-edge pairing

The consumer's polygon has two vertex classes, so it does not satisfy the
`PairingData.oneVertex` field used by the existing radial homology theorem.
We nevertheless record its exact edge involution and seven edge orbits.  This
is the degree-one coordinate system for the required two-vertex extension of
that theorem. -/

/-- The edge involution read literally from the frozen fourteen-edge word. -/
def frozenPairIndex (i : Fin 14) : Fin 14 :=
  ![12, 7, 8, 9, 11, 10, 13, 1, 2, 3, 5, 4, 0, 6] i

theorem frozenPairIndex_involutive : Function.Involutive frozenPairIndex := by
  intro i
  fin_cases i <;> rfl

/-- The frozen edge pairing as a permutation. -/
def frozenPair : Equiv.Perm (Fin 14) where
  toFun := frozenPairIndex
  invFun := frozenPairIndex
  left_inv := frozenPairIndex_involutive
  right_inv := frozenPairIndex_involutive

@[simp] theorem frozenPair_apply (i : Fin 14) :
    frozenPair i = frozenPairIndex i := rfl

/-- Orientations of the fourteen occurrences in the frozen word. -/
def frozenSign : Fin 14 → Bool :=
  ![true, true, false, false, true, false, true,
    false, false, false, false, true, true, true]

/-- Only the `c` pairing reverses its interval parameter; every other frozen
pairing preserves it. -/
theorem frozen_pairedParameter (i : Fin 14) (t : Set.Icc (0 : ℝ) 1) :
    pairedParameter frozenPair frozenSign i t =
      if i = 1 ∨ i = 7 then reverseIcc t else t := by
  fin_cases i <;>
    simp [pairedParameter, frozenPair, frozenPairIndex, frozenSign]

/-- The generic signed-polygon relation specializes literally to the frozen
fourteen-edge pairing and its sole reversed pair. -/
theorem frozen_boundaryRel_iff (x y : Surfaces.Disk) :
    boundaryRel 14 frozenPair frozenSign x y ↔
      ∃ i : Fin 14, ∃ t : Set.Icc (0 : ℝ) 1,
        x = Surfaces.edgePoint 14 i t ∧
          y = Surfaces.edgePoint 14 (frozenPair i)
            (if i = 1 ∨ i = 7 then reverseIcc t else t) := by
  simp only [boundaryRel]
  constructor
  · rintro ⟨i, t, rfl, rfl⟩
    exact ⟨i, t, rfl, by rw [frozen_pairedParameter]⟩
  · rintro ⟨i, t, rfl, rfl⟩
    exact ⟨i, t, rfl, by rw [frozen_pairedParameter]⟩

/-- The seven canonically oriented generators of the frozen polygon relation. -/
def frozenGeneratorRel (x y : Surfaces.Disk) : Prop :=
  ∃ t : Set.Icc (0 : ℝ) 1,
    (x = Surfaces.edgePoint 14 0 t ∧ y = Surfaces.edgePoint 14 12 t) ∨
    (x = Surfaces.edgePoint 14 6 t ∧ y = Surfaces.edgePoint 14 13 t) ∨
    (x = Surfaces.edgePoint 14 1 t ∧
      y = Surfaces.edgePoint 14 7 (reverseIcc t)) ∨
    (x = Surfaces.edgePoint 14 2 t ∧ y = Surfaces.edgePoint 14 8 t) ∨
    (x = Surfaces.edgePoint 14 5 t ∧ y = Surfaces.edgePoint 14 10 t) ∨
    (x = Surfaces.edgePoint 14 4 t ∧ y = Surfaces.edgePoint 14 11 t) ∨
    (x = Surfaces.edgePoint 14 3 t ∧ y = Surfaces.edgePoint 14 9 t)

/-- Every frozen generator identifies boundary points of the same radius. -/
theorem frozenGeneratorRel_radius_eq {x y : Surfaces.Disk}
    (h : frozenGeneratorRel x y) :
    PolygonRadialOpenCover.radius x = PolygonRadialOpenCover.radius y := by
  rcases h with ⟨t, h | h | h | h | h | h | h⟩ <;>
    rcases h with ⟨rfl, rfl⟩ <;>
    simp [PolygonRadialOpenCover.radius, norm_edgePoint]

/-- The genuine radial two-open cover of the explicit frozen generator
quotient. -/
def frozenGeneratorRadialPackage :
    PolygonRadialOpenCover.Package frozenGeneratorRel
      (fun {_ _} h => frozenGeneratorRel_radius_eq h) :=
  PolygonRadialOpenCover.package frozenGeneratorRel
    (fun {_ _} h => frozenGeneratorRel_radius_eq h)

/-- Every frozen generator identifies points on the polygon boundary. -/
theorem frozenGeneratorRel_boundary {x y : Surfaces.Disk}
    (h : frozenGeneratorRel x y) :
    PolygonRadialOpenCover.radius x = 1 ∧
      PolygonRadialOpenCover.radius y = 1 := by
  rcases h with ⟨t, h | h | h | h | h | h | h⟩ <;>
    rcases h with ⟨rfl, rfl⟩ <;>
    simp [PolygonRadialOpenCover.radius, norm_edgePoint]

/-- The inner member of the frozen generator radial cover. -/
abbrev FrozenGeneratorInnerPiece :=
  {q // q ∈ PolygonRadialOpenCover.innerOpen frozenGeneratorRel}

/-- The annular intersection of the frozen generator radial cover. -/
abbrev FrozenGeneratorOverlapPiece :=
  PolygonRadialOpenCover.overlapOpen frozenGeneratorRel

/-- The literal frozen inner piece contracts to its center. -/
def frozenGeneratorInnerHomotopyEquivPoint :
    ContinuousMap.HomotopyEquiv FrozenGeneratorInnerPiece Unit where
  toFun := ContinuousMap.const FrozenGeneratorInnerPiece ()
  invFun := ContinuousMap.const Unit
    (ConstructionTargets.PolygonInnerOpenPointedContraction.innerBase
      frozenGeneratorRel)
  left_inv := ⟨(ConstructionTargets.PolygonInnerOpenPointedContraction.innerOpenPointedContraction
      frozenGeneratorRel
      (fun {_ _} h => frozenGeneratorRel_radius_eq h)
      (fun {_ _} h => frozenGeneratorRel_boundary h)).homotopy.symm⟩
  right_inv := by
    rw [show (ContinuousMap.const FrozenGeneratorInnerPiece ()).comp
        (ContinuousMap.const Unit
          (ConstructionTargets.PolygonInnerOpenPointedContraction.innerBase
            frozenGeneratorRel)) =
        ContinuousMap.id Unit by
      apply ContinuousMap.ext
      intro u
      exact Subsingleton.elim _ _]

/-- The literal frozen overlap has the homotopy type of the positive circle. -/
def frozenGeneratorOverlapHomotopyEquivCircle :
    ContinuousMap.HomotopyEquiv FrozenGeneratorOverlapPiece Circle :=
  (ConstructionTargets.PolygonOverlapHomotopyEquivCircle.overlapHomotopyEquivCircle
      frozenGeneratorRel
      (fun {_ _} h => frozenGeneratorRel_radius_eq h)
      (fun {_ _} h => frozenGeneratorRel_boundary h)).symm

/-- Zeroth homology of the frozen inner piece. -/
noncomputable def frozenGeneratorInnerH0IsoInt :
    SpaceH FrozenGeneratorInnerPiece 0 ≅ ModuleCat.of ℤ ℤ :=
  ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsoOfGroupIso
      (TopCat.of FrozenGeneratorInnerPiece) 0 (ModuleCat.of ℤ ℤ)
      (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
          frozenGeneratorInnerHomotopyEquivPoint 0 ≪≫
        ConstructionTargets.SingularHomologyConcrete.pointH0IsoInt)

/-- Positive-degree homology of the frozen inner piece vanishes. -/
theorem frozenGeneratorInnerHigherHomology_isZero (k : ℕ) (hk : k ≠ 0) :
    IsZero (SpaceH FrozenGeneratorInnerPiece k) := by
  apply ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsZeroOfGroupIsZero
  exact (ConstructionTargets.SingularHomologyConcrete.pointHigherHomology_isZero
      k hk).of_iso
      (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
          frozenGeneratorInnerHomotopyEquivPoint k)

/-- Zeroth homology of the frozen annular overlap. -/
noncomputable def frozenGeneratorOverlapH0IsoInt :
    SpaceH FrozenGeneratorOverlapPiece 0 ≅ ModuleCat.of ℤ ℤ :=
  ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsoOfGroupIso
      (TopCat.of FrozenGeneratorOverlapPiece) 0 (ModuleCat.of ℤ ℤ)
      (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
          frozenGeneratorOverlapHomotopyEquivCircle 0 ≪≫
        circleGroupH0IsoInt)

/-- First homology of the frozen annular overlap. -/
noncomputable def frozenGeneratorOverlapH1IsoInt :
    SpaceH FrozenGeneratorOverlapPiece 1 ≅ ModuleCat.of ℤ ℤ :=
  ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsoOfGroupIso
      (TopCat.of FrozenGeneratorOverlapPiece) 1 (ModuleCat.of ℤ ℤ)
      (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
          frozenGeneratorOverlapHomotopyEquivCircle 1 ≪≫
        circleGroupH1IsoInt)

/-- Homology of the frozen annular overlap vanishes above degree one. -/
theorem frozenGeneratorOverlapHigherHomology_isZero (k : ℕ) (hk : 1 < k) :
    IsZero (SpaceH FrozenGeneratorOverlapPiece k) := by
  apply ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsZeroOfGroupIsZero
  exact (ConstructionTargets.SphereHomology.sphereHomology_isZero_of_gt
      1 k hk).of_iso
      ((ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
          frozenGeneratorOverlapHomotopyEquivCircle k).trans
        (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
            ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.toHomotopyEquiv
              k))

/-- The complete homology table for the inner and overlap members of the
literal frozen radial cover. -/
theorem frozenGeneratorInnerOverlapHomology :
    Nonempty (SpaceH FrozenGeneratorInnerPiece 0 ≅ ModuleCat.of ℤ ℤ) ∧
    (∀ k : ℕ, k ≠ 0 → IsZero (SpaceH FrozenGeneratorInnerPiece k)) ∧
    Nonempty (SpaceH FrozenGeneratorOverlapPiece 0 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (SpaceH FrozenGeneratorOverlapPiece 1 ≅ ModuleCat.of ℤ ℤ) ∧
    (∀ k : ℕ, 1 < k →
      IsZero (SpaceH FrozenGeneratorOverlapPiece k)) := by
  exact ⟨⟨frozenGeneratorInnerH0IsoInt⟩,
    frozenGeneratorInnerHigherHomology_isZero,
    ⟨frozenGeneratorOverlapH0IsoInt⟩,
    ⟨frozenGeneratorOverlapH1IsoInt⟩,
    frozenGeneratorOverlapHigherHomology_isZero⟩

/-- The outer member of the literal frozen radial cover. -/
abbrev FrozenGeneratorOuterPiece :=
  PolygonRadialOpenCover.outerOpen frozenGeneratorRel

/-- Boundary classes inside the literal frozen outer member. -/
def frozenGeneratorOuterBoundarySkeleton :
    Set FrozenGeneratorOuterPiece :=
  {z | ConstructionTargets.PolygonOuterOpenDeformation.IsBoundaryClass
    frozenGeneratorRel
      (fun {_ _} h => frozenGeneratorRel_radius_eq h) z}

/-- The boundary skeleton as a topological subspace of the outer member. -/
abbrev FrozenGeneratorOuterBoundaryPiece :=
  {z : FrozenGeneratorOuterPiece //
    z ∈ frozenGeneratorOuterBoundarySkeleton}

/-- The generic radial deformation specialized to the literal frozen
two-vertex relation. -/
def frozenGeneratorOuterHomotopy :
    C(unitInterval × FrozenGeneratorOuterPiece,
      FrozenGeneratorOuterPiece) :=
  ⟨ConstructionTargets.PolygonOuterOpenDeformation.outerOpenHomotopy
      frozenGeneratorRel
      (fun {_ _} h => frozenGeneratorRel_radius_eq h)
      (fun {_ _} h => frozenGeneratorRel_boundary h),
    ConstructionTargets.PolygonOuterOpenDeformation.continuous_outerOpenHomotopy
        frozenGeneratorRel
        (fun {_ _} h => frozenGeneratorRel_radius_eq h)
        (fun {_ _} h => frozenGeneratorRel_boundary h)⟩

/-- The literal frozen outer member has the homotopy type of its two-vertex,
seven-edge boundary graph. -/
def frozenGeneratorOuterHomotopyEquivBoundary :
    ContinuousMap.HomotopyEquiv FrozenGeneratorOuterPiece
      FrozenGeneratorOuterBoundaryPiece where
  toFun :=
    { toFun := fun z =>
        ⟨frozenGeneratorOuterHomotopy (1, z),
          ConstructionTargets.PolygonOuterOpenDeformation.outerOpenHomotopy_one_boundary
              frozenGeneratorRel
              (fun {_ _} h => frozenGeneratorRel_radius_eq h)
              (fun {_ _} h => frozenGeneratorRel_boundary h) z⟩
      continuous_toFun := by fun_prop }
  invFun :=
    { toFun := fun z => z.1
      continuous_toFun := continuous_subtype_val }
  left_inv := by
    let H :
        ContinuousMap.Homotopy (ContinuousMap.id FrozenGeneratorOuterPiece)
          ((ContinuousMap.mk
              (fun z : FrozenGeneratorOuterBoundaryPiece => z.1)
              continuous_subtype_val).comp
            (ContinuousMap.mk
              (fun z : FrozenGeneratorOuterPiece =>
                ⟨frozenGeneratorOuterHomotopy (1, z),
                  ConstructionTargets.PolygonOuterOpenDeformation.outerOpenHomotopy_one_boundary
                      frozenGeneratorRel
                      (fun {_ _} h => frozenGeneratorRel_radius_eq h)
                      (fun {_ _} h => frozenGeneratorRel_boundary h) z⟩)
              (by fun_prop))) :=
      { toFun := fun p => frozenGeneratorOuterHomotopy p
        continuous_toFun := frozenGeneratorOuterHomotopy.continuous
        map_zero_left := ConstructionTargets.PolygonOuterOpenDeformation.outerOpenHomotopy_zero
            frozenGeneratorRel
            (fun {_ _} h => frozenGeneratorRel_radius_eq h)
            (fun {_ _} h => frozenGeneratorRel_boundary h)
        map_one_left := by intro z; rfl }
    exact ⟨H.symm⟩
  right_inv := by
    have hmap :
        (ContinuousMap.mk
            (fun z : FrozenGeneratorOuterPiece =>
              ⟨frozenGeneratorOuterHomotopy (1, z),
                ConstructionTargets.PolygonOuterOpenDeformation.outerOpenHomotopy_one_boundary
                    frozenGeneratorRel
                    (fun {_ _} h => frozenGeneratorRel_radius_eq h)
                    (fun {_ _} h => frozenGeneratorRel_boundary h) z⟩)
            (by fun_prop)).comp
          (ContinuousMap.mk
            (fun z : FrozenGeneratorOuterBoundaryPiece => z.1)
            continuous_subtype_val) =
          ContinuousMap.id FrozenGeneratorOuterBoundaryPiece := by
      apply ContinuousMap.ext
      intro z
      apply Subtype.ext
      exact ConstructionTargets.PolygonOuterOpenDeformation.outerOpenHomotopy_fixed
          frozenGeneratorRel
          (fun {_ _} h => frozenGeneratorRel_radius_eq h)
          (fun {_ _} h => frozenGeneratorRel_boundary h) 1 z.1 z.2
    rw [hmap]

/-- Singular homology transports from the literal frozen outer member to its
boundary graph in every degree. -/
noncomputable def frozenGeneratorOuterHomologyIsoBoundary (k : ℕ) :
    SpaceH FrozenGeneratorOuterPiece k ≅
      SpaceH FrozenGeneratorOuterBoundaryPiece k :=
  ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyModuleIsoOfGroupIso
    (TopCat.of FrozenGeneratorOuterPiece) k
      (SpaceH FrozenGeneratorOuterBoundaryPiece k)
    (ConstructionTargets.SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv
      frozenGeneratorOuterHomotopyEquivBoundary k ≪≫
        (ConstructionTargets.IntegralSingularHomologyComparison.singularHomologyComparison
            (TopCat.of FrozenGeneratorOuterBoundaryPiece) k).symm)

/-- Circle-source presentation of the literal frozen boundary quotient. -/
abbrev FrozenGeneratorCircleQuotient :=
  ConstructionTargets.PolygonBoundaryInducedQuotient.CircleQuotient
    frozenGeneratorRel

/-- Boundary-subtype presentation of the literal frozen boundary quotient. -/
abbrev FrozenGeneratorBoundaryQuotient :=
  ConstructionTargets.PolygonBoundaryInducedQuotient.BoundaryQuotient
    frozenGeneratorRel

/-- Passing through the standard circle parametrization preserves the exact
frozen boundary quotient topology. -/
def frozenGeneratorCircleBoundaryHomeomorph :
    FrozenGeneratorCircleQuotient ≃ₜ FrozenGeneratorBoundaryQuotient :=
  ConstructionTargets.PolygonBoundaryInducedQuotient.circleBoundaryQuotientHomeomorph
    frozenGeneratorRel

/-- The circle and disk-boundary presentations have canonically isomorphic
integral singular homology in every degree. -/
def frozenGeneratorCircleBoundaryHomologyIso (k : ℕ) :
    SpaceH FrozenGeneratorCircleQuotient k ≅
      SpaceH FrozenGeneratorBoundaryQuotient k :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
      (ModuleCat.of ℤ ℤ)).mapIso
    (TopCat.isoOfHomeo frozenGeneratorCircleBoundaryHomeomorph))

/-- The point on the boundary of the frozen fourteen-gon with edge coordinate
`t` on edge `j`. -/
def frozenBoundaryEdgePoint (j : Fin 14) (t : Set.Icc (0 : ℝ) 1) :
    ConstructionTargets.PolygonBoundaryCircleSource.Boundary :=
  ⟨Surfaces.edgePoint 14 j t, by
    simpa [PolygonRadialOpenCover.radius] using norm_edgePoint 14 j t⟩

/-- The corresponding point in the standard circle source. -/
def frozenCircleEdgePoint (j : Fin 14) (t : Set.Icc (0 : ℝ) 1) : Circle :=
  ConstructionTargets.PolygonBoundaryCircleSource.boundaryToCircle
    (frozenBoundaryEdgePoint j t)

@[simp] theorem circleToBoundary_frozenCircleEdgePoint
    (j : Fin 14) (t : Set.Icc (0 : ℝ) 1) :
    ConstructionTargets.PolygonBoundaryCircleSource.circleToBoundary
        (frozenCircleEdgePoint j t) = frozenBoundaryEdgePoint j t :=
  ConstructionTargets.PolygonBoundaryCircleSource.circleToBoundary_boundaryToCircle _

/-- The seven literal pairings hold in the induced circle relation. -/
theorem frozenGeneratorCircleRel_generators (t : Set.Icc (0 : ℝ) 1) :
    let R := ConstructionTargets.PolygonBoundaryInducedQuotient.CircleRel
      frozenGeneratorRel
    R (frozenCircleEdgePoint 0 t) (frozenCircleEdgePoint 12 t) ∧
    R (frozenCircleEdgePoint 6 t) (frozenCircleEdgePoint 13 t) ∧
    R (frozenCircleEdgePoint 1 t)
      (frozenCircleEdgePoint 7 (reverseIcc t)) ∧
    R (frozenCircleEdgePoint 2 t) (frozenCircleEdgePoint 8 t) ∧
    R (frozenCircleEdgePoint 5 t) (frozenCircleEdgePoint 10 t) ∧
    R (frozenCircleEdgePoint 4 t) (frozenCircleEdgePoint 11 t) ∧
    R (frozenCircleEdgePoint 3 t) (frozenCircleEdgePoint 9 t) := by
  dsimp [ConstructionTargets.PolygonBoundaryInducedQuotient.CircleRel,
    ConstructionTargets.PolygonBoundaryInducedQuotient.BoundaryRel]
  simp only [circleToBoundary_frozenCircleEdgePoint, frozenBoundaryEdgePoint]
  exact ⟨⟨t, Or.inl ⟨rfl, rfl⟩⟩,
    ⟨t, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩,
    ⟨t, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩,
    ⟨t, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩,
    ⟨t, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩,
    ⟨t, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))⟩,
    ⟨t, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))⟩⟩

/-- The quotient map identifies the seven displayed pairs needed for the
two-vertex, seven-edge boundary graph presentation. -/
theorem frozenGeneratorCircleQuotient_identifies_generators
    (t : Set.Icc (0 : ℝ) 1) :
    let q : Circle → FrozenGeneratorCircleQuotient := Quotient.mk _
    q (frozenCircleEdgePoint 0 t) = q (frozenCircleEdgePoint 12 t) ∧
    q (frozenCircleEdgePoint 6 t) = q (frozenCircleEdgePoint 13 t) ∧
    q (frozenCircleEdgePoint 1 t) =
      q (frozenCircleEdgePoint 7 (reverseIcc t)) ∧
    q (frozenCircleEdgePoint 2 t) = q (frozenCircleEdgePoint 8 t) ∧
    q (frozenCircleEdgePoint 5 t) = q (frozenCircleEdgePoint 10 t) ∧
    q (frozenCircleEdgePoint 4 t) = q (frozenCircleEdgePoint 11 t) ∧
    q (frozenCircleEdgePoint 3 t) = q (frozenCircleEdgePoint 9 t) := by
  dsimp only
  rcases frozenGeneratorCircleRel_generators t with
    ⟨h0, h1, h2, h3, h4, h5, h6⟩
  exact ⟨Quotient.sound (Relation.EqvGen.rel _ _ h0),
    Quotient.sound (Relation.EqvGen.rel _ _ h1),
    Quotient.sound (Relation.EqvGen.rel _ _ h2),
    Quotient.sound (Relation.EqvGen.rel _ _ h3),
    Quotient.sound (Relation.EqvGen.rel _ _ h4),
    Quotient.sound (Relation.EqvGen.rel _ _ h5),
    Quotient.sound (Relation.EqvGen.rel _ _ h6)⟩

/-- The explicit seven-edge relation on the circle source.  This is kept
separate from the disk relation so the boundary graph can be constructed
without referring back to interior disk points. -/
def FrozenBoundaryGraphRel (z w : Circle) : Prop :=
  ∃ t : Set.Icc (0 : ℝ) 1,
    (z = frozenCircleEdgePoint 0 t ∧ w = frozenCircleEdgePoint 12 t) ∨
    (z = frozenCircleEdgePoint 6 t ∧ w = frozenCircleEdgePoint 13 t) ∨
    (z = frozenCircleEdgePoint 1 t ∧
      w = frozenCircleEdgePoint 7 (reverseIcc t)) ∨
    (z = frozenCircleEdgePoint 2 t ∧ w = frozenCircleEdgePoint 8 t) ∨
    (z = frozenCircleEdgePoint 5 t ∧ w = frozenCircleEdgePoint 10 t) ∨
    (z = frozenCircleEdgePoint 4 t ∧ w = frozenCircleEdgePoint 11 t) ∨
    (z = frozenCircleEdgePoint 3 t ∧ w = frozenCircleEdgePoint 9 t)

@[simp] theorem eq_frozenCircleEdgePoint_iff (z : Circle) (j : Fin 14)
    (t : Set.Icc (0 : ℝ) 1) :
    z = frozenCircleEdgePoint j t ↔
      (ConstructionTargets.PolygonBoundaryCircleSource.circleToBoundary z).1 =
        Surfaces.edgePoint 14 j t := by
  constructor
  · rintro rfl
    rfl
  · intro h
    apply ConstructionTargets.PolygonBoundaryCircleSource.boundaryCircleHomeomorph.injective
    exact Subtype.ext h

/-- The induced circle relation is exactly the explicit seven-edge graph
relation, not merely a relation containing its generators. -/
theorem frozenGeneratorCircleRel_iff_graphRel (z w : Circle) :
    ConstructionTargets.PolygonBoundaryInducedQuotient.CircleRel
        frozenGeneratorRel z w ↔ FrozenBoundaryGraphRel z w := by
  simp only [ConstructionTargets.PolygonBoundaryInducedQuotient.CircleRel,
    ConstructionTargets.PolygonBoundaryInducedQuotient.BoundaryRel,
    frozenGeneratorRel, FrozenBoundaryGraphRel, eq_frozenCircleEdgePoint_iff]
  norm_num

/-- Equivalence closure preserves the exact circle-to-graph relation
comparison. -/
theorem frozenGeneratorCircleEqvGen_iff_graphEqvGen (z w : Circle) :
    Relation.EqvGen
        (ConstructionTargets.PolygonBoundaryInducedQuotient.CircleRel
          frozenGeneratorRel) z w ↔
      Relation.EqvGen FrozenBoundaryGraphRel z w := by
  constructor
  · exact ConstructionTargets.PolygonBoundaryInducedQuotient.eqvGen_map
      _ _ id (fun {_ _} h => (frozenGeneratorCircleRel_iff_graphRel _ _).mp h)
  · exact ConstructionTargets.PolygonBoundaryInducedQuotient.eqvGen_map
      _ _ id (fun {_ _} h => (frozenGeneratorCircleRel_iff_graphRel _ _).mpr h)

/-- Quotient of the circle by the explicit seven-edge boundary graph
relation. -/
abbrev FrozenBoundaryGraphQuotient :=
  Quotient (Relation.EqvGen.setoid FrozenBoundaryGraphRel)

noncomputable instance : TopologicalSpace FrozenBoundaryGraphQuotient :=
  TopologicalSpace.coinduced (fun z : Circle => Quotient.mk _ z) inferInstance

/-- The induced boundary quotient and explicit graph quotient agree by the
identity on circle representatives, including their quotient topologies. -/
def frozenGeneratorCircleHomeomorphBoundaryGraph :
    FrozenGeneratorCircleQuotient ≃ₜ FrozenBoundaryGraphQuotient where
  toFun := Quotient.map id (by
    intro z w h
    exact (frozenGeneratorCircleEqvGen_iff_graphEqvGen z w).mp h)
  invFun := Quotient.map id (by
    intro z w h
    exact (frozenGeneratorCircleEqvGen_iff_graphEqvGen z w).mpr h)
  left_inv := by
    rintro ⟨z⟩
    rfl
  right_inv := by
    rintro ⟨z⟩
    rfl
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng
  continuous_invFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng

@[simp] theorem frozenGeneratorCircleHomeomorphBoundaryGraph_mk (z : Circle) :
    frozenGeneratorCircleHomeomorphBoundaryGraph
        (Quotient.mk _ z) = Quotient.mk _ z := rfl

/-- Integral singular homology transports from the induced circle quotient
to the explicit seven-edge graph quotient in every degree. -/
def frozenGeneratorCircleHomologyIsoBoundaryGraph (k : ℕ) :
    SpaceH FrozenGeneratorCircleQuotient k ≅
      SpaceH FrozenBoundaryGraphQuotient k :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
      (ModuleCat.of ℤ ℤ)).mapIso
    (TopCat.isoOfHomeo frozenGeneratorCircleHomeomorphBoundaryGraph))

/-- Direct homology comparison from the disk-boundary quotient presentation
to the explicit seven-edge graph presentation. -/
def frozenGeneratorBoundaryHomologyIsoGraph (k : ℕ) :
    SpaceH FrozenGeneratorBoundaryQuotient k ≅
      SpaceH FrozenBoundaryGraphQuotient k :=
  (frozenGeneratorCircleBoundaryHomologyIso k).symm ≪≫
    frozenGeneratorCircleHomologyIsoBoundaryGraph k

/-- The generic signed relation is precisely the symmetric closure of the
seven frozen generators.  This is the relation-level comparison needed to
reuse the radial quotient construction for the consumer's inductive relation. -/
theorem frozen_boundaryRel_iff_generator (x y : Surfaces.Disk) :
    boundaryRel 14 frozenPair frozenSign x y ↔
      frozenGeneratorRel x y ∨ frozenGeneratorRel y x := by
  rw [frozen_boundaryRel_iff]
  constructor
  · rintro ⟨i, t, rfl, rfl⟩
    fin_cases i
    · left; exact ⟨t, Or.inl ⟨rfl, rfl⟩⟩
    · left; exact ⟨t, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    · left; exact ⟨t, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
    · left; exact ⟨t, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))⟩
    · left; exact ⟨t, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))⟩
    · left; exact ⟨t, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
    · left; exact ⟨t, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · right; refine ⟨reverseIcc t, Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))⟩
      simp
    · right; exact ⟨t, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
    · right; exact ⟨t, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))⟩
    · right; exact ⟨t, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))⟩
    · right; exact ⟨t, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))⟩
    · right; exact ⟨t, Or.inl ⟨rfl, rfl⟩⟩
    · right; exact ⟨t, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · rintro (h | h) <;> rcases h with ⟨t, h⟩
    · rcases h with h | h | h | h | h | h | h
      · exact ⟨0, t, h.1, h.2⟩
      · exact ⟨6, t, h.1, h.2⟩
      · exact ⟨1, t, h.1, h.2⟩
      · exact ⟨2, t, h.1, h.2⟩
      · exact ⟨5, t, h.1, h.2⟩
      · exact ⟨4, t, h.1, h.2⟩
      · exact ⟨3, t, h.1, h.2⟩
    · rcases h with h | h | h | h | h | h | h
      · exact ⟨12, t, h.2, h.1⟩
      · exact ⟨13, t, h.2, h.1⟩
      · refine ⟨7, reverseIcc t, h.2, ?_⟩
        simpa using h.1
      · exact ⟨8, t, h.2, h.1⟩
      · exact ⟨10, t, h.2, h.1⟩
      · exact ⟨11, t, h.2, h.1⟩
      · exact ⟨9, t, h.2, h.1⟩

/-- Passing to equivalence closure removes the explicit symmetry added by the
generic signed relation, so both presentations define the same quotient. -/
theorem frozen_eqvGen_boundaryRel_iff_generator (x y : Surfaces.Disk) :
    Relation.EqvGen (boundaryRel 14 frozenPair frozenSign) x y ↔
      Relation.EqvGen frozenGeneratorRel x y := by
  constructor
  · intro h
    induction h with
    | rel a b hab =>
        rcases (frozen_boundaryRel_iff_generator a b).mp hab with hab | hba
        · exact Relation.EqvGen.rel _ _ hab
        · exact (Relation.EqvGen.rel _ _ hba).symm
    | refl a => exact Relation.EqvGen.refl a
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans a b c ih₁ ih₂
  · intro h
    induction h with
    | rel a b hab =>
        exact Relation.EqvGen.rel _ _
          ((frozen_boundaryRel_iff_generator a b).mpr (Or.inl hab))
    | refl a => exact Relation.EqvGen.refl a
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans a b c ih₁ ih₂

/-- Quotient carrier for the generic signed frozen relation. -/
abbrev FrozenSignedQuotient :=
  Quotient (Relation.EqvGen.setoid (boundaryRel 14 frozenPair frozenSign))

/-- Quotient carrier for the seven explicitly oriented frozen generators. -/
abbrev FrozenGeneratorQuotient :=
  Quotient (Relation.EqvGen.setoid frozenGeneratorRel)

noncomputable instance : TopologicalSpace FrozenSignedQuotient :=
  TopologicalSpace.coinduced
    (fun x : Surfaces.Disk => Quotient.mk _ x) inferInstance

noncomputable instance : TopologicalSpace FrozenGeneratorQuotient :=
  TopologicalSpace.coinduced
    (fun x : Surfaces.Disk => Quotient.mk _ x) inferInstance

/-- The two frozen quotient carriers are canonically equivalent, with the
identity map on disk representatives in both directions. -/
def frozenSignedQuotientEquivGenerator :
    FrozenSignedQuotient ≃ FrozenGeneratorQuotient where
  toFun := Quotient.map id (by
    intro x y h
    exact (frozen_eqvGen_boundaryRel_iff_generator x y).mp h)
  invFun := Quotient.map id (by
    intro x y h
    exact (frozen_eqvGen_boundaryRel_iff_generator x y).mpr h)
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    rfl
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    rfl

@[simp] theorem frozenSignedQuotientEquivGenerator_mk (x : Surfaces.Disk) :
    frozenSignedQuotientEquivGenerator
        (Quotient.mk (Relation.EqvGen.setoid
          (boundaryRel 14 frozenPair frozenSign)) x) =
      Quotient.mk (Relation.EqvGen.setoid frozenGeneratorRel) x := rfl

/-- The carrier comparison is a homeomorphism for the two coinduced quotient
topologies. -/
def frozenSignedQuotientHomeomorphGenerator :
    FrozenSignedQuotient ≃ₜ FrozenGeneratorQuotient where
  toEquiv := frozenSignedQuotientEquivGenerator
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng
  continuous_invFun := by
    apply Continuous.quotient_lift
    exact continuous_coinduced_rng

@[simp] theorem frozenSignedQuotientHomeomorphGenerator_mk
    (x : Surfaces.Disk) :
    frozenSignedQuotientHomeomorphGenerator
        (Quotient.mk (Relation.EqvGen.setoid
          (boundaryRel 14 frozenPair frozenSign)) x) =
      Quotient.mk (Relation.EqvGen.setoid frozenGeneratorRel) x := rfl

/-- Integral singular homology transports across the frozen quotient
homeomorphism in every degree. -/
def frozenSignedQuotientHomologyIsoGenerator (k : ℕ) :
    SpaceH FrozenSignedQuotient k ≅ SpaceH FrozenGeneratorQuotient k :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
      (ModuleCat.of ℤ ℤ)).mapIso
    (TopCat.isoOfHomeo frozenSignedQuotientHomeomorphGenerator))

theorem frozenPair_pair (i : Fin 14) : frozenPair (frozenPair i) = i :=
  frozenPairIndex_involutive i

theorem frozenPair_ne (i : Fin 14) : frozenPair i ≠ i := by
  fin_cases i <;> decide

/-- The seven labels of the frozen edge-pairing orbits, ordered `a` through
`g`. -/
def frozenOrbitLabel (i : Fin 14) : Fin 7 :=
  ![0, 2, 3, 6, 5, 4, 1, 2, 3, 6, 4, 5, 0, 1] i

/-- The frozen fourteen edges have exactly seven pairing orbits. -/
def frozenOrbitEquiv : PairingOrbit frozenPair ≃ Fin 7 where
  toFun := Quotient.lift frozenOrbitLabel (by
    intro a b h
    induction h with
    | rel a b h =>
        rcases h with ⟨rfl⟩
        fin_cases a <;> rfl
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂)
  invFun := fun j => Quotient.mk _ (![0, 6, 1, 2, 5, 4, 3] j : Fin 14)
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact Quotient.sound (Relation.EqvGen.rel _ _ rfl)
    · exact Quotient.sound (Relation.EqvGen.rel _ _ rfl)
    · exact Quotient.sound (Relation.EqvGen.rel _ _ rfl)
    · exact Quotient.sound (Relation.EqvGen.rel _ _ rfl)
    · exact Quotient.sound (Relation.EqvGen.rel _ _ rfl)
    · exact Quotient.sound (Relation.EqvGen.rel _ _ rfl)
    · exact Quotient.sound (Relation.EqvGen.rel _ _ rfl)
  right_inv := by
    intro j
    fin_cases j <;> rfl

/-! ## The frozen two-vertex graph boundary -/

/-- The degree-one boundary of the frozen quotient graph in the orbit order
`a,b,c,d,e,f,g`.  Only `d` and `g` join the two vertex classes. -/
def frozenGraphBoundary : (Fin 7 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) where
  toFun v := ![v 6 - v 3, v 3 - v 6]
  map_add' := by
    intro x y
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' := by
    intro n x
    funext i
    fin_cases i <;> simp <;> ring

/-- Six independent cycle coordinates for the frozen two-vertex graph. -/
noncomputable def frozenGraphBoundaryKernelEquiv :
    LinearMap.ker frozenGraphBoundary ≃ₗ[ℤ] (Fin 6 → ℤ) where
  toFun x i := x.1 i.castSucc
  invFun w :=
    ⟨fun i => ![w 0, w 1, w 2, w 3, w 4, w 5, w 3] i,
      by
        rw [LinearMap.mem_ker]
        ext i
        fin_cases i <;> simp [frozenGraphBoundary]⟩
  left_inv := by
    intro x
    apply Subtype.ext
    funext i
    have hx := x.2
    rw [LinearMap.mem_ker] at hx
    have h63 := congrFun hx (0 : Fin 2)
    have h63' : x.1 6 = x.1 3 := by
      change x.1 6 - x.1 3 = 0 at h63
      exact sub_eq_zero.mp h63
    fin_cases i <;> simp [h63']
  right_inv := by
    intro w
    funext i
    fin_cases i <;> rfl
  map_add' := by
    intro x y
    funext i
    rfl
  map_smul' := by
    intro n x
    funext i
    rfl

/-! ## The frozen face boundary in graph-cycle coordinates -/

/-- Signed degree of the fourteen-edge attaching word in orbit order
`a,b,c,d,e,f,g`. -/
def frozenAttachingDegree : Fin 7 → ℤ :=
  ![2, 2, 0, -2, -2, 2, -2]

/-- The attaching degree is a cycle for the two-vertex graph boundary. -/
theorem frozenGraphBoundary_attachingDegree_zero :
    frozenGraphBoundary frozenAttachingDegree = 0 := by
  funext i
  fin_cases i <;> rfl

/-- The frozen attaching cycle as an element of the graph-cycle module. -/
def frozenAttachingCycle : LinearMap.ker frozenGraphBoundary :=
  ⟨frozenAttachingDegree, frozenGraphBoundary_attachingDegree_zero⟩

/-- In the six independent graph-cycle coordinates, the face boundary is
`(2,2,0,-2,-2,2)`. -/
theorem frozenGraphBoundaryKernelEquiv_attachingCycle :
    frozenGraphBoundaryKernelEquiv frozenAttachingCycle =
      ![2, 2, 0, -2, -2, 2] := by
  funext i
  fin_cases i <;> rfl

/-- A unimodular change of graph-cycle coordinates sending the frozen face
cycle to the standard genus-six face cycle. -/
def frozenCycleToN6Coordinates :
    (Fin 6 → ℤ) ≃ₗ[ℤ] (Fin 6 → ℤ) where
  toFun x i := ![x 0, x 1, x 2 + x 0, -x 3, -x 4, x 5] i
  invFun y i := ![y 0, y 1, y 2 - y 0, -y 3, -y 4, y 5] i
  left_inv := by intro x; funext i; fin_cases i <;> simp
  right_inv := by intro y; funext i; fin_cases i <;> simp
  map_add' := by intro x y; funext i; fin_cases i <;> simp <;> ring
  map_smul' := by intro n x; funext i; fin_cases i <;> simp <;> ring

theorem frozenCycleToN6Coordinates_attachingCycle :
    frozenCycleToN6Coordinates
        (frozenGraphBoundaryKernelEquiv frozenAttachingCycle) =
      fun _ => 2 := by
  rw [frozenGraphBoundaryKernelEquiv_attachingCycle]
  funext i
  fin_cases i <;> rfl

/-- The face boundary written in the six independent cycle coordinates. -/
def frozenFaceBoundaryCoordinates : ℤ →ₗ[ℤ] (Fin 6 → ℤ) where
  toFun n := n • frozenGraphBoundaryKernelEquiv frozenAttachingCycle
  map_add' := by intros; simp [add_smul]
  map_smul' := by intros; simp [mul_smul]

theorem n6PolygonHomology :
    Nonempty (H n6PairingData 0 ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (H n6PairingData 1 ≅
        ModuleCat.of ℤ (BoundaryCokernel n6PairingData)) ∧
      Nonempty (H n6PairingData 2 ≅
        ModuleCat.of ℤ (BoundaryKernel n6PairingData)) ∧
      ∀ k : ℕ, 3 ≤ k → IsZero (H n6PairingData k) :=
  polygonQuotient_homology n6PairingData

/-- The six standard edge-orbit coordinates. -/
def n6OrbitCoordinates :
    (PairingOrbit n6PairingData.pair → ℤ) ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  { toFun := fun f j => f ((nonorientableOrbitEquiv 6).symm j)
    invFun := fun v q => v (nonorientableOrbitEquiv 6 q)
    left_inv := by intro f; funext q; simp
    right_inv := by intro v; funext j; simp
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

@[simp] theorem n6OrbitEquiv_orbit (i : Fin 12) :
    nonorientableOrbitEquiv 6 (n6PairingData.orbit i) =
      nonorientableOrbitLabel 6 i := rfl

@[simp] theorem n6_orbit_eq_named (i : Fin 12) (j : Fin 6) :
    n6PairingData.orbit i = (nonorientableOrbitEquiv 6).symm j ↔
      nonorientableOrbitEquiv 6 (n6PairingData.orbit i) = j :=
  (nonorientableOrbitEquiv 6).eq_symm_apply

theorem n6_attachingDegree_named (j : Fin 6) :
    attachingDegree n6PairingData ((nonorientableOrbitEquiv 6).symm j) = -2 := by
  rw [attachingDegree_apply]
  simp_rw [edgeOrbitContribution, n6_orbit_eq_named]
  simp_rw [n6OrbitEquiv_orbit]
  fin_cases j <;>
    simp [n6PairingData, nonorientableStandardPairingData,
      standardPairingDataOfOneVertex, standardPair, standardSign,
      nonorientableOrbitLabel, nonorientableCoord, edgeAttachingDegree] <;>
      decide

theorem n6OrbitCoordinates_attachingDegree :
    n6OrbitCoordinates (attachingDegree n6PairingData) = fun _ => -2 := by
  funext j
  exact n6_attachingDegree_named j

/-- Smith-normal boundary vector for the standard genus-six polygon. -/
def n6BoundaryLinear : ℤ →ₗ[ℤ] (Fin 6 → ℤ) where
  toFun n := fun _ => 2 * n
  map_add' := by intros; funext; simp [mul_add]
  map_smul' := by intros; funext; simp [mul_left_comm]

theorem frozenCycleToN6Coordinates_comp_faceBoundary :
    frozenCycleToN6Coordinates.toLinearMap.comp
        frozenFaceBoundaryCoordinates = n6BoundaryLinear := by
  apply LinearMap.ext
  intro n
  funext i
  change frozenCycleToN6Coordinates
      (n • frozenGraphBoundaryKernelEquiv frozenAttachingCycle) i = 2 * n
  rw [map_smul, frozenCycleToN6Coordinates_attachingCycle]
  simp [mul_comm]

theorem frozenCycleToN6Coordinates_map_faceBoundaryRange :
    Submodule.map frozenCycleToN6Coordinates.toLinearMap
        (LinearMap.range frozenFaceBoundaryCoordinates) =
      LinearMap.range n6BoundaryLinear := by
  rw [← LinearMap.range_comp,
    frozenCycleToN6Coordinates_comp_faceBoundary]

/-- The literal frozen face boundary is injective, so its degree-two
cellular kernel vanishes. -/
theorem frozenFaceBoundaryCoordinates_injective :
    Function.Injective frozenFaceBoundaryCoordinates := by
  intro a b hab
  have h0 := congrFun hab (0 : Fin 6)
  change a * 2 = b * 2 at h0
  omega

theorem frozenFaceBoundaryCoordinates_ker_eq_bot :
    LinearMap.ker frozenFaceBoundaryCoordinates = ⊥ :=
  LinearMap.ker_eq_bot.mpr frozenFaceBoundaryCoordinates_injective

theorem n6OrbitCoordinates_comp_attachingBoundary :
    n6OrbitCoordinates.toLinearMap.comp (attachingBoundary n6PairingData) =
      -n6BoundaryLinear := by
  apply LinearMap.ext
  intro n
  funext j
  change n * attachingDegree n6PairingData
      ((nonorientableOrbitEquiv 6).symm j) = _
  rw [n6_attachingDegree_named]
  simp [n6BoundaryLinear]
  ring

theorem n6BoundaryLinear_injective : Function.Injective n6BoundaryLinear := by
  intro a b h
  have h0 := congrFun h (0 : Fin 6)
  dsimp [n6BoundaryLinear] at h0
  omega

/-- Smith coordinates for the quotient of six integral coordinates by the
constant even vector: five differences and the parity of the first entry. -/
abbrev N6Smith := (Fin 5 → ℤ) × ZMod 2

def n6SmithCoordinate : (Fin 6 → ℤ) →ₗ[ℤ] N6Smith where
  toFun v := (fun j => v j.succ - v 0, v 0)
  map_add' := by
    intro x y
    ext j
    · simp
      ring
    · simp
  map_smul' := by
    intro m x
    ext j <;> simp [mul_sub]

theorem n6SmithCoordinate_surjective :
    Function.Surjective n6SmithCoordinate := by
  rintro ⟨a, c⟩
  let v : Fin 6 → ℤ := Fin.cases c.val (fun j => a j + c.val)
  refine ⟨v, ?_⟩
  ext j
  · simp [n6SmithCoordinate, v]
  · simp [n6SmithCoordinate, v]

theorem n6BoundaryLinear_range_eq_ker :
    LinearMap.range n6BoundaryLinear = LinearMap.ker n6SmithCoordinate := by
  ext v
  constructor
  · rintro ⟨n, rfl⟩
    rw [LinearMap.mem_ker]
    ext j
    · simp [n6SmithCoordinate, n6BoundaryLinear]
    · change ((2 * n : ℤ) : ZMod 2) = 0
      rw [Int.cast_mul]
      change (2 : ZMod 2) * (n : ZMod 2) = 0
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2, zero_mul]
  · intro hv
    rw [LinearMap.mem_ker] at hv
    have hdiff : ∀ j : Fin 5, v j.succ - v 0 = 0 := by
      intro j
      simpa [n6SmithCoordinate] using
        congrArg (fun q : N6Smith => q.1 j) hv
    have hparity : ((v 0 : ℤ) : ZMod 2) = 0 := by
      simpa [n6SmithCoordinate] using congrArg (fun q : N6Smith => q.2) hv
    have heven : (2 : ℤ) ∣ v 0 := by
      simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hparity
    rcases heven with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [n6BoundaryLinear] using hn.symm
    · have hj := hdiff j
      simp only [sub_eq_zero] at hj
      simpa [n6BoundaryLinear, hj] using hn.symm

def n6BoundaryMap : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ (Fin 6 → ℤ) :=
  ModuleCat.ofHom n6BoundaryLinear

/-- The explicit Smith cokernel used by the frozen degree-one answer. -/
noncomputable def n6SmithCokernelIso :
    cokernel n6BoundaryMap ≅ ModuleCat.of ℤ N6Smith :=
  ModuleCat.cokernelIsoRangeQuotient n6BoundaryMap ≪≫
    ((Submodule.quotEquivOfEq _ _ n6BoundaryLinear_range_eq_ker) ≪≫ₗ
      n6SmithCoordinate.quotKerEquivOfSurjective
        n6SmithCoordinate_surjective).toModuleIso

theorem n6AttachingBoundary_injective :
    Function.Injective (attachingBoundary n6PairingData) := by
  intro a b h
  apply n6BoundaryLinear_injective
  have hc := congrArg n6OrbitCoordinates h
  have ha := LinearMap.congr_fun n6OrbitCoordinates_comp_attachingBoundary a
  have hb := LinearMap.congr_fun n6OrbitCoordinates_comp_attachingBoundary b
  simpa [LinearMap.comp_apply] using ha.symm.trans (hc.trans hb)

theorem n6BoundaryKernel_eq_bot : BoundaryKernel n6PairingData = ⊥ :=
  LinearMap.ker_eq_bot.mpr n6AttachingBoundary_injective

theorem n6OrbitCoordinates_map_boundaryRange :
    Submodule.map n6OrbitCoordinates.toLinearMap
        (LinearMap.range (attachingBoundary n6PairingData)) =
      LinearMap.range n6BoundaryLinear := by
  rw [← LinearMap.range_comp,
    n6OrbitCoordinates_comp_attachingBoundary, LinearMap.range_neg]

/-- A coordinate equivalence carrying one boundary range onto another
descends to the corresponding quotient modules. -/
noncomputable def quotientLinearEquivOfMapEq
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N]
    (e : M ≃ₗ[ℤ] N) (p : Submodule ℤ M) (q : Submodule ℤ N)
    (h : Submodule.map e.toLinearMap p = q) :
    (M ⧸ p) ≃ₗ[ℤ] (N ⧸ q) := by
  let f : (M ⧸ p) →ₗ[ℤ] (N ⧸ q) :=
    p.mapQ q e.toLinearMap (by
      intro x hx
      change e x ∈ q
      rw [← h]
      exact ⟨x, hx, rfl⟩)
  let g : (N ⧸ q) →ₗ[ℤ] (M ⧸ p) :=
    q.mapQ p e.symm.toLinearMap (by
      intro y hy
      change e.symm y ∈ p
      have hy' : y ∈ Submodule.map e.toLinearMap p := h.symm ▸ hy
      rcases hy' with ⟨x, hx, hxy⟩
      simpa [← hxy] using hx)
  exact LinearEquiv.ofLinear f g
    (by
      apply LinearMap.ext
      intro x
      refine Quotient.inductionOn x ?_
      intro x
      change (Quotient.mk _ (e (e.symm x))) = Quotient.mk _ x
      rw [e.apply_symm_apply])
    (by
      apply LinearMap.ext
      intro y
      refine Quotient.inductionOn y ?_
      intro y
      change (Quotient.mk _ (e.symm (e y))) = Quotient.mk _ y
      rw [e.symm_apply_apply])

/-- The actual polygon boundary cokernel in explicit Smith coordinates. -/
noncomputable def n6BoundaryCokernelSmithEquiv :
    BoundaryCokernel n6PairingData ≃ₗ[ℤ] N6Smith :=
  quotientLinearEquivOfMapEq n6OrbitCoordinates _ _
      n6OrbitCoordinates_map_boundaryRange ≪≫ₗ
    (Submodule.quotEquivOfEq _ _ n6BoundaryLinear_range_eq_ker ≪≫ₗ
      n6SmithCoordinate.quotKerEquivOfSurjective
        n6SmithCoordinate_surjective)

/-- The cokernel of the literal frozen two-vertex face boundary has the
required five free coordinates and one parity coordinate. -/
noncomputable def frozenFaceCokernelSmithEquiv :
    ((Fin 6 → ℤ) ⧸ LinearMap.range frozenFaceBoundaryCoordinates) ≃ₗ[ℤ]
      N6Smith :=
  quotientLinearEquivOfMapEq frozenCycleToN6Coordinates _ _
      frozenCycleToN6Coordinates_map_faceBoundaryRange ≪≫ₗ
    (Submodule.quotEquivOfEq _ _ n6BoundaryLinear_range_eq_ker ≪≫ₗ
      n6SmithCoordinate.quotKerEquivOfSurjective
        n6SmithCoordinate_surjective)

/-- The final algebraic step of the Mayer--Vietoris calculation: any
surjective degree-one map whose kernel is the literal frozen face boundary
has the required Smith-form target. -/
noncomputable def frozenH1SmithEquivOfSurjectiveKernel
    {D : Type*} [AddCommGroup D] [Module ℤ D]
    (g : (Fin 6 → ℤ) →ₗ[ℤ] D) (hg : Function.Surjective g)
    (hker : LinearMap.ker g =
      LinearMap.range frozenFaceBoundaryCoordinates) :
    D ≃ₗ[ℤ] N6Smith :=
  (g.quotKerEquivOfSurjective hg).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ hker ≪≫ₗ
      frozenFaceCokernelSmithEquiv

/-- Assemble the literal homology calculation once the geometric comparison
maps identify the Mayer--Vietoris groups with the frozen chain complex. -/
theorem frozenPolygonHomology_of_comparisons
    (HF : ℕ → ModuleCat ℤ)
    (h0 : Nonempty (HF 0 ≅ ModuleCat.of ℤ ℤ))
    (g : (Fin 6 → ℤ) →ₗ[ℤ] HF 1)
    (hg : Function.Surjective g)
    (hker : LinearMap.ker g =
      LinearMap.range frozenFaceBoundaryCoordinates)
    (h2 : Nonempty (HF 2 ≅ ModuleCat.of ℤ
      (LinearMap.ker frozenFaceBoundaryCoordinates)))
    (hhigh : ∀ k : ℕ, 3 ≤ k → IsZero (HF k)) :
    Nonempty (HF 0 ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (HF 1 ≅ ModuleCat.of ℤ N6Smith) ∧
      ∀ k : ℕ, 2 ≤ k → IsZero (HF k) := by
  refine ⟨h0, ⟨(frozenH1SmithEquivOfSurjectiveKernel g hg hker).toModuleIso⟩, ?_⟩
  intro k hk
  by_cases hk2 : k = 2
  · subst k
    rcases h2 with ⟨e2⟩
    have hz : IsZero (ModuleCat.of ℤ
        (LinearMap.ker frozenFaceBoundaryCoordinates)) := by
      rw [frozenFaceBoundaryCoordinates_ker_eq_bot]
      rw [IsZero.iff_id_eq_zero]
      ext x
    exact hz.of_iso e2
  · exact hhigh k (by omega)

/-- Once Mayer--Vietoris computes the explicit generator quotient, the same
homology result holds for the generic signed quotient. -/
theorem frozenSignedHomology_of_generator_comparisons
    (h0 : Nonempty (SpaceH FrozenGeneratorQuotient 0 ≅ ModuleCat.of ℤ ℤ))
    (g : (Fin 6 → ℤ) →ₗ[ℤ] SpaceH FrozenGeneratorQuotient 1)
    (hg : Function.Surjective g)
    (hker : LinearMap.ker g =
      LinearMap.range frozenFaceBoundaryCoordinates)
    (h2 : Nonempty (SpaceH FrozenGeneratorQuotient 2 ≅ ModuleCat.of ℤ
      (LinearMap.ker frozenFaceBoundaryCoordinates)))
    (hhigh : ∀ k : ℕ, 3 ≤ k → IsZero (SpaceH FrozenGeneratorQuotient k)) :
    Nonempty (SpaceH FrozenSignedQuotient 0 ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (SpaceH FrozenSignedQuotient 1 ≅ ModuleCat.of ℤ N6Smith) ∧
      ∀ k : ℕ, 2 ≤ k → IsZero (SpaceH FrozenSignedQuotient k) := by
  rcases frozenPolygonHomology_of_comparisons
      (fun k => SpaceH FrozenGeneratorQuotient k)
      h0 g hg hker h2 hhigh with ⟨h0', h1', hhigh'⟩
  refine ⟨?_, ?_, ?_⟩
  · rcases h0' with ⟨e⟩
    exact ⟨frozenSignedQuotientHomologyIsoGenerator 0 ≪≫ e⟩
  · rcases h1' with ⟨e⟩
    exact ⟨frozenSignedQuotientHomologyIsoGenerator 1 ≪≫ e⟩
  · intro k hk
    exact (hhigh' k hk).of_iso (frozenSignedQuotientHomologyIsoGenerator k)

/-- Integral homology of the standard genus-six nonorientable polygon in the
explicit groups required by the frozen problem. -/
theorem n6PolygonHomologyExplicit :
    Nonempty (H n6PairingData 0 ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (H n6PairingData 1 ≅ ModuleCat.of ℤ N6Smith) ∧
      ∀ k : ℕ, 2 ≤ k → IsZero (H n6PairingData k) := by
  rcases n6PolygonHomology with ⟨h0, h1, h2, hhigh⟩
  refine ⟨h0, ?_, ?_⟩
  · rcases h1 with ⟨e1⟩
    exact ⟨e1 ≪≫ n6BoundaryCokernelSmithEquiv.toModuleIso⟩
  · intro k hk
    by_cases hk2 : k = 2
    · subst k
      rcases h2 with ⟨e2⟩
      have hz : IsZero (ModuleCat.of ℤ (BoundaryKernel n6PairingData)) := by
        rw [n6BoundaryKernel_eq_bot]
        rw [IsZero.iff_id_eq_zero]
        ext x
      exact hz.of_iso e2
    · exact hhigh k (by omega)

#print axioms n6PolygonHomology
#print axioms n6AttachingBoundary_injective
#print axioms n6BoundaryKernel_eq_bot
#print axioms n6SmithCokernelIso
#print axioms n6BoundaryCokernelSmithEquiv
#print axioms n6PolygonHomologyExplicit
#print axioms frozenPair_pair
#print axioms frozenPair_ne
#print axioms frozenOrbitEquiv
#print axioms frozenGraphBoundaryKernelEquiv
#print axioms frozenGraphBoundary_attachingDegree_zero
#print axioms frozenGraphBoundaryKernelEquiv_attachingCycle
#print axioms frozenFaceCokernelSmithEquiv
#print axioms frozenH1SmithEquivOfSurjectiveKernel
#print axioms frozenFaceBoundaryCoordinates_injective
#print axioms frozenFaceBoundaryCoordinates_ker_eq_bot
#print axioms frozenPolygonHomology_of_comparisons
#print axioms frozen_pairedParameter
#print axioms frozen_boundaryRel_iff
#print axioms frozenGeneratorRel_radius_eq
#print axioms frozenGeneratorRadialPackage
#print axioms frozenGeneratorRel_boundary
#print axioms frozenGeneratorInnerOverlapHomology
#print axioms frozenGeneratorOuterHomotopyEquivBoundary
#print axioms frozenGeneratorOuterHomologyIsoBoundary
#print axioms frozenGeneratorCircleBoundaryHomeomorph
#print axioms frozenGeneratorCircleBoundaryHomologyIso
#print axioms frozenGeneratorCircleQuotient_identifies_generators
#print axioms frozenGeneratorCircleRel_iff_graphRel
#print axioms frozenGeneratorCircleHomeomorphBoundaryGraph
#print axioms frozenGeneratorCircleHomologyIsoBoundaryGraph
#print axioms frozenGeneratorBoundaryHomologyIsoGraph
#print axioms frozen_boundaryRel_iff_generator
#print axioms frozen_eqvGen_boundaryRel_iff_generator
#print axioms frozenSignedQuotientEquivGenerator
#print axioms frozenSignedQuotientEquivGenerator_mk
#print axioms frozenSignedQuotientHomeomorphGenerator
#print axioms frozenSignedQuotientHomeomorphGenerator_mk
#print axioms frozenSignedQuotientHomologyIsoGenerator
#print axioms frozenSignedHomology_of_generator_comparisons

end ConstructionTargets.t94J09Closure
