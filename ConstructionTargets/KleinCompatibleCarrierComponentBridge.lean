import ConstructionTargets.KleinDiskClosedSquareRelationCompatibleCarrier
import ConstructionTargets.KleinSquareBoundaryRelation
import Mathlib.Topology.Connected.TotallyDisconnected

noncomputable section

namespace ConstructionTargets.KleinCompatibleCarrierComponentBridge

open Relation Set
open ConstructionTargets.Surfaces
open ConstructionTargets.KleinDiskClosedSquareRelationCompatibleCarrier
open KleinPlaneActionSquareOrbitClassification
open KleinSquareBoundaryRelation

abbrev ClosedSquare := {p : ℝ × ℝ // InSquare p}

def ClosedSquareRel (p q : ClosedSquare) : Prop := SquareRel p.1 q.1

def diskClass (x : Disk) : Set Disk :=
  {y | EqvGen (SurfaceRel false 2) x y}

def squareClass (p : ClosedSquare) : Set ClosedSquare :=
  {q | EqvGen ClosedSquareRel p q}

/-- A homeomorphism transports connected components.  This is the general
topological mechanism used after restricting a compatible carrier to the
intrinsically characterized punctured boundaries. -/
def connectedComponentsEquivOfHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) : ConnectedComponents X ≃ ConnectedComponents Y where
  toFun := e.continuous.connectedComponentsMap
  invFun := e.symm.continuous.connectedComponentsMap
  left_inv := by
    rintro ⟨x⟩
    change ((e.symm (e x) : X) : ConnectedComponents X) =
      (x : ConnectedComponents X)
    simp
  right_inv := by
    rintro ⟨y⟩
    change ((e (e.symm y) : Y) : ConnectedComponents Y) =
      (y : ConnectedComponents Y)
    simp

@[simp] theorem connectedComponentsEquivOfHomeomorph_apply
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    connectedComponentsEquivOfHomeomorph e (x : ConnectedComponents X) =
      (e x : ConnectedComponents Y) := rfl

/-- Relation compatibility identifies each complete generated-relation class,
not merely generator pairs.  This is the relation-theoretic part of the
boundary-stratification bridge. -/
theorem image_diskClass_eq_squareClass
    (h : Disk ≃ₜ ClosedSquare)
    (hrel : ∀ x y : Disk,
      EqvGen (SurfaceRel false 2) x y ↔ EqvGen ClosedSquareRel (h x) (h y))
    (x : Disk) :
    h '' diskClass x = squareClass (h x) := by
  ext q
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hrel x y).mp hy
  · intro hq
    refine ⟨h.symm q, ?_, h.apply_symm_apply q⟩
    apply (hrel x (h.symm q)).mpr
    simpa using hq

/-- In particular a compatible carrier preserves exactly the locus whose
generated-relation class contains a second point. -/
theorem exists_distinct_related_iff
    (h : Disk ≃ₜ ClosedSquare)
    (hrel : ∀ x y : Disk,
      EqvGen (SurfaceRel false 2) x y ↔ EqvGen ClosedSquareRel (h x) (h y))
    (x : Disk) :
    (∃ y : Disk, y ≠ x ∧ EqvGen (SurfaceRel false 2) x y) ↔
      ∃ q : ClosedSquare, q ≠ h x ∧ EqvGen ClosedSquareRel (h x) q := by
  constructor
  · rintro ⟨y, hyx, hxy⟩
    refine ⟨h y, ?_, (hrel x y).mp hxy⟩
    exact fun heq => hyx (h.injective heq)
  · rintro ⟨q, hqx, hxq⟩
    refine ⟨h.symm q, ?_, ?_⟩
    · intro heq
      apply hqx
      simpa using congrArg h heq
    · apply (hrel x (h.symm q)).mpr
      simpa using hxq

#print axioms image_diskClass_eq_squareClass
#print axioms exists_distinct_related_iff
#print axioms connectedComponentsEquivOfHomeomorph

end ConstructionTargets.KleinCompatibleCarrierComponentBridge
