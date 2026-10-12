import ConstructionTargets.Surfaces

/-!
# Polygon surface fundamental groups

This file begins the construction certified in
`PolygonSurfacePiOne.blueprint.md`.  It contains B1: polygon-pairing data and
the associated disk quotient.
-/

open Set

noncomputable section

namespace ConstructionTargets.PolygonSurfacePiOne

open Surfaces

/-- The generator indices of a polygon pairing are the orbits of its arc
permutation.  For pairing data the permutation is an involution, so every
orbit consists of exactly one paired pair. -/
def PairingOrbit {n : ℕ} (pair : Equiv.Perm (Fin n)) :=
  Quotient (Relation.EqvGen.setoid (fun i j => j = pair i))

/-- Reverse a unit-interval parameter. -/
def reverseIcc (t : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩

@[simp] theorem reverseIcc_value (t : Set.Icc (0 : ℝ) 1) :
    (reverseIcc t : ℝ) = 1 - t := rfl

@[simp] theorem reverseIcc_reverseIcc (t : Set.Icc (0 : ℝ) 1) :
    reverseIcc (reverseIcc t) = t := by
  ext
  simp [reverseIcc]

/-- The parameter on the paired arc.  Equal signs preserve the parameter;
unequal signs reverse it. -/
def pairedParameter {n : ℕ} (pair : Equiv.Perm (Fin n))
    (sign : Fin n → Bool) (i : Fin n) (t : Set.Icc (0 : ℝ) 1) :
    Set.Icc (0 : ℝ) 1 :=
  if sign i = sign (pair i) then t else reverseIcc t

/-- The generating boundary identifications of a signed polygon pairing. -/
def boundaryRel (n : ℕ) (pair : Equiv.Perm (Fin n))
    (sign : Fin n → Bool) (x y : Disk) : Prop :=
  ∃ i : Fin n, ∃ t : Set.Icc (0 : ℝ) 1,
    x = edgePoint n i t ∧
      y = edgePoint n (pair i) (pairedParameter pair sign i t)

/-- A polygon vertex, represented as the initial endpoint of an arc. -/
def polygonVertex (n : ℕ) (i : Fin n) : Disk :=
  edgePoint n i ⟨0, by simp⟩

/-- Finite signed polygon-pairing data.  The pairing is explicitly a
fixed-point-free involution, and `oneVertex` records exactly the hypothesis
needed later to identify the boundary skeleton with a wedge of circles. -/
structure PairingData where
  edgeCount : ℕ
  pair : Equiv.Perm (Fin edgeCount)
  pair_pair : ∀ i, pair (pair i) = i
  pair_ne : ∀ i, pair i ≠ i
  sign : Fin edgeCount → Bool
  oneVertex : ∀ i j : Fin edgeCount,
    Relation.EqvGen (boundaryRel edgeCount pair sign)
      (polygonVertex edgeCount i) (polygonVertex edgeCount j)

namespace PairingData

/-- The boundary relation belonging to pairing data. -/
def Rel (P : PairingData) : Disk → Disk → Prop :=
  boundaryRel P.edgeCount P.pair P.sign

/-- The polygon surface obtained from the closed disk by the generated
boundary identifications. -/
def Space (P : PairingData) :=
  Quotient (Relation.EqvGen.setoid P.Rel)

noncomputable instance (P : PairingData) : TopologicalSpace P.Space :=
  TopologicalSpace.coinduced
    (fun x : Disk => Quotient.mk (Relation.EqvGen.setoid P.Rel) x)
    inferInstance

/-- The canonical disk quotient map. -/
def quotientMap (P : PairingData) : Disk → P.Space :=
  fun x => Quotient.mk _ x

theorem continuous_quotientMap (P : PairingData) :
    Continuous P.quotientMap :=
  continuous_coinduced_rng

theorem surjective_quotientMap (P : PairingData) :
    Function.Surjective P.quotientMap :=
  Quotient.mk_surjective

/-- The distinguished point represented by the centre of the polygon. -/
def center (P : PairingData) : P.Space :=
  P.quotientMap ⟨0, by simp [Disk, Metric.mem_closedBall]⟩

/-- The orbit of an arc is a canonical generator index. -/
def orbit (P : PairingData) (i : Fin P.edgeCount) : PairingOrbit P.pair :=
  Quotient.mk _ i

@[simp] theorem orbit_pair (P : PairingData) (i : Fin P.edgeCount) :
    P.orbit (P.pair i) = P.orbit i := by
  apply Quotient.sound
  exact Relation.EqvGen.rel (P.pair i) i (P.pair_pair i).symm

end PairingData

end ConstructionTargets.PolygonSurfacePiOne
