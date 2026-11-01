import Mathlib
import ConstructionTargets.AttachTwoCell

/-!
# APM t00J05

For every embedding `f` of the circle onto an essential simple closed curve in
the torus, the attached space is the honest quotient `AttachTwoCell.Cell f`.
"Essential" is stated as: `f` is not homotopic to a constant map.

The universal-cover model is a cylinder `S¹ × ℝ` capped by a disk along every
circle `S¹ × {n}`, defined below as an honest quotient.  It does not depend on
`f`; the covering projection does, so the statement asserts that one exists.  The
book's "line with a sphere at every integer" is not homeomorphic to this cover
(and cannot cover a space which is locally two-dimensional everywhere); it
describes only its homotopy type.  We retain that concrete necklace and state the
homotopy equivalence explicitly.  Part (b) asks for continuous maps in both
directions which are not homotopic to any constant map.

No reduction to a standard curve is made in this statement.  A proof needs the
classification of essential curves (Schoenflies, then cutting the torus along the
curve), which is absent from Mathlib and from this repository.  The version for
one fixed curve is in `holes/labs/out-of-competition/t00J05/StandardCurve.lean`
and does not count.
-/

open scoped ContinuousMap

noncomputable section

namespace APMT00J05

open ConstructionTargets.AttachTwoCell

abbrev Torus := Circle × Circle

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev Sphere2 := Metric.sphere (0 : E3) 1

/-- A concrete chosen point of the unit 2-sphere. -/
def sphereBase : Sphere2 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

/-- Glue the integer point of the line to the basepoint of the corresponding
sphere. -/
inductive NecklaceRel : (ℝ ⊕ (ℤ × Sphere2)) → (ℝ ⊕ (ℤ × Sphere2)) → Prop
  | glue (n : ℤ) : NecklaceRel (.inl (n : ℝ)) (.inr (n, sphereBase))

/-- The line with one 2-sphere attached at every integer. -/
def Necklace := Quotient (Relation.EqvGen.setoid NecklaceRel)

instance : TopologicalSpace Necklace :=
  TopologicalSpace.coinduced
    (fun z : ℝ ⊕ (ℤ × Sphere2) ↦
      Quotient.mk (Relation.EqvGen.setoid NecklaceRel) z)
    inferInstance

/-- Glue the boundary of the disk indexed by `n` to the horizontal circle at
height `n` in the cylinder. -/
inductive CappedCylinderRel :
    ((Circle × ℝ) ⊕ (ℤ × Disk)) → ((Circle × ℝ) ⊕ (ℤ × Disk)) → Prop
  | cap (n : ℤ) (z : Circle) :
      CappedCylinderRel (.inl (z, (n : ℝ))) (.inr (n, circleToDisk z))

/-- The cylinder with one disk capping every integer-height circle. -/
def CappedCylinder :=
  Quotient (Relation.EqvGen.setoid CappedCylinderRel)

instance : TopologicalSpace CappedCylinder :=
  TopologicalSpace.coinduced
    (fun z : (Circle × ℝ) ⊕ (ℤ × Disk) ↦
      Quotient.mk (Relation.EqvGen.setoid CappedCylinderRel) z)
    inferInstance

end APMT00J05

open APMT00J05
open ConstructionTargets.AttachTwoCell

/-- The two assertions requested in the problem, for every essential embedded
curve in the torus. -/
theorem apm_t00j05 :
    ∀ f : C(Circle, Torus), Topology.IsEmbedding f →
      (¬ ∃ x : Torus, ContinuousMap.Homotopic f (ContinuousMap.const Circle x)) →
      ((∃ p : C(CappedCylinder, Cell f), IsCoveringMap p) ∧
        SimplyConnectedSpace CappedCylinder ∧
        Nonempty (ContinuousMap.HomotopyEquiv CappedCylinder Necklace)) ∧
      (∃ i : C(Sphere2, Cell f),
        (¬ ∃ x : Cell f, ContinuousMap.Homotopic i (ContinuousMap.const Sphere2 x)) ∧
        ∃ q : C(Cell f, Sphere2),
          ¬ ∃ s : Sphere2,
            ContinuousMap.Homotopic q (ContinuousMap.const (Cell f) s)) := by
  sorry
