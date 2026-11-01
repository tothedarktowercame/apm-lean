import Mathlib
import ConstructionTargets.AttachTwoCell

/-!
# APM t00J05: standard-curve version, OUT OF COMPETITION

Does not count towards t00J05 (Joe, 2026-11-01: the general version is needed to
count it).  The registered statement in `problems/t00J05/lean/Main.lean` quantifies
over every essential embedded curve; this file fixes one curve.

The printed problem allows any essential embedded circle in the torus.  The
classification of essential curves on the torus (Schoenflies followed by
cutting the torus along the curve) carries its image to a standard factor;
the Alexander trick absorbs a reparametrisation of the attaching circle.  We
therefore fix the standard first-factor representative.  Primitivity of the
homotopy class alone would not justify this reduction of an embedding.

The attached space is the honest quotient `AttachTwoCell.Cell standardCurve`.
The actual universal-cover model is a cylinder `S¹ × ℝ` capped by a disk along
every circle `S¹ × {n}`.  It is defined below as an honest quotient, as is its
projection to the attached space.  The book's “line with a sphere at every
integer” is not homeomorphic to this cover (and cannot cover a space which is
locally two-dimensional everywhere); it describes only its homotopy type.  We
retain that concrete necklace and state the homotopy equivalence explicitly.
Part (b) asks for continuous maps in both directions which are not homotopic
to any constant map.
-/

open scoped ContinuousMap

noncomputable section

namespace APMT00J05

open ConstructionTargets.AttachTwoCell

abbrev Torus := Circle × Circle

/-- The standard essential simple closed curve in the torus. -/
def standardCurve : C(Circle, Torus) :=
  ⟨fun z ↦ (z, 1), continuous_id.prodMk continuous_const⟩

/-- The complex obtained by attaching a disk to the torus along the standard
essential circle. -/
abbrev X := Cell standardCurve

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

/-- The period-one exponential used in the second torus coordinate. -/
def periodOneExp (t : ℝ) : Circle := Circle.exp (t * (2 * Real.pi))

lemma continuous_periodOneExp : Continuous periodOneExp := by
  exact Circle.exp.continuous.comp
    (continuous_id.mul (continuous_const.mul continuous_const))

@[simp] lemma periodOneExp_int (n : ℤ) : periodOneExp (n : ℝ) = 1 := by
  simpa [periodOneExp] using Circle.exp_int_mul_two_pi n

/-- The projection on representatives: the cylinder wraps in the second torus
coordinate and every cap maps identically to the single attached disk. -/
def cappedCylinderRaw : ((Circle × ℝ) ⊕ (ℤ × Disk)) → X
  | .inl (z, t) => cellMk standardCurve (.inl (z, periodOneExp t))
  | .inr (_, d) => cellMk standardCurve (.inr d)

lemma cappedCylinderRaw_respects {a b}
    (h : Relation.EqvGen CappedCylinderRel a b) :
    cappedCylinderRaw a = cappedCylinderRaw b := by
  induction h with
  | rel a b h =>
      cases h with
      | cap n z =>
          simp only [cappedCylinderRaw, periodOneExp_int]
          apply Quotient.sound
          exact Relation.EqvGen.rel _ _ (CellRel.boundary z)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma continuous_cappedCylinderRaw : Continuous cappedCylinderRaw := by
  apply continuous_sum_dom.mpr
  constructor
  · exact (continuous_cellMk standardCurve).comp
      (continuous_inl.comp
        (continuous_fst.prodMk (continuous_periodOneExp.comp continuous_snd)))
  · exact (continuous_cellMk standardCurve).comp
      (continuous_inr.comp continuous_snd)

/-- The explicit projection from the capped cylinder to the attached torus. -/
def cappedCylinderProjection : C(CappedCylinder, X) where
  toFun := Quotient.lift cappedCylinderRaw
    (fun _ _ h ↦ cappedCylinderRaw_respects h)
  continuous_toFun := by
    exact Continuous.quotient_lift continuous_cappedCylinderRaw
      (fun _ _ h ↦ cappedCylinderRaw_respects h)

end APMT00J05

open APMT00J05

/-- The two assertions requested in the problem, for the standard representative
of the essential curve. -/
theorem apm_t00j05 :
    (IsCoveringMap cappedCylinderProjection ∧
      SimplyConnectedSpace CappedCylinder ∧
      Nonempty (ContinuousMap.HomotopyEquiv CappedCylinder Necklace)) ∧
    (∃ i : C(Sphere2, X),
      (¬ ∃ x : X, ContinuousMap.Homotopic i (ContinuousMap.const Sphere2 x)) ∧
      ∃ q : C(X, Sphere2),
        ¬ ∃ s : Sphere2,
          ContinuousMap.Homotopic q (ContinuousMap.const X s)) := by
  sorry
