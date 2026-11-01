import Mathlib
import ConstructionTargets.AttachTwoCell

/-!
# Blueprint for APM t00J05

The registered statement is unchanged.  The large first leaf is the missing
arbitrary-embedding surface-normalisation theorem; no tameness or smoothness
hypothesis is added.
-/

open scoped ContinuousMap

noncomputable section

namespace APMT00J05

open ConstructionTargets.AttachTwoCell

abbrev Torus := Circle × Circle

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev Sphere2 := Metric.sphere (0 : E3) 1

def sphereBase : Sphere2 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩

inductive NecklaceRel : (ℝ ⊕ (ℤ × Sphere2)) → (ℝ ⊕ (ℤ × Sphere2)) → Prop
  | glue (n : ℤ) : NecklaceRel (.inl (n : ℝ)) (.inr (n, sphereBase))

def Necklace := Quotient (Relation.EqvGen.setoid NecklaceRel)

instance : TopologicalSpace Necklace :=
  TopologicalSpace.coinduced
    (fun z : ℝ ⊕ (ℤ × Sphere2) ↦
      Quotient.mk (Relation.EqvGen.setoid NecklaceRel) z)
    inferInstance

inductive CappedCylinderRel :
    ((Circle × ℝ) ⊕ (ℤ × Disk)) → ((Circle × ℝ) ⊕ (ℤ × Disk)) → Prop
  | cap (n : ℤ) (z : Circle) :
      CappedCylinderRel (.inl (z, (n : ℝ))) (.inr (n, circleToDisk z))

def CappedCylinder := Quotient (Relation.EqvGen.setoid CappedCylinderRel)

instance : TopologicalSpace CappedCylinder :=
  TopologicalSpace.coinduced
    (fun z : (Circle × ℝ) ⊕ (ℤ × Disk) ↦
      Quotient.mk (Relation.EqvGen.setoid CappedCylinderRel) z)
    inferInstance

/-- The standard primitive curve used only as an intermediate model. -/
def standardCurve : C(Circle, Torus) :=
  ⟨fun z ↦ (z, 1), continuous_id.prodMk continuous_const⟩

/-- **LIBRARY / missing foundation.** Arbitrary essential embedded circles in
the torus give homeomorphic two-cell attachments.  A proof requires the
Jordan--Schoenflies/collar theorem and compact-surface cutting, including
extension of the boundary reparametrisation across the attached disk. -/
theorem apm_t00J05_cell_normal_form
    (f : C(Circle, Torus)) (hf : Topology.IsEmbedding f)
    (hessential : ¬ ∃ x : Torus,
      ContinuousMap.Homotopic f (ContinuousMap.const Circle x)) :
    Nonempty (Cell f ≃ₜ Cell standardCurve) := by
  sorry

/-- **LIBRARY.** The explicit capped-cylinder model covers the standard
attachment.  Construct the quotient projection and prove evenly covered
neighbourhoods at cylinder points, cap interiors, and the glued seam. -/
theorem apm_t00J05_standard_cover :
    ∃ p : C(CappedCylinder, Cell standardCurve), IsCoveringMap p := by
  sorry

/-- **LIBRARY.** The capped cylinder is simply connected.  Use an exhaustion
by finite strings of capped bands and van Kampen, with the inclusions killing
the cylinder generator. -/
theorem apm_t00J05_cappedCylinder_simplyConnected :
    SimplyConnectedSpace CappedCylinder := by
  sorry

/-- **LIBRARY.** Collapse the contractible connecting arcs in the capped
cylinder to obtain the line with one sphere at each integer. -/
theorem apm_t00J05_cappedCylinder_necklace :
    Nonempty (ContinuousMap.HomotopyEquiv CappedCylinder Necklace) := by
  sorry

/-- **LIBRARY.** For the standard attachment, construct the sphere summand
inclusion and collapse map and detect both by their identity composite (or by
integral `H₂`). -/
theorem apm_t00J05_standard_nonnull_maps :
    ∃ i : C(Sphere2, Cell standardCurve),
      (¬ ∃ x : Cell standardCurve,
        ContinuousMap.Homotopic i (ContinuousMap.const Sphere2 x)) ∧
      ∃ q : C(Cell standardCurve, Sphere2),
        ¬ ∃ s : Sphere2,
          ContinuousMap.Homotopic q (ContinuousMap.const (Cell standardCurve) s) := by
  sorry

/-- Transport a covering projection across a target homeomorphism.  Use
`IsCoveringMap.comp` and the covering-map instance of a homeomorphism. -/
theorem apm_t00J05_transport_cover
    {f : C(Circle, Torus)} (H : Cell f ≃ₜ Cell standardCurve)
    (hcover : ∃ p : C(CappedCylinder, Cell standardCurve), IsCoveringMap p) :
    ∃ p : C(CappedCylinder, Cell f), IsCoveringMap p := by
  sorry

/-- Transport the two non-null maps across a homeomorphism.  Null-homotopies
would compose with `H` or `H.symm` to contradict the supplied ones. -/
theorem apm_t00J05_transport_nonnull_maps
    {f : C(Circle, Torus)} (H : Cell f ≃ₜ Cell standardCurve)
    (hmodel : ∃ i : C(Sphere2, Cell standardCurve),
      (¬ ∃ x : Cell standardCurve,
        ContinuousMap.Homotopic i (ContinuousMap.const Sphere2 x)) ∧
      ∃ q : C(Cell standardCurve, Sphere2),
        ¬ ∃ s : Sphere2,
          ContinuousMap.Homotopic q (ContinuousMap.const (Cell standardCurve) s)) :
    ∃ i : C(Sphere2, Cell f),
      (¬ ∃ x : Cell f,
        ContinuousMap.Homotopic i (ContinuousMap.const Sphere2 x)) ∧
      ∃ q : C(Cell f, Sphere2),
        ¬ ∃ s : Sphere2,
          ContinuousMap.Homotopic q (ContinuousMap.const (Cell f) s) := by
  sorry

end APMT00J05

open APMT00J05
open ConstructionTargets.AttachTwoCell

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
  intro f hf hessential
  obtain ⟨H⟩ := apm_t00J05_cell_normal_form f hf hessential
  exact ⟨⟨apm_t00J05_transport_cover H apm_t00J05_standard_cover,
    apm_t00J05_cappedCylinder_simplyConnected,
    apm_t00J05_cappedCylinder_necklace⟩,
    apm_t00J05_transport_nonnull_maps H apm_t00J05_standard_nonnull_maps⟩
