import Mathlib
import ConstructionTargets.SingularHomologyHomotopy

/-!
# Boundaries of filling disks in singular homology

This module packages the elementary input used before an intersection-theoretic
argument: a circle which extends continuously across the closed complex unit
disk is nullhomotopic, and hence induces the zero map on positive-degree
singular homology.
-/

open CategoryTheory Set

noncomputable section

namespace ConstructionTargets.DiskBoundaryHomology

abbrev Disk := Metric.closedBall (0 : ℂ) 1

/-- The standard inclusion of the complex unit circle into the closed unit
disk. -/
def circleToDisk (z : Circle) : Disk :=
  ⟨(z : ℂ), by
    rw [mem_closedBall_zero_iff]
    exact (Circle.norm_coe z).le⟩

lemma continuous_circleToDisk : Continuous circleToDisk :=
  continuous_subtype_val.subtype_mk _

/-- The boundary restriction of a continuous map out of the closed unit disk
is nullhomotopic in its codomain. -/
theorem nullhomotopic_boundary {X : Type} [TopologicalSpace X]
    (d : Disk → X) (hd : Continuous d) :
    ContinuousMap.Nullhomotopic
      ⟨fun z : Circle => d (circleToDisk z),
        hd.comp continuous_circleToDisk⟩ := by
  let d' : C(Disk, X) := ⟨d, hd⟩
  let boundary : C(Circle, Disk) :=
    ⟨circleToDisk, continuous_circleToDisk⟩
  letI : ContractibleSpace Disk :=
    Metric.contractibleSpace_closedBall (x := (0 : ℂ)) (r := 1) zero_le_one
  have hdnull : ContinuousMap.Nullhomotopic d' := by
    simpa [d'] using (id_nullhomotopic Disk).comp_right d'
  simpa [d', boundary] using hdnull.comp_left boundary

/-- A boundary which extends across the disk induces zero on every positive
degree of singular homology, with arbitrary coefficient category and object. -/
theorem singularHomology_map_boundary_eq_zero
    (C : Type*) [Category C] [Preadditive C] [Limits.HasCoproducts C]
    [CategoryWithHomology C]
    (A : C) {X : Type} [TopologicalSpace X]
    (d : Disk → X) (hd : Continuous d) (n : ℕ) (hn : n ≠ 0) :
    ((AlgebraicTopology.singularHomologyFunctor C n).obj A).map
      (TopCat.ofHom
        (⟨fun z : Circle => d (circleToDisk z),
          hd.comp continuous_circleToDisk⟩ : C(Circle, X))) = 0 := by
  let f : C(Circle, X) :=
    ⟨fun z => d (circleToDisk z), hd.comp continuous_circleToDisk⟩
  exact ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_zero_of_nullhomotopic
    C A n hn f (nullhomotopic_boundary d hd)

/-- A set has disk-bounded components when every point lies in a connected
component displayed as the boundary range of an embedded continuous disk. -/
def ComponentsBoundByDisks {X : Type} [TopologicalSpace X] (s : Set X) : Prop :=
  ∀ x ∈ s, ∃ d : Disk → X,
    Continuous d ∧ Topology.IsEmbedding d ∧
      range (fun z : Circle => d (circleToDisk z)) = connectedComponentIn s x

/-- A disk-bounded component is the range of a continuous circle whose map on
positive-degree singular homology vanishes, for arbitrary coefficients. -/
theorem exists_boundary_eq_component_and_singularHomology_map_eq_zero
    (C : Type*) [Category C] [Preadditive C] [Limits.HasCoproducts C]
    [CategoryWithHomology C]
    (A : C) {X : Type} [TopologicalSpace X] {s : Set X}
    (hdisks : ComponentsBoundByDisks s) {x : X} (hx : x ∈ s)
    (n : ℕ) (hn : n ≠ 0) :
    ∃ γ : C(Circle, X), range γ = connectedComponentIn s x ∧
      ((AlgebraicTopology.singularHomologyFunctor C n).obj A).map
        (TopCat.ofHom γ) = 0 := by
  rcases hdisks x hx with ⟨d, hd, _hemb, hrange⟩
  let γ : C(Circle, X) :=
    ⟨fun z => d (circleToDisk z), hd.comp continuous_circleToDisk⟩
  refine ⟨γ, hrange, ?_⟩
  exact singularHomology_map_boundary_eq_zero C A d hd n hn

/-- Every point of a disk-bounded set lies on a circle contained in the set
and killed by positive-degree singular homology. -/
theorem exists_homology_trivial_circle_through_point
    (C : Type*) [Category C] [Preadditive C] [Limits.HasCoproducts C]
    [CategoryWithHomology C]
    (A : C) {X : Type} [TopologicalSpace X] {s : Set X}
    (hdisks : ComponentsBoundByDisks s) {x : X} (hx : x ∈ s)
    (n : ℕ) (hn : n ≠ 0) :
    ∃ γ : C(Circle, X), x ∈ range γ ∧ range γ ⊆ s ∧
      ((AlgebraicTopology.singularHomologyFunctor C n).obj A).map
        (TopCat.ofHom γ) = 0 := by
  rcases exists_boundary_eq_component_and_singularHomology_map_eq_zero
    C A hdisks hx n hn with ⟨γ, hrange, hzero⟩
  refine ⟨γ, ?_, ?_, hzero⟩
  · rw [hrange]
    exact mem_connectedComponentIn hx
  · rw [hrange]
    exact connectedComponentIn_subset s x

end ConstructionTargets.DiskBoundaryHomology

#print axioms ConstructionTargets.DiskBoundaryHomology.exists_homology_trivial_circle_through_point
