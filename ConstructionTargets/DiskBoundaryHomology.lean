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

end ConstructionTargets.DiskBoundaryHomology
