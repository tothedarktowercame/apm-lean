import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.SuppliedCoverAlgebra
import ConstructionTargets.FiniteIndexFreeGroupSchreierRank
import ConstructionTargets.PointWedgeVanKampen
import ConstructionTargets.ProductionOpenCoverMayerVietoris
import ConstructionTargets.SphereHomology
import ConstructionTargets.CircleSingularHomology

/-! # APM t97A03: connected double covers of a sphere with a circle attached

The statement and concrete quotient models are copied from the registered
problem.  The two remaining obligations are genuine library boundaries: an
explicit monodromy classification and the invariant calculation for the two
literal quotient models.
-/

open CategoryTheory Set

noncomputable section

abbrev apm_t97A03_R3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t97A03_S2 := Metric.sphere (0 : apm_t97A03_R3) 1

def apm_t97A03_north : apm_t97A03_S2 :=
  ⟨EuclideanSpace.single (2 : Fin 3) 1, by simp⟩

def apm_t97A03_south : apm_t97A03_S2 :=
  ⟨EuclideanSpace.single (2 : Fin 3) (-1), by simp⟩

inductive apm_t97A03_BaseRel (A B : Circle) :
    Sum Circle apm_t97A03_S2 → Sum Circle apm_t97A03_S2 → Prop
  | north : apm_t97A03_BaseRel A B (.inl A) (.inr apm_t97A03_north)
  | south : apm_t97A03_BaseRel A B (.inl B) (.inr apm_t97A03_south)

def apm_t97A03_BaseSpace (A B : Circle) :=
  Quotient (Relation.EqvGen.setoid (apm_t97A03_BaseRel A B))

noncomputable instance (A B : Circle) :
    TopologicalSpace (apm_t97A03_BaseSpace A B) :=
  TopologicalSpace.coinduced (fun x : Sum Circle apm_t97A03_S2 ↦
    Quotient.mk _ x) inferInstance

lemma apm_t97A03_base_north_eq (A B : Circle) :
    (Quotient.mk _ (.inl A) : apm_t97A03_BaseSpace A B) =
      Quotient.mk _ (.inr apm_t97A03_north) := by
  exact Quotient.sound
    (Relation.EqvGen.rel _ _
      (apm_t97A03_BaseRel.north (A := A) (B := B)))

lemma apm_t97A03_base_south_eq (A B : Circle) :
    (Quotient.mk _ (.inl B) : apm_t97A03_BaseSpace A B) =
      Quotient.mk _ (.inr apm_t97A03_south) := by
  exact Quotient.sound
    (Relation.EqvGen.rel _ _
      (apm_t97A03_BaseRel.south (A := A) (B := B)))

def apm_t97A03_circleOne : Circle := ⟨1, by simp⟩
def apm_t97A03_circleNegOne : Circle := ⟨-1, by
  exact mem_sphere_zero_iff_norm.mpr (by norm_num)⟩
def apm_t97A03_circleI : Circle := ⟨Complex.I, by
  exact mem_sphere_zero_iff_norm.mpr Complex.norm_I⟩
def apm_t97A03_circleNegI : Circle := ⟨-Complex.I, by
  exact mem_sphere_zero_iff_norm.mpr (by rw [norm_neg, Complex.norm_I])⟩

abbrev apm_t97A03_TwoSpheres := Fin 2 × apm_t97A03_S2

inductive apm_t97A03_OneCircleRel :
    Sum apm_t97A03_TwoSpheres Circle →
      Sum apm_t97A03_TwoSpheres Circle → Prop
  | n0 : apm_t97A03_OneCircleRel
      (.inr apm_t97A03_circleOne) (.inl (0, apm_t97A03_north))
  | s0 : apm_t97A03_OneCircleRel
      (.inr apm_t97A03_circleI) (.inl (0, apm_t97A03_south))
  | n1 : apm_t97A03_OneCircleRel
      (.inr apm_t97A03_circleNegOne) (.inl (1, apm_t97A03_north))
  | s1 : apm_t97A03_OneCircleRel
      (.inr apm_t97A03_circleNegI) (.inl (1, apm_t97A03_south))

def apm_t97A03_OneCircleCover :=
  Quotient (Relation.EqvGen.setoid apm_t97A03_OneCircleRel)

noncomputable instance : TopologicalSpace apm_t97A03_OneCircleCover :=
  TopologicalSpace.coinduced
    (fun x : Sum apm_t97A03_TwoSpheres Circle ↦ Quotient.mk _ x) inferInstance

inductive apm_t97A03_TwoCircleRel :
    Sum apm_t97A03_TwoSpheres (Fin 2 × Circle) →
      Sum apm_t97A03_TwoSpheres (Fin 2 × Circle) → Prop
  | c0n : apm_t97A03_TwoCircleRel
      (.inr (0, apm_t97A03_circleOne)) (.inl (0, apm_t97A03_north))
  | c0s : apm_t97A03_TwoCircleRel
      (.inr (0, apm_t97A03_circleNegOne)) (.inl (1, apm_t97A03_south))
  | c1n : apm_t97A03_TwoCircleRel
      (.inr (1, apm_t97A03_circleOne)) (.inl (1, apm_t97A03_north))
  | c1s : apm_t97A03_TwoCircleRel
      (.inr (1, apm_t97A03_circleNegOne)) (.inl (0, apm_t97A03_south))

def apm_t97A03_TwoCircleCover :=
  Quotient (Relation.EqvGen.setoid apm_t97A03_TwoCircleRel)

noncomputable instance : TopologicalSpace apm_t97A03_TwoCircleCover :=
  TopologicalSpace.coinduced
    (fun x : Sum apm_t97A03_TwoSpheres (Fin 2 × Circle) ↦ Quotient.mk _ x)
    inferInstance

abbrev apm_t97A03_Homology (X : Type) [TopologicalSpace X] (n : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

lemma apm_t97A03_surjective_of_fiber_card_two
    {A B : Circle} {Y : Type} (p : Y → apm_t97A03_BaseSpace A B)
    (hdegree : ∀ x : apm_t97A03_BaseSpace A B,
      Nat.card (p ⁻¹' ({x} : Set _)) = 2) :
    Function.Surjective p := by
  intro x
  by_contra hx
  push_neg at hx
  have hempty : p ⁻¹' ({x} : Set _) = ∅ := by
    ext y
    simp [hx y]
  have h := hdegree x
  rw [hempty] at h
  simp at h

lemma apm_t97A03_fiber_equiv_fin_two
    {A B : Circle} {Y : Type} (p : Y → apm_t97A03_BaseSpace A B)
    (hdegree : ∀ x : apm_t97A03_BaseSpace A B,
      Nat.card (p ⁻¹' ({x} : Set _)) = 2)
    (x : apm_t97A03_BaseSpace A B) :
    Nonempty ((p ⁻¹' ({x} : Set _)) ≃ Fin 2) := by
  have hcard0 : Nat.card (p ⁻¹' ({x} : Set _)) ≠ 0 := by
    rw [hdegree x]
    norm_num
  letI : Finite (p ⁻¹' ({x} : Set _)) := Nat.finite_of_card_ne_zero hcard0
  letI := Fintype.ofFinite (p ⁻¹' ({x} : Set _))
  exact ⟨Fintype.equivOfCardEq (by simpa [Nat.card_eq_fintype_card] using hdegree x)⟩

/-- **LIBRARY: explicit two-sheet monodromy classification.** -/
theorem apm_t97A03_classify_connected_double_cover
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y] [ConnectedSpace Y]
    (p : Y → apm_t97A03_BaseSpace A B)
    (hp : IsCoveringMap p)
    (hdegree : ∀ x : apm_t97A03_BaseSpace A B,
      Nat.card (p ⁻¹' ({x} : Set _)) = 2) :
    Nonempty (Y ≃ₜ apm_t97A03_OneCircleCover) ∨
      Nonempty (Y ≃ₜ apm_t97A03_TwoCircleCover) := by
  sorry

/-- **LIBRARY: Mayer--Vietoris and van Kampen for the two literal models.**
The model disjunction is an input so this theorem is independent of the
classification theorem and can be implemented in parallel. -/
theorem apm_t97A03_invariants_of_model
    (Y : Type) [TopologicalSpace Y] (y : Y)
    (hmodel : Nonempty (Y ≃ₜ apm_t97A03_OneCircleCover) ∨
      Nonempty (Y ≃ₜ apm_t97A03_TwoCircleCover)) :
    Nonempty (apm_t97A03_Homology Y 0 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t97A03_Homology Y 1 ≅ ModuleCat.of ℤ (Fin 3 → ℤ)) ∧
    Nonempty (apm_t97A03_Homology Y 2 ≅ ModuleCat.of ℤ (Fin 2 → ℤ)) ∧
    (∀ n, 3 ≤ n → Limits.IsZero (apm_t97A03_Homology Y n)) ∧
    Nonempty (FundamentalGroup Y y ≃* FreeGroup (Fin 3)) := by
  sorry

theorem apm_t97a03
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type) [TopologicalSpace Y] [ConnectedSpace Y]
    (y : Y) (p : Y → apm_t97A03_BaseSpace A B)
    (hp : IsCoveringMap p)
    (hdegree : ∀ x : apm_t97A03_BaseSpace A B,
      Nat.card (p ⁻¹' ({x} : Set _)) = 2) :
    (Nonempty (Y ≃ₜ apm_t97A03_OneCircleCover) ∨
      Nonempty (Y ≃ₜ apm_t97A03_TwoCircleCover)) ∧
    Nonempty (apm_t97A03_Homology Y 0 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t97A03_Homology Y 1 ≅ ModuleCat.of ℤ (Fin 3 → ℤ)) ∧
    Nonempty (apm_t97A03_Homology Y 2 ≅ ModuleCat.of ℤ (Fin 2 → ℤ)) ∧
    (∀ n, 3 ≤ n → Limits.IsZero (apm_t97A03_Homology Y n)) ∧
    Nonempty (FundamentalGroup Y y ≃* FreeGroup (Fin 3)) := by
  have hmodel := apm_t97A03_classify_connected_double_cover A B hAB Y p hp hdegree
  exact ⟨hmodel, apm_t97A03_invariants_of_model Y y hmodel⟩

#print axioms apm_t97a03
