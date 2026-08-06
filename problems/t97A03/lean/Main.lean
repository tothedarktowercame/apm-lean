import Mathlib

/-!
# APM t97A03

## Statement repairs

None.

## Encoding questions

The circle, two-sphere, marked points, covering map, sheet cardinality,
fundamental group, and claimed invariants are retained explicitly. Mathlib
does not package the adjunction space formed by the two point-identifications,
the two pictured cover constructions, or general integral singular homology;
those genuine spaces and the homology functor are therefore isolated as
opaque typed constructions.
-/

open Set

abbrev apm_t97A03_R3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t97A03_S2 := Metric.sphere (0 : apm_t97A03_R3) 1

noncomputable def apm_t97A03_north : apm_t97A03_S2 :=
  ⟨EuclideanSpace.single (2 : Fin 3) 1, by simp⟩

noncomputable def apm_t97A03_south : apm_t97A03_S2 :=
  ⟨EuclideanSpace.single (2 : Fin 3) (-1), by simp⟩

/-- `S¹ ⊔ S²` with `A` glued to the north pole and `B` to the south pole. -/
opaque apm_t97A03_BaseSpace (A B : Circle) : Type

opaque apm_t97A03_baseTopology (A B : Circle) :
    TopologicalSpace (apm_t97A03_BaseSpace A B)

noncomputable instance (A B : Circle) :
    TopologicalSpace (apm_t97A03_BaseSpace A B) :=
  apm_t97A03_baseTopology A B

/-- The picture with one lifted circle threading through the two sphere sheets. -/
opaque apm_t97A03_OneCircleCover : Type

opaque apm_t97A03_oneCircleTopology :
    TopologicalSpace apm_t97A03_OneCircleCover

noncomputable instance : TopologicalSpace apm_t97A03_OneCircleCover :=
  apm_t97A03_oneCircleTopology

/-- The picture with two lifted circles joining the two sphere sheets. -/
opaque apm_t97A03_TwoCircleCover : Type

opaque apm_t97A03_twoCircleTopology :
    TopologicalSpace apm_t97A03_TwoCircleCover

noncomputable instance : TopologicalSpace apm_t97A03_TwoCircleCover :=
  apm_t97A03_twoCircleTopology

/-- Integral singular homology in degree `n`. -/
opaque apm_t97A03_Homology
    (X : Type*) [TopologicalSpace X] (n : ℕ) : Type

axiom apm_t97A03_homologyAddCommGroupExists
    (X : Type*) [TopologicalSpace X] (n : ℕ) :
    Nonempty (AddCommGroup (apm_t97A03_Homology X n))

noncomputable instance
    (X : Type*) [TopologicalSpace X] (n : ℕ) :
    AddCommGroup (apm_t97A03_Homology X n) :=
  Classical.choice (apm_t97A03_homologyAddCommGroupExists X n)

theorem apm_t97a03
    (A B : Circle) (hAB : A ≠ B)
    (Y : Type*) [TopologicalSpace Y] [ConnectedSpace Y]
    (y : Y) (p : Y → apm_t97A03_BaseSpace A B)
    (hp : IsCoveringMap p)
    (hdegree : ∀ x : apm_t97A03_BaseSpace A B,
      Nat.card (p ⁻¹' ({x} : Set _)) = 2) :
    (Nonempty (Y ≃ₜ apm_t97A03_OneCircleCover) ∨
      Nonempty (Y ≃ₜ apm_t97A03_TwoCircleCover)) ∧
    Nonempty (apm_t97A03_Homology Y 0 ≃+ ℤ) ∧
    Nonempty (apm_t97A03_Homology Y 1 ≃+ (Fin 3 → ℤ)) ∧
    Nonempty (apm_t97A03_Homology Y 2 ≃+ (Fin 2 → ℤ)) ∧
    (∀ n, 3 ≤ n → Nonempty (apm_t97A03_Homology Y n ≃+ ZMod 1)) ∧
    Nonempty (FundamentalGroup Y y ≃* FreeGroup (Fin 3)) := by
  sorry
