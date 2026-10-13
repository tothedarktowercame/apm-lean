import Mathlib
import ConstructionTargets.SurfaceClassification

/-! # APM t99J03 — blueprint after the genus-zero repair -/

open Set
open scoped Manifold

noncomputable section

abbrev apm_t99J03_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t99J03_Disk := Metric.closedBall (0 : ℂ) 1

def apm_t99J03_edgePoint (edgeCount edge : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    apm_t99J03_Disk :=
  ⟨Complex.exp
      (Complex.I * (2 * Real.pi * ((edge : ℝ) + t.1) / edgeCount)), by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
    simp⟩

def apm_t99J03_SurfaceRel (orientable : Bool) (genus : ℕ)
    (x y : apm_t99J03_Disk) : Prop :=
  if orientable then
    if genus = 0 then
      ∃ t : Set.Icc (0 : ℝ) 1,
        let tr : Set.Icc (0 : ℝ) 1 :=
          ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩
        x = apm_t99J03_edgePoint 2 0 t ∧
          y = apm_t99J03_edgePoint 2 1 tr
    else
      ∃ j : ℕ, j < genus ∧ ∃ t : Set.Icc (0 : ℝ) 1,
        let tr : Set.Icc (0 : ℝ) 1 :=
          ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩
        (x = apm_t99J03_edgePoint (4 * genus) (4 * j) t ∧
            y = apm_t99J03_edgePoint (4 * genus) (4 * j + 2) tr) ∨
          (x = apm_t99J03_edgePoint (4 * genus) (4 * j + 1) t ∧
            y = apm_t99J03_edgePoint (4 * genus) (4 * j + 3) tr)
  else
    ∃ j : ℕ, j < genus ∧ ∃ t : Set.Icc (0 : ℝ) 1,
      x = apm_t99J03_edgePoint (2 * genus) (2 * j) t ∧
      y = apm_t99J03_edgePoint (2 * genus) (2 * j + 1) t

def apm_t99J03_Surface (orientable : Bool) (genus : ℕ) :=
  Quotient (Relation.EqvGen.setoid (apm_t99J03_SurfaceRel orientable genus))

noncomputable instance (orientable : Bool) (genus : ℕ) :
    TopologicalSpace (apm_t99J03_Surface orientable genus) :=
  TopologicalSpace.coinduced
    (fun x : apm_t99J03_Disk ↦ Quotient.mk _ x) inferInstance

def apm_t99J03_eulerCharacteristic (orientable : Bool) (genus : ℕ) : ℤ :=
  if orientable then 2 - 2 * genus else 2 - genus

@[simp] lemma apm_t99J03_eulerCharacteristic_orientable (genus : ℕ) :
    apm_t99J03_eulerCharacteristic true genus = 2 - 2 * genus := rfl

@[simp] lemma apm_t99J03_eulerCharacteristic_nonorientable (genus : ℕ) :
    apm_t99J03_eulerCharacteristic false genus = 2 - genus := rfl

/-- The repaired genus-zero relation really glues the two boundary edges; in
particular it is no longer the empty relation that produced a disk. -/
lemma apm_t99J03_sphere_word_related (t : Set.Icc (0 : ℝ) 1) :
    let tr : Set.Icc (0 : ℝ) 1 :=
      ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩
    apm_t99J03_SurfaceRel true 0
      (apm_t99J03_edgePoint 2 0 t) (apm_t99J03_edgePoint 2 1 tr) := by
  dsimp [apm_t99J03_SurfaceRel]
  exact ⟨t, rfl, rfl⟩

/-- **LIBRARY.** Classification of compact connected smooth surfaces into the
repaired literal polygon models, including uniqueness of the parameter. -/
theorem t99J03_compact_surface_classification
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace apm_t99J03_E2 X]
    [IsManifold (𝓘(ℝ, apm_t99J03_E2)) ⊤ X] :
    (∃! g : ℕ, Nonempty (X ≃ₜ apm_t99J03_Surface true g)) ∨
      (∃! k : ℕ, 0 < k ∧ Nonempty (X ≃ₜ apm_t99J03_Surface false k)) := by
  sorry

theorem apm_t99j03 :
    ∀ (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
      [ConnectedSpace X] [ChartedSpace apm_t99J03_E2 X]
      [IsManifold (𝓘(ℝ, apm_t99J03_E2)) ⊤ X],
      (∃! g : ℕ,
        Nonempty (X ≃ₜ apm_t99J03_Surface true g) ∧
        apm_t99J03_eulerCharacteristic true g = 2 - 2 * g) ∨
      (∃! k : ℕ,
        0 < k ∧ Nonempty (X ≃ₜ apm_t99J03_Surface false k) ∧
        apm_t99J03_eulerCharacteristic false k = 2 - k) := by
  intro X _ _ _ _ _ _
  simpa using t99J03_compact_surface_classification X

#print axioms apm_t99j03
